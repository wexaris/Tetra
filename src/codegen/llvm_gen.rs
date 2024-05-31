use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::{AddressSpace, FloatPredicate, IntPredicate};
use inkwell::module::Module;
use inkwell::support::LLVMString;
use inkwell::types::{AnyTypeEnum, BasicMetadataTypeEnum, BasicType, BasicTypeEnum, PointerType, StructType};
use inkwell::values::{BasicMetadataValueEnum, BasicValue, BasicValueEnum, FloatValue, FunctionValue, IntValue, PointerValue};
use itertools::Itertools;
use crate::ast::*;
use crate::codegen::gen::Generator;
use crate::codegen::stacked_map::StackedMap;
use crate::log::{Log, LogHandler};
use crate::parse::{ItemDef, Scope, ScopeTree, TokenType};

pub struct LLVMGenerator<'ctx> {
    ctx: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    types: HashMap<SymbolName, (StructDef, StructType<'ctx>)>,
    variables: StackedMap<ItemData<'ctx>>,
    error_count: RefCell<usize>,
}

impl LogHandler for LLVMGenerator<'_> {
    fn on_emit(&self, log: &mut Log) -> bool {
        if log.is_error() {
            *self.error_count.borrow_mut() += 1
        }
        true
    }
}

impl<'ctx> Generator<'ctx> for LLVMGenerator<'ctx> {
    fn compile_module<'m>(ctx: &'ctx Context, node: &'m crate::ast::Module, defs: Rc<RefCell<ScopeTree>>) -> Self {
        let builder = ctx.create_builder();
        let module = ctx.create_module(&node.def.name);
        let mut gen = Self {
            ctx,
            module,
            builder,
            types: HashMap::new(),
            variables: StackedMap::new(),
            error_count: RefCell::new(0),
        };

        gen.precompile_static_defs(&node, defs);

        for item in &node.items {
            gen.compile_stmt(&item);
        }

        if let Err(e) = gen.module.verify() {
            crate::log::error(Error::InvalidModule(node.def.name.clone(), e))
                .handled(&mut gen)
                .print();
        }

        gen
    }
}

impl<'ctx> LLVMGenerator<'ctx> {
    fn precompile_static_defs(&mut self, node: &crate::ast::Module, defs: Rc<RefCell<ScopeTree>>) {
        let root = defs.borrow().get_root();
        let module = root.borrow()
            .find_local_scope(&node.def.name)
            .expect("current module missing from scope tree!");
        self.precompile_static_defs_recursive(&module);

        {
            let main_type = self.ctx.void_type().fn_type(&[], false);
            let main_fn = self.module.add_function("main", main_type, None);
            let main_bb = self.ctx.append_basic_block(main_fn, "entry");

            let builder = self.ctx.create_builder();
            builder.position_at_end(main_bb);

            let name = node.items.iter()
                .find_map(|item| match item.as_ref() {
                    Stmt::FuncDecl(decl) if decl.def.id.name == "main" => Some(decl.def.mangled.clone()),
                    _ => None,
                }).expect("missing main function!");

            let main = self.module.get_function(name.as_str()).unwrap();
            let _ = builder.build_call(main, &[], &format!("call.{}", name.as_str())).unwrap();

            builder.build_return(None).unwrap();
        }

        {
            let i8_ptr_type = self.ctx.i8_type().ptr_type(AddressSpace::default());
            let i32_type = self.ctx.i32_type();
            let f64_type = self.ctx.f64_type();

            let printf_type = i32_type.fn_type(&[i8_ptr_type.into()], true);
            let printf_fn = self.module.add_function("printf", printf_type, None);

            let print_type = self.ctx.void_type().fn_type(&[f64_type.into()], false);
            let print_fn = self.module.add_function("print", print_type, None);
            let print_bb = self.ctx.append_basic_block(print_fn, "entry");

            let builder = self.ctx.create_builder();
            builder.position_at_end(print_bb);

            let fmt = builder.build_global_string_ptr("%f\n", "fmt").unwrap();
            let arg = print_fn.get_first_param().unwrap();
            builder.build_call(printf_fn, &[fmt.as_pointer_value().into(), arg.into()], "call.printf").unwrap();

            builder.build_return(None).unwrap();
        }
    }

    fn precompile_static_defs_recursive(&mut self, scope: &Rc<RefCell<Scope>>) {
        let scope = scope.borrow();
        for (_, def) in scope.iter() {
            match def {
                ItemDef::Package => unreachable!("packages cannot be defined within one another!"),
                ItemDef::Module(_) => unreachable!("modules cannot be defined within one another!"),
                ItemDef::Struct(def) => {
                    self.compile_struct_def(def);
                }
                ItemDef::Func(def) => {
                    self.compile_func_prototype(def);
                    let scope = scope.find_local_scope(&def.id.name).unwrap();
                    self.precompile_static_defs_recursive(&scope);
                }
                ItemDef::Var(_) => {
                    // TODO: Save static variables to map
                }
                ItemDef::Block(id) => {
                    let scope = scope.find_local_scope(&id.name).unwrap();
                    self.precompile_static_defs_recursive(&scope);
                }
            }
        }
    }

    fn compile_stmt(&mut self, node: &Stmt) {
        match node {
            Stmt::Block(stmt) => self.compile_block(stmt),
            Stmt::VarDecl(stmt) => self.compile_var_decl(stmt),
            Stmt::FuncDecl(stmt) => { self.compile_func_decl(stmt); },
            Stmt::StructDecl(_) => { /* Handled by precompile */ },
            Stmt::Branch(stmt) => self.compile_branch(stmt),
            Stmt::ForLoop(_) => {}
            Stmt::WhileLoop(stmt) => self.compile_while_loop(stmt),
            Stmt::Loop(stmt) => self.compile_loop(stmt),
            Stmt::Continue(_) => {}
            Stmt::Break(_) => {}
            Stmt::Return(stmt) => self.compile_return(stmt),
            Stmt::Expr(expr) => { self.compile_expr(&expr); },
        }
    }

    #[inline]
    fn compile_block(&mut self, node: &Block) {
        self.variables.push();
        for item in &node.items {
            self.compile_stmt(&item);
        }
        self.variables.pop();
    }

    fn compile_var_decl(&mut self, node: &VarDecl) {
        let alloc = match node.value.as_ref() {
            Expr::StructInit(expr) => {
                let alloc = self.compile_struct_init(&expr);
                alloc.set_name(&node.def.id.name);
                alloc
            },
            expr => {
                let val = self.compile_expr(&expr).expect("unexpected void expr!");

                let func = self.get_parent_func().unwrap();
                let alloc = self.build_entry_block_alloca(func, &node.def.ty, &node.def.id.name);

                self.builder.build_store(alloc, val).unwrap();
                alloc
            }
        };

        let data = ItemData { ty: node.def.ty.clone(), ptr: alloc };
        self.variables.insert(node.def.id.name.clone(), data);
    }

    fn compile_func_prototype(&mut self, def: &FuncDef) -> FunctionValue<'ctx> {
        // Get argument types
        let args_meta = def.params.items.iter()
            .map(|arg| arg.def.ty.llvm_type_basic(self.ctx).into())
            .collect::<Vec<BasicMetadataTypeEnum>>();

        // Get function return type
        let fn_ty = if def.ret.is_void() {
            self.ctx.void_type().fn_type(args_meta.as_slice(), false)
        } else {
            def.ret.llvm_type_basic(self.ctx).fn_type(args_meta.as_slice(), false)
        };

        // Register function with module
        let fn_val = self.module.add_function(def.mangled.as_str(), fn_ty, None);

        // Set argument names for debugging
        for (i, arg) in fn_val.get_param_iter().enumerate() {
            let name = &def.params[i].def.id.name;
            arg.set_name(name.as_str());
        }

        fn_val
    }

    fn compile_func_decl(&mut self, node: &FuncDecl) -> Option<FunctionValue<'ctx>> {
        // Retrieve function prototype
        let func = self.get_function(&node.def.mangled)
            .expect("function prototypes should have already been compiled!");

        // Add function block
        let entry = self.ctx.append_basic_block(func, "entry");
        self.builder.position_at_end(entry);

        self.variables.push();

        // Set up param variables
        for (i, val) in func.get_param_iter().enumerate() {
            let param = &node.def.params[i].def;
            let alloc = self.build_entry_block_alloca(func, &param.ty, &param.id.name);
            self.builder.build_store(alloc, val).unwrap();

            let data = ItemData { ty: param.ty.clone(), ptr: alloc };
            self.variables.insert(param.id.name.clone(), data);
        }

        // Compile block
        self.compile_block(&node.block);

        self.variables.pop();

        // Validate function
        if !func.verify(true) {
            crate::log::error(Error::InvalidFunction(node.def.id.clone()))
                .handled(self)
                .print();
            func.print_to_stderr();
            unsafe { func.delete() }
            return None;
        }

        Some(func)
    }

    fn compile_struct_def(&mut self, node: &StructDef) -> StructType<'ctx> {
        // Get field types
        let field_types = node.fields.iter()
            .map(|field| field.def.ty.llvm_type_basic(self.ctx))
            .collect::<Vec<BasicTypeEnum>>();

        let struct_ty = self.ctx.opaque_struct_type(node.mangled.as_str());
        struct_ty.set_body(&field_types, false);

        self.types.insert(node.mangled.clone(), (node.clone(), struct_ty.clone()));

        struct_ty
    }

    fn compile_branch(&mut self, node: &Branch) {
        self.variables.push();

        let func = self.get_parent_func().unwrap();
        let true_bb = self.ctx.append_basic_block(func, "branch.true");
        let false_bb = self.ctx.append_basic_block(func, "branch.false");
        let end_bb = self.ctx.append_basic_block(func, "branch.end");

        // Build branch condition
        let cond = self.compile_expr(&node.cond).expect("unexpected void expr!");
        assert!(cond.is_int_value(), "cannot branch on non-boolean values!");
        self.builder.build_conditional_branch(cond.into_int_value(), true_bb, false_bb).unwrap();

        // Compile true block
        self.builder.position_at_end(true_bb);
        self.compile_block(&node.true_block);
        self.builder.build_unconditional_branch(end_bb).unwrap();

        // Compile false block
        self.builder.position_at_end(false_bb);
        if let Some(false_block) = &node.false_block {
            self.compile_block(&false_block);
        }
        self.builder.build_unconditional_branch(end_bb).unwrap();

        // Exit branch
        self.builder.position_at_end(end_bb);
        self.variables.pop();
    }

    fn compile_while_loop(&mut self, node: &WhileLoop) {
        self.variables.push();

        let func = self.get_parent_func().unwrap();
        let start_bb = self.ctx.append_basic_block(func, "loop.start");
        let body_bb = self.ctx.append_basic_block(func, "loop.body");
        let end_bb = self.ctx.append_basic_block(func, "loop.end");

        self.builder.build_unconditional_branch(start_bb).unwrap();
        self.builder.position_at_end(start_bb);

        let cond = self.compile_expr(&node.cond).expect("unexpected void expr!");
        assert!(cond.is_int_value(), "cannot branch on non-boolean values!");
        self.builder.build_conditional_branch(cond.into_int_value(), body_bb, end_bb).unwrap();

        self.builder.position_at_end(body_bb);
        self.compile_block(&node.block);
        self.builder.build_unconditional_branch(start_bb).unwrap();

        self.builder.position_at_end(end_bb);
        self.variables.pop();
    }

    fn compile_loop(&mut self, node: &Loop) {
        self.variables.push();

        let func = self.get_parent_func().unwrap();
        let start_bb = self.ctx.append_basic_block(func, "loop.start");

        self.builder.build_unconditional_branch(start_bb).unwrap();
        self.builder.position_at_end(start_bb);

        self.compile_block(&node.block);
        self.builder.build_unconditional_branch(start_bb).unwrap();

        let end_bb = self.ctx.append_basic_block(func, "loop.end");

        self.builder.position_at_end(end_bb);
        self.variables.pop();
    }

    #[inline]
    fn compile_return(&mut self, node: &Return) {
        if let Some(val) = &node.value {
            let val = self.compile_expr(val).expect("unexpected void expr!");
            self.builder.build_return(Some(&val)).unwrap();
        }
        else {
            self.builder.build_return(None).unwrap();
        }
    }

    fn compile_expr(&mut self, node: &Expr) -> Option<BasicValueEnum<'ctx>> {
        match node {
            Expr::VarAccess(sym) => Some(self.compile_var_access(&sym)),
            Expr::FieldAccess(expr) => Some(self.compile_field_access(&expr)),
            Expr::FuncCall(expr) => self.compile_func_call(&expr),
            Expr::StructInit(expr) => Some(self.compile_struct_init(&expr).into()),
            Expr::Assign(expr) => Some(self.compile_assign(&expr)),
            Expr::UnaryOp(expr) => Some(self.compile_unary_op(&expr)),
            Expr::BinaryOp(expr) => self.compile_binary_op(&expr),
            Expr::Number(val, _) => Some(self.compile_literal_num(*val).into()),
            Expr::Bool(val, _) => Some(self.compile_literal_bool(*val).into()),
        }
    }

    #[inline]
    fn compile_var_access(&mut self, sym: &SymbolRef) -> BasicValueEnum<'ctx> {
        assert!(sym.mangled.is_some(), "variable '{}' not mangled!", sym.path);
        let sym = sym.mangled.as_ref().unwrap();

        let data = self.variables.find(sym.as_str())
            .cloned()
            .expect(&format!("undefined item: {}", sym.as_str()));

        let llvm_ty = data.ty.llvm_type_basic(self.ctx);
        self.builder.build_load(llvm_ty, data.ptr, sym.as_str()).unwrap()
    }

    pub fn return_type(&self, expr: &Expr) -> Option<TypeSymbol> {
        match expr {
            Expr::VarAccess(sym) => {
                let item_name = sym.mangled.as_ref().unwrap().as_str();
                match self.variables.find(item_name) {
                    Some(def) => Some(def.ty.ty.clone()),
                    _ => None,
                }
            },
            Expr::FieldAccess(op) => {
                let item_ty = self.return_type(&op.item);
                let type_name = match item_ty {
                    Some(TypeSymbol::Struct(def)) => def.mangled.unwrap(),
                    _ => return None,
                };

                match self.types.get(&type_name) {
                    Some((def, _)) => {
                        // Get accessed struct field
                        let field = def.fields.iter()
                            .find(|field| field.def.id == op.field);

                        match field {
                            Some(field) => Some(field.def.ty.ty.clone()),
                            None => None,
                        }
                    }
                    _ => None,
                }
            }
            Expr::FuncCall(_) => {
                todo!()
                //match self.functions.find(&func.symbol.path) {
                //    Some(ItemDef::Func(def)) => def.ret.ty.clone(),
                //    _ => TypeSymbol::Undefined,
                //}
            },
            Expr::StructInit(init) => {
                let ty_ref = init.ty.get_symbol().unwrap();
                let type_name = ty_ref.mangled.as_ref().unwrap();
                Some(TypeSymbol::Struct(SymbolRef {
                    path: ty_ref.path.clone(),
                    mangled: Some(type_name.clone())
                }))
            },
            Expr::Assign(op) => self.return_type(&op.target),
            Expr::UnaryOp(_) => todo!(),
            Expr::BinaryOp(_) => todo!(),
            Expr::Number(_, _) => Some(TypeSymbol::Number),
            Expr::Bool(_, _) => Some(TypeSymbol::Bool),
        }
    }

    fn compile_field_access(&mut self, node: &FieldAccess) -> BasicValueEnum<'ctx> {
        let struct_ptr = match node.item.as_ref() {
            Expr::VarAccess(sym) => {
                let name = sym.mangled.as_ref().unwrap();
                match self.variables.find(name.as_str()) {
                    Some(var) => var.ptr,
                    None => unreachable!("unknown variable access!"),
                }
            }
            _ => {
                let item = self.compile_expr(&node.item).unwrap();
                item.into_pointer_value()
            },
        };

        let struct_ty = self.return_type(&node.item).unwrap();
        assert!(matches!(struct_ty, TypeSymbol::Struct(_)), "cannot access field of type '{}'!", struct_ty);

        let (def, struct_ty) = match &struct_ty {
            TypeSymbol::Struct(def) => {
                let ty = self.types.get(def.mangled.as_ref().unwrap());
                match ty {
                    Some(ret) => ret,
                    None => unreachable!("undefined struct type!"),
                }
            }
            _ => unreachable!("cannot access field of non-struct type!"),
        };

        let (idx, field) = def.fields.iter()
            .find_position(|field| field.def.id == node.field)
            .unwrap();

        //self.builder.build_extract_value(struct_val, idx as u32, "struct.idx").unwrap()

        let addr = self.builder.build_struct_gep(struct_ty.clone(), struct_ptr, idx as u32, "idx").unwrap();

        let field_ty = field.def.ty.llvm_type_basic(self.ctx);
        self.builder.build_load(field_ty, addr, &node.field.name).unwrap()
    }

    fn compile_func_call(&mut self, node: &FuncCall) -> Option<BasicValueEnum<'ctx>> {
        let mut compiled_args = Vec::with_capacity(node.args.len());

        for arg in node.args.iter() {
            let compiled = self.compile_expr(&arg.expr).expect("unexpected void expr!");
            compiled_args.push(compiled);
        }

        let args_meta = compiled_args.iter()
            .map(|arg| (*arg).into())
            .collect::<Vec<BasicMetadataValueEnum>>();

        let name = node.symbol.mangled.as_ref().unwrap();
        let func = self.get_function(&name)
            .expect(&format!("undefined function: {}", name.as_str()));

        let tag = format!("call.{}", name.as_str());
        let call = self.builder.build_direct_call(func, args_meta.as_slice(), &tag);
        match call {
            Ok(call) => call.try_as_basic_value().left(),
            Err(e) => panic!("generated invalid function call: {}", e),
        }
    }

    fn compile_struct_init(&mut self, node: &StructInit) -> PointerValue<'ctx> {
        assert!(matches!(*node.ty, TypeSymbol::Struct(_)), "struct field count mismatch!");

        let sym = node.ty.get_symbol().unwrap();
        let name = sym.mangled.as_ref().unwrap();
        let (def, struct_ty) = self.types.get(name).cloned().unwrap();

        assert_eq!(node.fields.len(), struct_ty.count_fields() as usize, "struct field count mismatch!");

        let func = self.get_parent_func().unwrap();
        let alloc = self.build_entry_block_alloca(func, &node.ty, &format!("struct.{name}"));

        for arg in node.fields.iter() {
            let (i, _) = def.fields.iter()
                .find_position(|field| field.def.id == arg.id)
                .expect("undeclared struct field!");
            
            let val = self.compile_expr(&arg.value).expect("unexpected void expr!");

            let addr = self.builder.build_struct_gep(struct_ty, alloc, i as u32, "idx").unwrap();
            self.builder.build_store(addr, val).unwrap();
        }

        alloc
    }

    fn compile_assign(&mut self, node: &Assign) -> BasicValueEnum<'ctx> {
        assert!(matches!(node.target.as_ref(), Expr::VarAccess(_) | Expr::FieldAccess(_)), "invalid assignment target!");

        let val = self.compile_expr(&node.value).expect("unexpected void expr!");

        match node.target.as_ref() {
            Expr::VarAccess(sym) => {
                let data = {
                    let sym = sym.mangled.as_ref().unwrap();
                    self.variables.find(sym.as_str())
                        .cloned()
                        .expect(&format!("undefined item: {sym}"))
                };

                self.builder.build_store(data.ptr, val.clone()).unwrap();
            }
            Expr::FieldAccess(sym) => {
                let struct_ptr = match sym.item.as_ref() {
                    Expr::VarAccess(sym) => {
                        let name = sym.mangled.as_ref().unwrap();
                        match self.variables.find(name.as_str()) {
                            Some(var) => var.ptr,
                            None => unreachable!("unknown variable access!"),
                        }
                    }
                    _ => {
                        let item = self.compile_expr(&sym.item).unwrap();
                        item.into_pointer_value()
                    },
                };

                let struct_ty = self.return_type(&sym.item).unwrap();
                assert!(matches!(struct_ty, TypeSymbol::Struct(_)), "cannot access field of type '{}'!", struct_ty);

                let (def, struct_ty) = match &struct_ty {
                    TypeSymbol::Struct(def) => {
                        let ty = self.types.get(def.mangled.as_ref().unwrap());
                        match ty {
                            Some(ret) => ret,
                            None => unreachable!("undefined struct type!"),
                        }
                    }
                    _ => unreachable!("cannot access field of non-struct type!"),
                };

                let (idx, _) = def.fields.iter()
                    .find_position(|field| field.def.id == sym.field)
                    .unwrap();

                let addr = self.builder.build_struct_gep(struct_ty.clone(), struct_ptr, idx as u32, "idx").unwrap();

                self.builder.build_store(addr, val).unwrap();
            }
            _ => unreachable!("invalid assignment target!"),
        }

        val
    }

    fn compile_unary_op(&mut self, node: &UnaryOp) -> BasicValueEnum<'ctx> {
        let val = self.compile_expr(&node.value).expect("unexpected void expr!");
        match &node.op {
            TokenType::Not => {
                assert!(val.is_int_value(), "cannot negate non-integer values");
                self.builder.build_int_neg(val.into_int_value(), "neg")
                    .map(|ret| ret.as_basic_value_enum())
                    .unwrap()
            }
            TokenType::Plus => val,
            TokenType::Minus => {
                assert!(val.is_float_value(), "cannot negate non-float values");
                self.builder.build_float_neg(val.into_float_value(), "fneg")
                    .map(|ret| ret.as_basic_value_enum())
                    .unwrap()
            }
            op => unreachable!("invalid unary op: {}", op),
        }
    }

    fn compile_binary_op(&mut self, node: &BinaryOp) -> Option<BasicValueEnum<'ctx>> {
        let res = match &node.op {
            TokenType::Eq => {
                let lhs = self.compile_expr(&node.lhs).expect("unexpected void expr!");
                let rhs = self.compile_expr(&node.rhs).expect("unexpected void expr!");
                assert_eq!(lhs.get_type(), rhs.get_type(), "expression type mismatch!");

                if lhs.is_int_value() {
                    self.builder.build_int_compare(IntPredicate::EQ, lhs.into_int_value(), rhs.into_int_value(), "ieq")
                        .unwrap().as_basic_value_enum()
                } else if lhs.is_float_value() {
                    self.builder.build_float_compare(FloatPredicate::OEQ, lhs.into_float_value(), rhs.into_float_value(), "foeq")
                        .unwrap().as_basic_value_enum()
                }
                else { unreachable!("unsupported type!") }
            }
            TokenType::Neq => {
                let lhs = self.compile_expr(&node.lhs).expect("unexpected void expr!");
                let rhs = self.compile_expr(&node.rhs).expect("unexpected void expr!");
                assert_eq!(lhs.get_type(), rhs.get_type(), "expression type mismatch!");

                if lhs.is_int_value() {
                    self.builder.build_int_compare(IntPredicate::NE, lhs.into_int_value(), rhs.into_int_value(), "ine")
                        .unwrap().as_basic_value_enum()
                } else if lhs.is_float_value() {
                    self.builder.build_float_compare(FloatPredicate::ONE, lhs.into_float_value(), rhs.into_float_value(), "fone")
                        .unwrap().as_basic_value_enum()
                }
                else { unreachable!("unsupported type!") }
            }

            TokenType::Lesser => {
                let lhs = self.compile_expr(&node.lhs).expect("unexpected void expr!");
                let rhs = self.compile_expr(&node.rhs).expect("unexpected void expr!");
                assert_eq!(lhs.get_type(), rhs.get_type(), "expression type mismatch!");
                assert!(lhs.is_float_value(), "operator '<' can only be applied to numbers!");

                self.builder.build_float_compare(FloatPredicate::OLT, lhs.into_float_value(), rhs.into_float_value(), "folt")
                    .unwrap().as_basic_value_enum()
            }
            TokenType::LesserEq => {
                let lhs = self.compile_expr(&node.lhs).expect("unexpected void expr!");
                let rhs = self.compile_expr(&node.rhs).expect("unexpected void expr!");
                assert_eq!(lhs.get_type(), rhs.get_type(), "expression type mismatch!");
                assert!(lhs.is_float_value(), "operator '<=' can only be applied to numbers!");

                self.builder.build_float_compare(FloatPredicate::OLE, lhs.into_float_value(), rhs.into_float_value(), "fole")
                    .unwrap().as_basic_value_enum()
            }
            TokenType::Greater => {
                let lhs = self.compile_expr(&node.lhs).expect("unexpected void expr!");
                let rhs = self.compile_expr(&node.rhs).expect("unexpected void expr!");
                assert_eq!(lhs.get_type(), rhs.get_type(), "expression type mismatch!");
                assert!(lhs.is_float_value(), "operator '>' can only be applied to numbers!");

                self.builder.build_float_compare(FloatPredicate::OGT, lhs.into_float_value(), rhs.into_float_value(), "fogt")
                    .unwrap().as_basic_value_enum()
            }
            TokenType::GreaterEq => {
                let lhs = self.compile_expr(&node.lhs).expect("unexpected void expr!");
                let rhs = self.compile_expr(&node.rhs).expect("unexpected void expr!");
                assert_eq!(lhs.get_type(), rhs.get_type(), "expression type mismatch!");
                assert!(lhs.is_float_value(), "operator '>=' can only be applied to numbers!");

                self.builder.build_float_compare(FloatPredicate::OGE, lhs.into_float_value(), rhs.into_float_value(), "foge")
                    .unwrap().as_basic_value_enum()
            }

            TokenType::LogicAnd => {
                let lhs = self.compile_expr(&node.lhs).expect("unexpected void expr!");
                assert!(lhs.is_int_value(), "operator '&&' can only be applied to booleans!");

                let const_true = self.ctx.bool_type().const_all_ones();
                let res_lhs = self.builder.build_int_compare(IntPredicate::EQ, lhs.into_int_value(), const_true, "boolcmp").unwrap();

                let initial_bb = self.builder.get_insert_block().unwrap();

                let parent_func = self.get_parent_func().unwrap();
                let rhs_bb = self.ctx.append_basic_block(parent_func, "land.rhs");
                let end_bb = self.ctx.append_basic_block(parent_func, "land.end");

                self.builder.build_conditional_branch(res_lhs, rhs_bb, end_bb).unwrap();

                self.builder.position_at_end(rhs_bb);
                let rhs = self.compile_expr(&node.rhs).expect("unexpected void expr!");
                assert!(rhs.is_int_value(), "operator '&&' can only be applied to booleans!");

                let const_true = self.ctx.bool_type().const_all_ones();
                let res_rhs = self.builder.build_int_compare(IntPredicate::EQ, rhs.into_int_value(), const_true, "boolcmp").unwrap();
                self.builder.build_unconditional_branch(end_bb).unwrap();

                self.builder.position_at_end(end_bb);

                let phi = self.builder.build_phi(self.ctx.bool_type(), "land").unwrap();
                phi.add_incoming(&[(&self.ctx.bool_type().const_zero(), initial_bb), (&res_rhs, rhs_bb)]);

                phi.as_basic_value()
            }
            TokenType::LogicOr => {
                let lhs = self.compile_expr(&node.lhs).expect("unexpected void expr!");
                assert!(lhs.is_int_value(), "operator '||' can only be applied to booleans!");

                let const_true = self.ctx.bool_type().const_all_ones();
                let res_lhs = self.builder.build_int_compare(IntPredicate::EQ, lhs.into_int_value(), const_true, "boolcmp").unwrap();

                let initial_bb = self.builder.get_insert_block().unwrap();

                let parent_func = self.get_parent_func().unwrap();
                let rhs_bb = self.ctx.append_basic_block(parent_func, "lor.rhs");
                let end_bb = self.ctx.append_basic_block(parent_func, "lor.end");

                self.builder.build_conditional_branch(res_lhs, end_bb, rhs_bb).unwrap();

                self.builder.position_at_end(rhs_bb);
                let rhs = self.compile_expr(&node.rhs).expect("unexpected void expr!");
                assert!(rhs.is_int_value(), "operator '||' can only be applied to booleans!");

                let const_true = self.ctx.bool_type().const_all_ones();
                let res_rhs = self.builder.build_int_compare(IntPredicate::EQ, rhs.into_int_value(), const_true, "boolcmp").unwrap();
                self.builder.build_unconditional_branch(end_bb).unwrap();

                self.builder.position_at_end(end_bb);

                let phi = self.builder.build_phi(self.ctx.bool_type(), "lor").unwrap();
                phi.add_incoming(&[(&self.ctx.bool_type().const_all_ones(), initial_bb), (&res_rhs, rhs_bb)]);

                phi.as_basic_value()
            }

            TokenType::Plus => {
                let lhs = self.compile_expr(&node.lhs).expect("unexpected void expr!");
                let rhs = self.compile_expr(&node.rhs).expect("unexpected void expr!");
                assert_eq!(lhs.get_type(), rhs.get_type(), "expression type mismatch!");
                assert!(lhs.is_float_value(), "operator '+' can only be applied to numbers!");
                self.builder.build_float_add(lhs.into_float_value(), rhs.into_float_value(), "fsum")
                    .unwrap().as_basic_value_enum()
            }
            TokenType::Minus => {
                let lhs = self.compile_expr(&node.lhs).expect("unexpected void expr!");
                let rhs = self.compile_expr(&node.rhs).expect("unexpected void expr!");
                assert_eq!(lhs.get_type(), rhs.get_type(), "expression type mismatch!");
                assert!(lhs.is_float_value(), "operator '-' can only be applied to numbers!");
                self.builder.build_float_sub(lhs.into_float_value(), rhs.into_float_value(), "fsub")
                    .unwrap().as_basic_value_enum()
            }
            TokenType::Star => {
                let lhs = self.compile_expr(&node.lhs).expect("unexpected void expr!");
                let rhs = self.compile_expr(&node.rhs).expect("unexpected void expr!");
                assert_eq!(lhs.get_type(), rhs.get_type(), "expression type mismatch!");
                assert!(lhs.is_float_value(), "operator '*' can only be applied to numbers!");
                self.builder.build_float_mul(lhs.into_float_value(), rhs.into_float_value(), "fmul")
                    .unwrap().as_basic_value_enum()
            }
            TokenType::Slash => {
                let lhs = self.compile_expr(&node.lhs).expect("unexpected void expr!");
                let rhs = self.compile_expr(&node.rhs).expect("unexpected void expr!");
                assert_eq!(lhs.get_type(), rhs.get_type(), "expression type mismatch!");
                assert!(lhs.is_float_value(), "operator '/' can only be applied to numbers!");
                self.builder.build_float_div(lhs.into_float_value(), rhs.into_float_value(), "fdiv")
                    .unwrap().as_basic_value_enum()
            }
            TokenType::Percent => {
                let lhs = self.compile_expr(&node.lhs).expect("unexpected void expr!");
                let rhs = self.compile_expr(&node.rhs).expect("unexpected void expr!");
                assert_eq!(lhs.get_type(), rhs.get_type(), "expression type mismatch!");
                assert!(lhs.is_float_value(), "operator '%' can only be applied to numbers!");
                self.builder.build_float_rem(lhs.into_float_value(), rhs.into_float_value(), "frem")
                    .unwrap().as_basic_value_enum()
            }

            op => unreachable!("invalid binary op: {}", op),
        };
        Some(res)
    }

    #[inline]
    fn compile_literal_num(&mut self, val: f64) -> FloatValue<'ctx> {
        self.ctx.f64_type().const_float(val)
    }

    #[inline]
    fn compile_literal_bool(&mut self, val: bool) -> IntValue<'ctx> {
        self.ctx.bool_type().const_int(val as u64, false)
    }

    fn build_entry_block_alloca(&self, func: FunctionValue, ty: &Type, name: &str) -> PointerValue<'ctx> {
        let builder = self.ctx.create_builder();

        let entry = func.get_first_basic_block().unwrap();
        match entry.get_first_instruction() {
            Some(instr) => builder.position_before(&instr),
            None => builder.position_at_end(entry),
        }

        let llvm_ty = ty.llvm_type_basic(self.ctx);
        builder.build_alloca(llvm_ty, name).unwrap()
    }

    fn build_load(&self, name: &str) -> BasicValueEnum<'ctx> {
        let data = {
            self.variables.find(name)
                .cloned()
                .expect(&format!("undefined item: {name}"))
        };

        let llvm_ty = data.ty.llvm_type_basic(self.ctx);
        self.builder.build_load(llvm_ty, data.ptr, name).unwrap()
    }

    #[inline]
    fn get_function(&self, sym: &SymbolName) -> Option<FunctionValue<'ctx>> {
        self.module.get_function(sym.as_str())
    }

    #[inline]
    fn get_parent_func(&self) -> Option<FunctionValue<'ctx>> {
        self.builder.get_insert_block()
            .map_or(None, |block| block.get_parent())
    }

    #[inline]
    pub fn get_module(&self) -> &Module<'ctx> {
        &self.module
    }

    #[inline]
    pub fn has_errors(&self) -> bool { self.error_count() != 0 }

    #[inline]
    pub fn error_count(&self) -> usize { *self.error_count.borrow() }
}

trait LLVMType {
    fn llvm_type_basic<'ctx>(&self, ctx: &'ctx Context) -> BasicTypeEnum<'ctx>;
    fn llvm_type_any<'ctx>(&self, ctx: &'ctx Context) -> AnyTypeEnum<'ctx>;
}

impl LLVMType for TypeSymbol {
    fn llvm_type_basic<'ctx>(&self, ctx: &'ctx Context) -> BasicTypeEnum<'ctx> {
        match self {
            TypeSymbol::Struct(sym) => {
                let name = sym.mangled.as_ref().unwrap();
                ctx.get_struct_type(name.as_str()).unwrap().into()
            },
            TypeSymbol::Number => ctx.f64_type().into(),
            TypeSymbol::Bool => ctx.bool_type().into(),
            TypeSymbol::Void => panic!(""),
            TypeSymbol::Undefined => panic!(""),
        }
    }

    fn llvm_type_any<'ctx>(&self, ctx: &'ctx Context) -> AnyTypeEnum<'ctx> {
        match self {
            TypeSymbol::Struct(sym) => {
                let name = sym.mangled.as_ref().unwrap();
                ctx.get_struct_type(name.as_str()).unwrap().into()
            },
            TypeSymbol::Number => ctx.f64_type().into(),
            TypeSymbol::Bool => ctx.bool_type().into(),
            TypeSymbol::Void => ctx.void_type().into(),
            TypeSymbol::Undefined => panic!(""),
        }
    }
}

#[derive(Debug, Clone)]
struct ItemData<'ctx> {
    ty: Type,
    ptr: PointerValue<'ctx>,
}

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("generated invalid module: {0}; {1}")]
    InvalidModule(String, LLVMString),

    #[error("generated invalid function: {}", .0.name)]
    InvalidFunction(Ident),
}
