use std::cell::RefCell;
use std::rc::Rc;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::{FloatPredicate, IntPredicate, OptimizationLevel};
use inkwell::module::Module;
use inkwell::support::LLVMString;
use inkwell::targets::{CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine};
use inkwell::types::{AnyType, AnyTypeEnum, BasicMetadataTypeEnum, BasicType, BasicTypeEnum};
use inkwell::values::{BasicMetadataValueEnum, BasicValue, BasicValueEnum, FloatValue, FunctionValue, IntValue, PointerValue};
use log::Level;
use crate::ast::*;
use crate::codegen::stacked_map::StackedMap;
use crate::log::{Log, LogHandler};
use crate::parse::{ItemDef, Scope, ScopeTree, TokenType};

pub struct Generator<'ctx> {
    ctx: &'ctx Context,
    module_def: ModuleDef,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    variables: RefCell<StackedMap<ItemData<'ctx>>>,
    error_count: RefCell<usize>,
}

impl<'ctx> LogHandler for Generator<'ctx> {
    fn on_emit(&self, log: &mut Log) -> bool {
        match log.level {
            Level::Error => *self.error_count.borrow_mut() += 1,
            _ => {}
        }
        true
    }
}

impl<'ctx> Generator<'ctx> {
    #[inline]
    pub fn create_context() -> Context {
        Context::create()
    }

    pub fn compile_module(node: &crate::ast::Module, ctx: &'ctx Context, defs: Rc<RefCell<ScopeTree>>) -> Self {
        let module = ctx.create_module(&node.def.name);
        let builder = ctx.create_builder();
        let mut gen = Self {
            ctx,
            module_def: node.def.clone(),
            module,
            builder,
            variables: RefCell::new(StackedMap::new()),
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

    fn precompile_static_defs(&self, node: &crate::ast::Module, defs: Rc<RefCell<ScopeTree>>) {
        let root = defs.borrow().get_root();
        let module = root.borrow()
            .find_local_scope(&node.def.name)
            .expect("current module missing from scope tree!");
        self.precompile_static_defs_recursive(&module);
    }

    fn precompile_static_defs_recursive(&self, scope: &Rc<RefCell<Scope>>) {
        let scope = scope.borrow();
        for (_, def) in scope.iter() {
            match def {
                ItemDef::Package(_) => unreachable!("packages cannot be defined within one another!"),
                ItemDef::Module(_) => unreachable!("modules cannot be defined within one another!"),
                ItemDef::Func(def) => {
                    self.compile_func_prototype(def.clone());
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

    fn compile_stmt(&self, node: &Stmt) {
        match node {
            Stmt::Block(stmt) => self.compile_block(stmt),
            Stmt::Branch(stmt) => self.compile_branch(stmt),
            Stmt::ForLoop(_) => {}
            Stmt::WhileLoop(stmt) => self.compile_while_loop(stmt),
            Stmt::Loop(stmt) => self.compile_loop(stmt),
            Stmt::Continue(_) => {}
            Stmt::Break(_) => {}
            Stmt::Return(stmt) => self.compile_return(stmt),
            Stmt::VarDecl(stmt) => self.compile_var_decl(stmt),
            Stmt::FuncDecl(stmt) => { self.compile_func_decl(stmt); },
            Stmt::Expr(expr) => { self.compile_expr(&expr); },
        }
    }

    #[inline]
    fn compile_block(&self, node: &Block) {
        self.variables.borrow_mut().push();
        for item in &node.items {
            self.compile_stmt(&item);
        }
        self.variables.borrow_mut().pop();
    }

    fn compile_branch(&self, node: &Branch) {
        self.variables.borrow_mut().push();

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
        self.variables.borrow_mut().pop();
    }

    fn compile_while_loop(&self, node: &WhileLoop) {
        self.variables.borrow_mut().push();

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
        self.variables.borrow_mut().pop();
    }

    fn compile_loop(&self, node: &Loop) {
        self.variables.borrow_mut().push();

        let func = self.get_parent_func().unwrap();
        let start_bb = self.ctx.append_basic_block(func, "loop.start");

        self.builder.build_unconditional_branch(start_bb).unwrap();
        self.builder.position_at_end(start_bb);

        self.compile_block(&node.block);
        self.builder.build_unconditional_branch(start_bb).unwrap();

        let end_bb = self.ctx.append_basic_block(func, "loop.end");

        self.builder.position_at_end(end_bb);
        self.variables.borrow_mut().pop();
    }

    #[inline]
    fn compile_return(&self, node: &Return) {
        if let Some(val) = &node.value {
            let val = self.compile_expr(val).expect("unexpected void expr!");
            self.builder.build_return(Some(&val)).unwrap();
        }
        else {
            self.builder.build_return(None).unwrap();
        }
    }

    fn compile_var_decl(&self, node: &VarDecl) {
        let val = self.compile_expr(&node.value).expect("unexpected void expr!");
        let func = self.get_parent_func().unwrap();
        let alloc = self.build_entry_block_alloca(func, node.def.ty, &node.def.id.name);
        self.builder.build_store(alloc, val).unwrap();

        let data = ItemData { ty: node.def.ty, ptr: alloc };
        self.variables.borrow_mut().insert(node.def.id.name.clone(), data);
    }

    fn compile_func_prototype(&self, def: FuncDef) -> FunctionValue {
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

    fn compile_func_decl(&self, node: &FuncDecl) -> Option<FunctionValue> {
        // Retrieve function prototype
        let func = self.get_function(&node.def.mangled)
            .expect("function prototypes should have already been compiled!");

        // Add function block
        let entry = self.ctx.append_basic_block(func, "entry");
        self.builder.position_at_end(entry);

        self.variables.borrow_mut().push();

        // Set up param variables
        for (i, val) in func.get_param_iter().enumerate() {
            let param = &node.def.params[i].def;
            let alloc = self.build_entry_block_alloca(func, param.ty, &param.id.name);
            self.builder.build_store(alloc, val).unwrap();

            let data = ItemData { ty: param.ty, ptr: alloc };
            self.variables.borrow_mut().insert(param.id.name.clone(), data);
        }

        // Compile block
        self.compile_block(&node.block);

        self.variables.borrow_mut().pop();

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

    fn compile_expr(&self, node: &Expr) -> Option<BasicValueEnum> {
        match node {
            Expr::Number(val, _) => Some(self.compile_literal_num(*val).as_basic_value_enum()),
            Expr::Bool(val, _) => Some(self.compile_literal_bool(*val).as_basic_value_enum()),
            Expr::UnaryOp(expr) => Some(self.compile_unary_op(&expr)),
            Expr::BinaryOp(expr) => self.compile_binary_op(&expr),
            Expr::VarAccess(sym) => Some(self.compile_var_access(&sym)),
            Expr::FuncCall(expr) => self.compile_func_call(&expr),
        }
    }

    #[inline]
    fn compile_var_access(&self, sym: &SymbolRef) -> BasicValueEnum {
        let sym = sym.mangled.borrow();
        let sym = sym.as_ref().unwrap();
        self.build_load(&sym.as_str())
    }

    fn compile_unary_op(&self, node: &UnaryOp) -> BasicValueEnum {
        let val = self.compile_expr(&node.val).expect("unexpected void expr!");
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

    fn compile_binary_op(&self, node: &BinaryOp) -> Option<BasicValueEnum> {
        if node.op.is_assign() {
            assert!(matches!(node.lhs.as_ref(), Expr::VarAccess(_)), "invalid assignment target!");
            assert_eq!(node.op, TokenType::Assign, "complex assignment should've been desugared!");

            if let Expr::VarAccess(sym) = node.lhs.as_ref() {
                let val = self.compile_expr(&node.rhs).expect("unexpected void expr!");

                let data = {
                    let sym = sym.mangled.borrow();
                    let sym = sym.as_ref().unwrap();

                    self.variables
                        .borrow()
                        .find(sym.as_str())
                        .cloned()
                        .expect(&format!("undefined item: {sym}"))
                };

                // TODO: handle complex assignment

                self.builder.build_store(data.ptr, val).unwrap();
                return None;
            }
            else {
                unreachable!("invalid assignment target!");
            }
        }

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

            TokenType::Assign => {
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

    fn compile_func_call(&self, node: &FuncCall) -> Option<BasicValueEnum> {
        let mut compiled_args = Vec::with_capacity(node.args.len());

        for arg in node.args.iter() {
            let compiled = self.compile_expr(&arg.expr).expect("unexpected void expr!");
            compiled_args.push(compiled);
        }

        let args_meta = compiled_args.iter()
            .map(|arg| (*arg).into())
            .collect::<Vec<BasicMetadataValueEnum>>();

        let sym = node.symbol.mangled.borrow();
        let name = sym.as_ref().unwrap();
        let func = self.get_function(&name)
            .expect(&format!("undefined function: {}", name.as_str()));

        let tag = format!("call.{}", name.as_str());
        let call = self.builder.build_direct_call(func, args_meta.as_slice(), &tag);
        match call {
            Ok(call) => call.try_as_basic_value().left(),
            Err(e) => panic!("generated invalid function call: {}", e),
        }
    }

    #[inline]
    fn compile_literal_num(&self, val: f64) -> FloatValue {
        self.ctx.f64_type().const_float(val)
    }

    #[inline]
    fn compile_literal_bool(&self, val: bool) -> IntValue {
        self.ctx.bool_type().const_int(val as u64, false)
    }

    fn build_entry_block_alloca(&self, func: FunctionValue, ty: Type, name: &str) -> PointerValue<'ctx> {
        let builder = self.ctx.create_builder();

        let entry = func.get_first_basic_block().unwrap();
        match entry.get_first_instruction() {
            Some(instr) => builder.position_before(&instr),
            None => builder.position_at_end(entry),
        }

        let llvm_ty = ty.llvm_type_basic(self.ctx);
        builder.build_alloca(llvm_ty, name).unwrap()
    }

    fn build_load(&self, name: &str) -> BasicValueEnum {
        let data = {
            let defs = self.variables.borrow();
            defs.find(name).cloned().expect(&format!("undefined item: {name}"))
        };

        let llvm_ty = data.ty.llvm_type_basic(self.ctx);

        if llvm_ty.is_int_type() {
            self.builder.build_load(llvm_ty.into_int_type(), data.ptr, name).unwrap()
        }
        else if llvm_ty.is_float_type() {
            self.builder.build_load(llvm_ty.into_float_type(), data.ptr, name).unwrap()
        }
        else {
            panic!("unsupported load instruction type!");
        }
    }

    #[inline]
    fn get_function(&self, sym: &SymbolName) -> Option<FunctionValue> {
        self.module.get_function(sym.as_str())
    }

    #[inline]
    fn get_parent_func(&self) -> Option<FunctionValue> {
        self.builder.get_insert_block()
            .map_or(None, |block| block.get_parent())
    }

    #[inline]
    pub fn get_module(&self) -> Module<'ctx> {
        self.module.clone()
    }

    pub fn write_bitcode_to_dir<P: AsRef<std::path::Path>>(&self, path: P) {
        std::fs::create_dir_all(&path).unwrap();
        let filename = self.module_def.name.clone() + ".bc";
        let filepath = path.as_ref().join(&filename);
        self.module.write_bitcode_to_path(&filepath);
    }

    pub fn write_obj_to_dir<P: AsRef<std::path::Path>>(&self, path: P) {
        std::fs::create_dir_all(&path).unwrap();
        let filename = self.module_def.name.clone() + ".o";
        let filepath = path.as_ref().join(&filename);

        let config = InitializationConfig::default();
        Target::initialize_all(&config);

        let target_triple = TargetMachine::get_default_triple();
        self.module.set_triple(&target_triple);

        let target = Target::from_triple(&target_triple).unwrap();

        let cpu = "generic";
        let features = "";
        let optimization = OptimizationLevel::Default;
        let reloc_mode = RelocMode::Default;
        let code_model = CodeModel::Default;
        let machine = target.create_target_machine(
            &target_triple, cpu, features, optimization, reloc_mode, code_model).unwrap();

        let target_data = machine.get_target_data();
        self.module.set_data_layout(&target_data.get_data_layout());

        machine.write_to_file(&self.module, FileType::Object, &filepath).unwrap();
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

impl LLVMType for Type {
    fn llvm_type_basic<'ctx>(&self, ctx: &'ctx Context) -> BasicTypeEnum<'ctx> {
        match self {
            Type::Undefined => panic!(""),
            Type::Void => panic!(""),
            Type::Number => ctx.f64_type().as_basic_type_enum(),
            Type::Bool => ctx.bool_type().as_basic_type_enum(),
        }
    }

    fn llvm_type_any<'ctx>(&self, ctx: &'ctx Context) -> AnyTypeEnum<'ctx> {
        match self {
            Type::Undefined => panic!(""),
            Type::Void => ctx.void_type().as_any_type_enum(),
            Type::Number => ctx.f64_type().as_any_type_enum(),
            Type::Bool => ctx.bool_type().as_any_type_enum(),
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
