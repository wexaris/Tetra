use std::cell::RefCell;
use std::rc::Rc;
use itertools::Itertools;
use crate::ast::*;
use crate::parse::{ItemDef, ScopeTree, TokenType};
use crate::validate::{Visitor, Result};

pub struct ExprValidate {}

impl ExprValidate {
    pub fn new() -> Self { Self {} }
}

impl Visitor for ExprValidate {
    fn visit_var_decl_pre(&mut self, decl: &mut VarDecl, ctx: Rc<RefCell<ScopeTree>>) -> Result<()> {
        if let TypeSymbol::Struct(sym) = &mut *decl.def.ty {
            let ctx = ctx.borrow();

            match ctx.find(&sym.path) {
                Some(ItemDef::Struct(def)) => {
                    sym.mangled.replace(def.mangled);
                },
                _ => {
                    let module = ctx.current_module();
                    return crate::log::error(Error::UndefinedType(sym.path.clone()))
                        .with_span(&sym.path.get_span(), &module.source)
                        .into_result();
                },
            }
        }
        Ok(())
    }

    fn visit_var_decl_post(&mut self, decl: &mut VarDecl, ctx: Rc<RefCell<ScopeTree>>) -> Result<()> {
        let ctx = ctx.borrow();

        let lhs_ty = decl.def.ty.clone();
        let rhs_ty = decl.value.return_type(&ctx);
        
        if !lhs_ty.is_valid() {
            let module = ctx.current_module();
            return crate::log::error(Error::InvalidVariableType(lhs_ty.ty.clone()))
                .with_span(&decl.span, &module.source)
                .into_result();
        }
        
        if *lhs_ty != rhs_ty {
            let module = ctx.current_module();
            return crate::log::error(Error::TypeMismatch(lhs_ty.ty.clone(), rhs_ty))
                .with_span(&decl.span, &module.source)
                .into_result();
        }
        
        Ok(())
    }

    fn visit_field_decl_post(&mut self, init: &mut FieldDecl, ctx: Rc<RefCell<ScopeTree>>) -> Result<()> {
        let ctx = ctx.borrow();

        if !init.def.ty.is_valid() {
            let module = ctx.current_module();
            return crate::log::error(Error::InvalidFieldType(init.def.ty.ty.clone()))
                .with_span(&init.span, &module.source)
                .into_result();
        }

        Ok(())
    }

    fn visit_branch_post(&mut self, stmt: &mut Branch, ctx: Rc<RefCell<ScopeTree>>) -> Result<()> {
        let ctx = ctx.borrow();
        let expr_ty = stmt.cond.return_type(&ctx);

        if TypeSymbol::Bool != expr_ty {
            let module = ctx.current_module();
            return crate::log::error(Error::TypeMismatch(TypeSymbol::Bool, expr_ty))
                .with_span(&stmt.span, &module.source)
                .into_result();
        }

        Ok(())
    }

    fn visit_for_loop_post(&mut self, _stmt: &mut ForLoop, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> {
        // TODO:
        Ok(())
    }

    fn visit_while_loop_post(&mut self, stmt: &mut WhileLoop, ctx: Rc<RefCell<ScopeTree>>) -> Result<()> {
        let ctx = ctx.borrow();
        let expr_ty = stmt.cond.return_type(&ctx);

        if TypeSymbol::Bool != expr_ty {
            let module = ctx.current_module();
            return crate::log::error(Error::TypeMismatch(TypeSymbol::Bool, expr_ty))
                .with_span(&stmt.span, &module.source)
                .into_result();
        }

        Ok(())
    }

    fn visit_loop_post(&mut self, _stmt: &mut Loop, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> {
        // TODO:
        Ok(())
    }

    fn visit_return_post(&mut self, stmt: &mut Return, ctx: Rc<RefCell<ScopeTree>>) -> Result<()> {
        let ctx = ctx.borrow();
        
        let func_ty = ctx.current_func().ret;
        let ret_ty = stmt.value.as_ref()
            .map(|val| val.return_type(&ctx))
            .unwrap_or(TypeSymbol::Void);
        
        if *func_ty != ret_ty {
            let module = ctx.current_module();
            return crate::log::error(Error::TypeMismatch(func_ty.ty, ret_ty))
                .with_span(&stmt.span, &module.source)
                .into_result();
        }
        
        Ok(())
    }

    fn visit_var_access_post(&mut self, sym: &mut SymbolRef, ctx: Rc<RefCell<ScopeTree>>) -> Result<()> {
        let ctx = ctx.borrow();

        match ctx.find(&sym.path) {
            Some(ItemDef::Var(def)) => {
                let mangled = SymbolName::new(def.id.name.clone());
                sym.mangled.replace(mangled);
                Ok(())
            },
            _ => {
                let module = ctx.current_module();
                return crate::log::error(Error::UndefinedVariable(sym.path.clone()))
                    .with_span(&sym.path.get_span(), &module.source)
                    .into_result();
            },
        }
    }

    fn visit_func_call_post(&mut self, call: &mut FuncCall, ctx: Rc<RefCell<ScopeTree>>) -> Result<()> {
        let ctx = ctx.borrow();

        if let Some(ItemDef::Func(def)) = ctx.find(&call.symbol.path) {
            // Save mangled function name
            call.symbol.mangled.replace(def.mangled);

            // Match argument types
            // NOTE: won't catch args.len() != params.len()
            for i in 0..def.params.len() {
                let param = def.params.get(i).unwrap();

                if let Some(arg) = call.args.get(i) {
                    let expected_ty = &param.def.ty;
                    let found_ty = arg.expr.return_type(&ctx);

                    if expected_ty.ty != found_ty {
                        let module = ctx.current_module();
                        return crate::log::error(Error::TypeMismatch(expected_ty.ty.clone(), found_ty))
                            .with_span(&arg.span, &module.source)
                            .into_result();
                    }
                }
            }

            // Check argument count
            if def.params.len() != call.args.len() {
                let module = ctx.current_module();
                return crate::log::error(Error::ArgumentCountMismatch(def.params.len(), call.args.len()))
                    .with_span(&call.args.span, &module.source)
                    .into_result();
            }
        }
        // TODO: remove
        else if call.symbol.path.items.first().unwrap().name == "print" {
            call.symbol.mangled.replace(SymbolName::new("print".to_string()));
        }
        else { // Undefined function
            let module = ctx.current_module();
            return crate::log::error(Error::UndefinedFunction(call.symbol.path.clone()))
                .with_span(&call.symbol.path.get_span(), &module.source)
                .into_result();
        }

        Ok(())
    }

    fn visit_struct_init_post(&mut self, init: &mut StructInit, ctx: Rc<RefCell<ScopeTree>>) -> Result<()> {
        let ctx = ctx.borrow();

        let sym = init.ty.get_symbol_mut().unwrap();
        match ctx.find(&sym.path) {
            Some(ItemDef::Struct(def)) => {
                sym.mangled.replace(def.mangled.clone());

                let mut fields = def.fields.clone();

                // Match argument types
                for arg in &init.fields {
                    let idx = fields.iter()
                        .find_position(|f| f.def.id == arg.id)
                        .map(|(idx, _)| idx);
                    
                    if let Some(idx) = idx {
                        let field = fields.swap_remove(idx);
                        let expected_ty = &field.def.ty;
                        let found_ty = arg.value.return_type(&ctx);

                        if expected_ty.ty != found_ty {
                            let module = ctx.current_module();
                            return crate::log::error(Error::TypeMismatch(expected_ty.ty.clone(), found_ty))
                                .with_span(&arg.span, &module.source)
                                .into_result();
                        }
                    }
                    else {
                        let module = ctx.current_module();
                        return crate::log::error(Error::UndefinedField(arg.id.clone()))
                            .with_span(&arg.span, &module.source)
                            .into_result();
                    }
                }

                if !fields.is_empty() {
                    let module = ctx.current_module();
                    let fields = fields.into_iter()
                        .map(|f| f.def.id)
                        .collect::<Vec<_>>();
                    return crate::log::error(Error::MissingFieldInit(fields))
                        .with_span(&init.span, &module.source)
                        .into_result();
                }
            }
            _ => {
                let module = ctx.current_module();
                return crate::log::error(Error::UndefinedType(sym.path.clone()))
                    .with_span(&sym.path.get_span(), &module.source)
                    .into_result();
            }
        }

        Ok(())
    }

    fn visit_unary_op_post(&mut self, op: &mut UnaryOp, ctx: Rc<RefCell<ScopeTree>>) -> Result<()> {
        let ctx = ctx.borrow();
        match &op.op {
            TokenType::Not => {
                let expr_ty = op.value.return_type(&ctx);
                if expr_ty != TypeSymbol::Bool {
                    let module = ctx.current_module();
                    return crate::log::error(Error::InvalidUnaryOperand(op.op.clone(), expr_ty))
                        .with_span(&op.span, &module.source)
                        .into_result();
                }
                Ok(())
            }
            TokenType::Plus | TokenType::Minus => {
                let expr_ty = op.value.return_type(&ctx);
                if expr_ty != TypeSymbol::Number {
                    let module = ctx.current_module();
                    return crate::log::error(Error::InvalidUnaryOperand(op.op.clone(), expr_ty))
                        .with_span(&op.span, &module.source)
                        .into_result();
                }
                Ok(())
            }
            _ => {
                let module = ctx.current_module();
                return crate::log::error(Error::InvalidOperator(op.op.clone()))
                    .with_span(&op.span, &module.source)
                    .into_result();
            }
        }
    }

    fn visit_binary_op_post(&mut self, op: &mut BinaryOp, ctx: Rc<RefCell<ScopeTree>>) -> Result<()> {
        let ctx = ctx.borrow();
        
        match &op.op {
            TokenType::Dot => {
                let lhs_ty = op.lhs.return_type(&ctx);

                let lhs_sym = match &lhs_ty {
                    TypeSymbol::Struct(sym) => sym,
                    _ => {
                        // TODO:
                        let module = ctx.current_module();
                        return crate::log::error("not a struct type!")
                            .with_span(&op.lhs.get_span(), &module.source)
                            .into_result();
                    }
                };

                let rhs_sym = match op.rhs.as_ref() {
                    Expr::VarAccess(sym) if sym.path.is_ident() => sym.path.first().unwrap(),
                    _ => {
                        // TODO:
                        let module = ctx.current_module();
                        return crate::log::error("invalid field access!")
                            .with_span(&op.rhs.get_span(), &module.source)
                            .into_result();
                    }
                };

                match ctx.find(&lhs_sym.path) {
                    Some(ItemDef::Struct(def)) => {
                        let field = def.fields.iter()
                            .find(|field| field.def.id == *rhs_sym);

                        if let Some(field) = field {
                            assert!(field.def.ty.is_valid(), "invalid type!");
                        }
                        else {
                            let module = ctx.current_module();
                            return crate::log::error(Error::UndefinedField(rhs_sym.clone()))
                                .with_span(&rhs_sym.span, &module.source)
                                .into_result();
                        }
                    }
                    _ => {
                        let module = ctx.current_module();
                        return crate::log::error("not a struct type!")
                            .with_span(&op.lhs.get_span(), &module.source)
                            .into_result();
                    }
                }

                Ok(())
            }
            TokenType::Eq | TokenType::Neq => {
                let lhs_ty = op.lhs.return_type(&ctx);
                let rhs_ty = op.rhs.return_type(&ctx);

                assert!(lhs_ty.is_valid(), "invalid type!");

                if lhs_ty != rhs_ty {
                    let module = ctx.current_module();
                    return crate::log::error(Error::IncomparableTypes(lhs_ty, rhs_ty))
                        .with_span(&op.span, &module.source)
                        .into_result();
                }

                Ok(())
            }
            TokenType::LogicAnd | TokenType::LogicOr => {
                let lhs_ty = op.lhs.return_type(&ctx);
                let rhs_ty = op.rhs.return_type(&ctx);

                assert!(lhs_ty.is_valid(), "invalid type!");

                if lhs_ty != rhs_ty {
                    let module = ctx.current_module();
                    return crate::log::error(Error::IncomparableTypes(lhs_ty, rhs_ty))
                        .with_span(&op.span, &module.source)
                        .into_result();
                }
                if !matches!(lhs_ty, TypeSymbol::Bool) {
                    let module = ctx.current_module();
                    return crate::log::error(Error::InvalidBinaryOperand(op.op.clone(), lhs_ty, rhs_ty))
                        .with_span(&op.span, &module.source)
                        .into_result();
                }
                Ok(())
            }
            TokenType::Lesser  | TokenType::LesserEq  |
            TokenType::Greater | TokenType::GreaterEq |
            TokenType::Plus | TokenType::Minus |
            TokenType::Star | TokenType::Slash | TokenType::Percent => {
                let lhs_ty = op.lhs.return_type(&ctx);
                let rhs_ty = op.rhs.return_type(&ctx);

                if lhs_ty != rhs_ty {
                    let module = ctx.current_module();
                    return crate::log::error(Error::IncomparableTypes(lhs_ty, rhs_ty))
                        .with_span(&op.span, &module.source)
                        .into_result();
                }
                if !matches!(lhs_ty, TypeSymbol::Number) {
                    let module = ctx.current_module();
                    return crate::log::error(Error::InvalidBinaryOperand(op.op.clone(), lhs_ty, rhs_ty))
                        .with_span(&op.span, &module.source)
                        .into_result();
                }
                Ok(())
            }
            TokenType::Assign |
            TokenType::AndAssign | TokenType::OrAssign |
            TokenType::AddAssign | TokenType::SubAssign |
            TokenType::MulAssign | TokenType::DivAssign | TokenType::ModAssign => {
                match op.lhs.as_ref() {
                    Expr::VarAccess(_) => {}
                    _ => {
                        let module = ctx.current_module();
                        return crate::log::error(Error::InvalidAssignmentTarget)
                            .with_span(&op.lhs.get_span(), &module.source)
                            .into_result();
                    }
                }

                let lhs_ty = op.lhs.return_type(&ctx);
                let rhs_ty = op.rhs.return_type(&ctx);

                assert!(lhs_ty.is_valid(), "invalid type!");

                if lhs_ty != rhs_ty {
                    let module = ctx.current_module();
                    return crate::log::error(Error::TypeMismatch(lhs_ty, rhs_ty))
                        .with_span(&op.span, &module.source)
                        .into_result();
                }
                if lhs_ty.is_void() && op.op != TokenType::Assign {
                    let module = ctx.current_module();
                    return crate::log::error(Error::InvalidBinaryOperand(op.op.clone(), lhs_ty, rhs_ty))
                        .with_span(&op.span, &module.source)
                        .into_result();
                }
                Ok(())
            }
            _ => {
                let module = ctx.current_module();
                return crate::log::error(Error::InvalidOperator(op.op.clone()))
                    .with_span(&op.span, &module.source)
                    .into_result();
            }
        }
    }

    fn as_any(&self) -> &dyn std::any::Any { self }
    fn as_any_mut(&mut self) -> &mut dyn std::any::Any { self }
}

#[derive(thiserror::Error, Debug)]
enum Error {
    #[error("undefined variable: {0}")]
    UndefinedVariable(Path),

    #[error("undefined function: {0}")]
    UndefinedFunction(Path),

    #[error("undefined type: {0}")]
    UndefinedType(Path),

    #[error("undefined field: {0}")]
    UndefinedField(Ident),

    #[error("missing field values: '{}'", .0.into_iter().join("', '"))]
    MissingFieldInit(Vec<Ident>),

    #[error("invalid function arguments; expected {0}, found {1}")]
    ArgumentCountMismatch(usize, usize),

    #[error("type mismatch; expected {0}, found {1}")]
    TypeMismatch(TypeSymbol, TypeSymbol),

    #[error("invalid variable type: {0}")]
    InvalidVariableType(TypeSymbol),

    #[error("invalid field type: {0}")]
    InvalidFieldType(TypeSymbol),

    #[error("invalid assignment; only variables can be assigned to!")]
    InvalidAssignmentTarget,

    #[error("invalid expression; symbol {0} cannot be used as an operator!")]
    InvalidOperator(TokenType),

    #[error("invalid expression; operator {0} cannot be applied to {1}!")]
    InvalidUnaryOperand(TokenType, TypeSymbol),

    #[error("invalid expression; operator {0} cannot be applied between {1} and {2}!")]
    InvalidBinaryOperand(TokenType, TypeSymbol, TypeSymbol),

    #[error("invalid expression; expression types {0} and {1} cannot be compared!")]
    IncomparableTypes(TypeSymbol, TypeSymbol),
}
