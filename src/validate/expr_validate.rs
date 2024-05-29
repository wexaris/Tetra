use std::cell::RefCell;
use std::rc::Rc;
use crate::ast::*;
use crate::parse::{ItemDef, ScopeTree, TokenType};
use crate::validate::{Visitor, Result};

pub struct ExprValidate {}

impl ExprValidate {
    pub fn new() -> Self { Self {} }
}

impl Visitor for ExprValidate {
    fn visit_var_decl_post(&mut self, decl: &mut VarDecl, ctx: Rc<RefCell<ScopeTree>>) -> Result<()> {
        let ctx = ctx.borrow();

        let lhs_ty = decl.def.ty.clone();
        let rhs_ty = decl.value.return_type(&ctx);
        
        if matches!(lhs_ty, Type::Void | Type::Undefined) {
            let module = ctx.current_module();
            return crate::log::error(Error::InvalidVariableType)
                .with_span(&decl.span, &module.source)
                .into_result();
        }
        
        if lhs_ty != rhs_ty {
            let module = ctx.current_module();
            return crate::log::error(Error::TypeMismatch(lhs_ty, rhs_ty))
                .with_span(&decl.span, &module.source)
                .into_result();
        }
        
        Ok(())
    }

    fn visit_branch_post(&mut self, stmt: &mut Branch, ctx: Rc<RefCell<ScopeTree>>) -> Result<()> {
        let ctx = ctx.borrow();
        let expr_ty = stmt.cond.return_type(&ctx);

        if expr_ty != Type::Bool {
            let module = ctx.current_module();
            return crate::log::error(Error::TypeMismatch(Type::Bool, expr_ty))
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

        if expr_ty != Type::Bool {
            let module = ctx.current_module();
            return crate::log::error(Error::TypeMismatch(Type::Bool, expr_ty))
                .with_span(&stmt.span, &module.source)
                .into_result();
        }

        Ok(())
    }

    fn visit_loop_post(&mut self, _stmt: &mut Loop, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> {
        Ok(())
    }

    fn visit_return_post(&mut self, stmt: &mut Return, ctx: Rc<RefCell<ScopeTree>>) -> Result<()> {
        let ctx = ctx.borrow();
        
        let func_ty = ctx.current_func().ret;
        let ret_ty = stmt.value.as_ref()
            .map(|val| val.return_type(&ctx))
            .unwrap_or(Type::Void);
        
        if ret_ty != func_ty {
            let module = ctx.current_module();
            return crate::log::error(Error::TypeMismatch(func_ty, ret_ty))
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
                sym.mangled.replace(Some(mangled));
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

    fn visit_unary_op_post(&mut self, op: &mut UnaryOp, ctx: Rc<RefCell<ScopeTree>>) -> Result<()> {
        let ctx = ctx.borrow();
        match &op.op {
            TokenType::Not => {
                let expr_ty = op.val.return_type(&ctx);
                if expr_ty != Type::Bool {
                    let module = ctx.current_module();
                    return crate::log::error(Error::InvalidOperand(op.op.clone()))
                        .with_span(&op.span, &module.source)
                        .into_result();
                }
                Ok(())
            }
            TokenType::Plus | TokenType::Minus => {
                let expr_ty = op.val.return_type(&ctx);
                if expr_ty != Type::Number {
                    let module = ctx.current_module();
                    return crate::log::error(Error::InvalidOperand(op.op.clone()))
                        .with_span(&op.span, &module.source)
                        .into_result();
                }
                Ok(())
            }
            _ => {
                let module = ctx.current_module();
                return crate::log::error(Error::InvalidOperand(op.op.clone()))
                    .with_span(&op.span, &module.source)
                    .into_result();
            }
        }
    }

    fn visit_binary_op_post(&mut self, op: &mut BinaryOp, ctx: Rc<RefCell<ScopeTree>>) -> Result<()> {
        let ctx = ctx.borrow();
        
        match &op.op {
            TokenType::Eq | TokenType::Neq => {
                let lhs_ty = op.lhs.return_type(&ctx);
                let rhs_ty = op.rhs.return_type(&ctx);
                if lhs_ty != rhs_ty {
                    let module = ctx.current_module();
                    return crate::log::error(Error::IncomparableTypes)
                        .with_span(&op.span, &module.source)
                        .into_result();
                }
                if matches!(lhs_ty, Type::Void | Type::Undefined) {
                    let module = ctx.current_module();
                    return crate::log::error(Error::VoidExpression)
                        .with_span(&op.span, &module.source)
                        .into_result();
                }
                Ok(())
            }
            TokenType::LogicAnd | TokenType::LogicOr => {
                let lhs_ty = op.lhs.return_type(&ctx);
                let rhs_ty = op.rhs.return_type(&ctx);
                if lhs_ty != rhs_ty {
                    let module = ctx.current_module();
                    return crate::log::error(Error::IncomparableTypes)
                        .with_span(&op.span, &module.source)
                        .into_result();
                }
                if matches!(lhs_ty, Type::Void | Type::Undefined) {
                    let module = ctx.current_module();
                    return crate::log::error(Error::VoidExpression)
                        .with_span(&op.span, &module.source)
                        .into_result();
                }
                if !matches!(lhs_ty, Type::Bool) {
                    let module = ctx.current_module();
                    return crate::log::error(Error::InvalidOperand(op.op.clone()))
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
                    return crate::log::error(Error::IncomparableTypes)
                        .with_span(&op.span, &module.source)
                        .into_result();
                }
                if matches!(lhs_ty, Type::Void | Type::Undefined) {
                    let module = ctx.current_module();
                    return crate::log::error(Error::VoidExpression)
                        .with_span(&op.span, &module.source)
                        .into_result();
                }
                if !matches!(lhs_ty, Type::Number) {
                    let module = ctx.current_module();
                    return crate::log::error(Error::InvalidOperand(op.op.clone()))
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
                            .with_span(&op.span, &module.source)
                            .into_result();
                    }
                }

                let lhs_ty = op.lhs.return_type(&ctx);
                let rhs_ty = op.rhs.return_type(&ctx);
                if lhs_ty != rhs_ty {
                    let module = ctx.current_module();
                    return crate::log::error(Error::TypeMismatch(lhs_ty, rhs_ty))
                        .with_span(&op.span, &module.source)
                        .into_result();
                }
                if matches!(lhs_ty, Type::Void | Type::Undefined) {
                    let module = ctx.current_module();
                    return crate::log::error(Error::VoidExpression)
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

    fn visit_func_call_post(&mut self, call: &mut FuncCall, ctx: Rc<RefCell<ScopeTree>>) -> Result<()> {
        let defs = ctx.borrow();

        if let Some(ItemDef::Func(def)) = defs.find(&call.symbol.path) {
            // Save mangled function name
            call.symbol.mangled.replace(Some(def.mangled.clone()));

            // Match argument types
            // NOTE: won't catch args.len() != params.len()
            for i in 0..def.params.len() {
                let param = def.params.get(i).unwrap();

                if let Some(arg) = call.args.get(i) {
                    let expected_ty = param.def.ty.clone();
                    let found_ty = arg.expr.return_type(&defs);

                    if expected_ty != found_ty {
                        let module = defs.current_module();
                        return crate::log::error(Error::TypeMismatch(expected_ty, found_ty))
                            .with_span(&arg.span, &module.source)
                            .into_result();
                    }
                }
            }

            // Check argument count
            if def.params.len() != call.args.len() {
                let module = defs.current_module();
                return crate::log::error(Error::ArgumentCountMismatch(def.params.len(), call.args.len()))
                    .with_span(&call.args.span, &module.source)
                    .into_result();
            }
        }
        else if call.symbol.path.items.first().unwrap().name == "print" {
            call.symbol.mangled.replace(Some(SymbolName::new("print".to_string())));
        }
        else { // Undefined function
            let module = defs.current_module();
            return crate::log::error(Error::UndefinedFunction(call.symbol.path.clone()))
                .with_span(&call.args.span, &module.source)
                .into_result();
        }

        Ok(())
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

    #[error("invalid function arguments; expected {0}, found {1}")]
    ArgumentCountMismatch(usize, usize),

    #[error("type mismatch; expected {0}, found {1}")]
    TypeMismatch(Type, Type),

    #[error("invalid variable type!")]
    InvalidVariableType,

    #[error("invalid assignment; only variables can be assigned to!")]
    InvalidAssignmentTarget,

    #[error("invalid expression; symbol {0} cannot be used as an operator!")]
    InvalidOperator(TokenType),

    #[error("invalid expression; operator {0} cannot be applied here!")]
    InvalidOperand(TokenType),

    #[error("invalid expression; expression types cannot be compared!")]
    IncomparableTypes,

    #[error("invalid expression; expression does not return a value!")]
    VoidExpression,
}
