use std::cell::RefCell;
use std::rc::Rc;
use crate::ast::*;
use crate::parse::{FileSpan, ItemDef, ScopeTree, TokenType};
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
            let err_span = decl.span.with_file(&module.source);
            let err = Error::InvalidVariableType(err_span);
            return Err(Box::new(err));
        }
        
        if lhs_ty != rhs_ty {
            let module = ctx.current_module();
            let err_span = decl.value.get_span().with_file(&module.source);
            let err = Error::TypeMismatch(err_span, lhs_ty, rhs_ty);
            return Err(Box::new(err));
        }
        
        Ok(())
    }

    fn visit_branch_post(&mut self, stmt: &mut Branch, ctx: Rc<RefCell<ScopeTree>>) -> Result<()> {
        let ctx = ctx.borrow();
        let expr_ty = stmt.cond.return_type(&ctx);

        if expr_ty != Type::Bool {
            let module = ctx.current_module();
            let err_span = stmt.cond.get_span().with_file(&module.source);
            let err = Error::TypeMismatch(err_span, Type::Bool, expr_ty);
            return Err(Box::new(err));
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
            let err_span = stmt.cond.get_span().with_file(&module.source);
            let err = Error::TypeMismatch(err_span, Type::Bool, expr_ty);
            return Err(Box::new(err));
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
            let err_span = stmt.span.with_file(&module.source);
            let err = Error::TypeMismatch(err_span, func_ty, ret_ty);
            return Err(Box::new(err));
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
                let err_span = sym.path.get_span().with_file(&module.source);
                let err = Error::UndefinedVariable(err_span, sym.path.clone());
                Err(Box::new(err))
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
                    let err_span = op.span.with_file(&module.source);
                    let err = Error::InvalidOperand(err_span, op.op.clone());
                    return Err(Box::new(err));
                }
                Ok(())
            }
            TokenType::Plus | TokenType::Minus => {
                let expr_ty = op.val.return_type(&ctx);
                if expr_ty != Type::Number {
                    let module = ctx.current_module();
                    let err_span = op.span.with_file(&module.source);
                    let err = Error::InvalidOperand(err_span, op.op.clone());
                    return Err(Box::new(err));
                }
                Ok(())
            }
            _ => {
                let module = ctx.current_module();
                let err_span = op.span.with_file(&module.source);
                let err = Error::InvalidOperand(err_span, op.op.clone());
                Err(Box::new(err))
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
                    let err_span = op.span.with_file(&module.source);
                    let err = Error::IncomparableTypes(err_span);
                    return Err(Box::new(err));
                }
                if matches!(lhs_ty, Type::Void | Type::Undefined) {
                    let module = ctx.current_module();
                    let err_span = op.span.with_file(&module.source);
                    let err = Error::VoidExpression(err_span);
                    return Err(Box::new(err));
                }
                Ok(())
            }
            TokenType::LogicAnd | TokenType::LogicOr => {
                let lhs_ty = op.lhs.return_type(&ctx);
                let rhs_ty = op.rhs.return_type(&ctx);
                if lhs_ty != rhs_ty {
                    let module = ctx.current_module();
                    let err_span = op.span.with_file(&module.source);
                    let err = Error::IncomparableTypes(err_span);
                    return Err(Box::new(err));
                }
                if matches!(lhs_ty, Type::Void | Type::Undefined) {
                    let module = ctx.current_module();
                    let err_span = op.span.with_file(&module.source);
                    let err = Error::VoidExpression(err_span);
                    return Err(Box::new(err));
                }
                if !matches!(lhs_ty, Type::Bool) {
                    let module = ctx.current_module();
                    let err_span = op.span.with_file(&module.source);
                    let err = Error::InvalidOperand(err_span, op.op.clone());
                    return Err(Box::new(err));
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
                    let err_span = op.span.with_file(&module.source);
                    let err = Error::IncomparableTypes(err_span);
                    return Err(Box::new(err));
                }
                if matches!(lhs_ty, Type::Void | Type::Undefined) {
                    let module = ctx.current_module();
                    let err_span = op.span.with_file(&module.source);
                    let err = Error::VoidExpression(err_span);
                    return Err(Box::new(err));
                }
                if !matches!(lhs_ty, Type::Number) {
                    let module = ctx.current_module();
                    let err_span = op.span.with_file(&module.source);
                    let err = Error::InvalidOperand(err_span, op.op.clone());
                    return Err(Box::new(err));
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
                        let err_span = op.span.with_file(&module.source);
                        let err = Error::InvalidAssignmentTarget(err_span);
                        return Err(Box::new(err));
                    }
                }

                let lhs_ty = op.lhs.return_type(&ctx);
                let rhs_ty = op.rhs.return_type(&ctx);
                if lhs_ty != rhs_ty {
                    let module = ctx.current_module();
                    let err_span = op.span.with_file(&module.source);
                    let err = Error::TypeMismatch(err_span, lhs_ty, rhs_ty);
                    return Err(Box::new(err));
                }
                if matches!(lhs_ty, Type::Void | Type::Undefined) {
                    let module = ctx.current_module();
                    let err_span = op.span.with_file(&module.source);
                    let err = Error::VoidExpression(err_span);
                    return Err(Box::new(err));
                }
                Ok(())
            }
            _ => {
                let module = ctx.current_module();
                let err_span = op.span.with_file(&module.source);
                let err = Error::InvalidOperator(err_span, op.op.clone());
                Err(Box::new(err))
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
                        let err_span = arg.span.with_file(&module.source);
                        let err = Error::TypeMismatch(err_span, expected_ty, found_ty);
                        return Err(Box::new(err));
                    }
                }
            }

            // Check argument count
            if def.params.len() != call.args.len() {
                let module = defs.current_module();
                let err_span = call.args.span.with_file(&module.source);
                let err = Error::ArgumentCountMismatch(err_span, def.params.len(), call.args.len());
                return Err(Box::new(err));
            }
        }
        else { // Undefined function
            let module = defs.current_module();
            let err_span = call.span.with_file(&module.source);
            let err = Error::UndefinedFunction(err_span, call.symbol.path.clone());
            return Err(Box::new(err));
        }

        Ok(())
    }

    fn as_any(&self) -> &dyn std::any::Any { self }
    fn as_any_mut(&mut self) -> &mut dyn std::any::Any { self }
}

#[derive(thiserror::Error, Debug)]
enum Error {
    #[error("{0}: undefined variable: {1}")]
    UndefinedVariable(FileSpan, Path),

    #[error("{0}: undefined function: {1}")]
    UndefinedFunction(FileSpan, Path),

    #[error("{0}: invalid function arguments; expected {1}, found {2}")]
    ArgumentCountMismatch(FileSpan, usize, usize),

    #[error("{0}: type mismatch; expected {1}, found {2}")]
    TypeMismatch(FileSpan, Type, Type),

    #[error("{0}: invalid variable type!")]
    InvalidVariableType(FileSpan),

    #[error("{0}: invalid assignment; only variables can be assigned to!")]
    InvalidAssignmentTarget(FileSpan),

    #[error("{0}: invalid expression; symbol {1} cannot be used as an operator!")]
    InvalidOperator(FileSpan, TokenType),

    #[error("{0}: invalid expression; operator {1} cannot be applied here!")]
    InvalidOperand(FileSpan, TokenType),

    #[error("{0}: invalid expression; expression types cannot be compared!")]
    IncomparableTypes(FileSpan),

    #[error("{0}: invalid expression; expression does not return a value!")]
    VoidExpression(FileSpan),
}
