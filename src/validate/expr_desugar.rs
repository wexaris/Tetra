use std::any::Any;
use std::cell::RefCell;
use std::rc::Rc;
use crate::ast::{BinaryOp, Expr};
use crate::parse::{ScopeTree, TokenType};
use crate::validate::{Result, Visitor};

pub struct ExprDesugar {}

impl ExprDesugar {
    pub fn new() -> Self {
        Self {}
    }
}

impl Visitor for ExprDesugar {
    fn visit_binary_op_pre(&mut self, op: &mut BinaryOp, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> {
        // Simplify complex assignment
        if op.op.is_assign() {
            if let Some(pre_op) = op.op.assign_pre_op() {
                let pre_op = BinaryOp {
                    op: pre_op,
                    lhs: op.lhs.clone(),
                    rhs: op.rhs.clone(),
                    span: op.span.clone(),
                };
                op.rhs = Box::new(Expr::BinaryOp(pre_op));
            }
            op.op = TokenType::Assign;
        }
        Ok(())
    }

    fn as_any(&self) -> &dyn Any { self }
    fn as_any_mut(&mut self) -> &mut dyn Any { self }
}
