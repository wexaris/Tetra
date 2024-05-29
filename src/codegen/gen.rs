use std::cell::RefCell;
use std::rc::Rc;
use inkwell::context::Context;
use crate::ast::Module;
use crate::parse::ScopeTree;

pub trait Generator<'ctx>: Sized {
    fn compile_module<'m>(ctx: &'ctx Context, node: &'m Module, defs: Rc<RefCell<ScopeTree>>) -> Self;
}
