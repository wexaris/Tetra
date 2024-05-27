use std::cell::RefCell;
use std::rc::Rc;
use crate::ast::FuncDecl;
use crate::parse::ScopeTree;
use crate::validate::{Result, Visitor};

pub struct EntrypointFinder {}

impl EntrypointFinder {
    pub fn new() -> Self { Self {} }
}

impl Visitor for EntrypointFinder {
    fn visit_func_decl_post(&mut self, _decl: &mut FuncDecl, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> {
        todo!()
    }

    fn as_any(&self) -> &dyn std::any::Any { self }
    fn as_any_mut(&mut self) -> &mut dyn std::any::Any { self }
}
