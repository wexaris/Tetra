use std::any::TypeId;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use crate::ast::*;
use crate::parse::ScopeTree;

pub type Result<T> = std::result::Result<T, crate::log::Log>;

pub struct Crawler {
    ctx: Rc<RefCell<ScopeTree>>,
    visitors: HashMap<TypeId, Box<dyn Visitor>>,
    error_count: usize,
}

impl Crawler {
    pub fn new(scope_tree: Rc<RefCell<ScopeTree>>) -> Self {
        Self {
            ctx: scope_tree,
            visitors: HashMap::new(),
            error_count: 0,
        }
    }

    pub fn with<T: Visitor + 'static>(mut self, visitor: Box<T>) -> Self {
        let replaced = self.visitors.insert(TypeId::of::<T>(), visitor);
        assert!(replaced.is_none(), "Multiple instances of the same visitor!");
        Self {
            ctx: self.ctx,
            visitors: self.visitors,
            error_count: self.error_count,
        }
    }

    pub fn visit_package(&mut self, x: &mut Package) {
        assert_eq!(self.ctx.borrow_mut().current_package(), x.def, "mismatched packages!");
        self.for_each_layer(|v, ctx| v.visit_package_pre(x, ctx));
        for (_, module) in &mut x.modules {
            self.visit_module(module);
        }
        self.for_each_layer(|v, ctx| v.visit_package_post(x, ctx));
    }
    pub fn visit_module(&mut self, x: &mut Module) {
        self.ctx.borrow_mut().push_into(&x.def.name).unwrap();
        self.for_each_layer(|v, ctx| v.visit_module_pre(x, ctx));
        for item in &mut x.items {
            self.visit_stmt(item);
        }
        self.for_each_layer(|v, ctx| v.visit_module_post(x, ctx));
        self.ctx.borrow_mut().pop();
    }

    pub fn visit_stmt(&mut self, x: &mut Stmt) {
        self.for_each_layer(|v, ctx| v.visit_stmt_pre(x, ctx));
        match x {
            Stmt::Block(block) => self.visit_block(block),
            Stmt::VarDecl(decl) => self.visit_var_decl(decl),
            Stmt::Branch(stmt) => self.visit_branch(stmt),
            Stmt::ForLoop(stmt) => self.visit_for_loop(stmt),
            Stmt::WhileLoop(stmt) => self.visit_while_loop(stmt),
            Stmt::Loop(stmt) => self.visit_loop(stmt),
            Stmt::Continue(stmt) => self.visit_continue(stmt),
            Stmt::Break(stmt) => self.visit_break(stmt),
            Stmt::Return(stmt) => self.visit_return(stmt),
            Stmt::FuncDecl(decl) => self.visit_func_decl(decl),
            Stmt::Expr(expr) => self.visit_expr(expr),
        }
        self.for_each_layer(|v, ctx| v.visit_stmt_post(x, ctx));
    }
    pub fn visit_var_decl(&mut self, x: &mut VarDecl) {
        self.for_each_layer(|v, ctx| v.visit_var_decl_pre(x, ctx));
        self.visit_expr(&mut x.value);
        self.ctx.borrow_mut().define_var(x.def.clone());
        self.for_each_layer(|v, ctx| v.visit_var_decl_post(x, ctx));
    }
    pub fn visit_branch(&mut self, x: &mut Branch) {
        self.for_each_layer(|v, ctx| v.visit_branch_pre(x, ctx));
        self.visit_expr(&mut x.cond);
        self.visit_block(&mut x.true_block);
        if let Some(false_block) = &mut x.false_block {
            self.visit_block(false_block);
        }
        self.for_each_layer(|v, ctx| v.visit_branch_post(x, ctx));
    }
    pub fn visit_for_loop(&mut self, x: &mut ForLoop) {
        self.ctx.borrow_mut().push_into(&x.id.name).unwrap();
        self.for_each_layer(|v, ctx| v.visit_for_loop_pre(x, ctx));
        self.visit_stmt(&mut x.init);
        self.visit_expr(&mut x.cond);
        self.visit_expr(&mut x.update);
        self.visit_block(&mut x.block);
        self.for_each_layer(|v, ctx| v.visit_for_loop_post(x, ctx));
        self.ctx.borrow_mut().pop();
    }
    pub fn visit_while_loop(&mut self, x: &mut WhileLoop) {
        self.ctx.borrow_mut().push_into(&x.id.name).unwrap();
        self.for_each_layer(|v, ctx| v.visit_while_loop_pre(x, ctx));
        self.visit_expr(&mut x.cond);
        self.visit_block(&mut x.block);
        self.for_each_layer(|v, ctx| v.visit_while_loop_post(x, ctx));
        self.ctx.borrow_mut().pop();
    }
    pub fn visit_loop(&mut self, x: &mut Loop) {
        self.ctx.borrow_mut().push_into(&x.id.name).unwrap();
        self.for_each_layer(|v, ctx| v.visit_loop_pre(x, ctx));
        self.visit_block(&mut x.block);
        self.for_each_layer(|v, ctx| v.visit_loop_post(x, ctx));
        self.ctx.borrow_mut().pop();
    }
    pub fn visit_continue(&mut self, x: &mut Continue) {
        self.for_each_layer(|v, ctx| v.visit_continue_pre(x, ctx));
        self.for_each_layer(|v, ctx| v.visit_continue_post(x, ctx));
    }
    pub fn visit_break(&mut self, x: &mut Break) {
        self.for_each_layer(|v, ctx| v.visit_break_pre(x, ctx));
        self.for_each_layer(|v, ctx| v.visit_break_post(x, ctx));
    }
    pub fn visit_return(&mut self, x: &mut Return) {
        self.for_each_layer(|v, ctx| v.visit_return_pre(x, ctx));
        if let Some(val) = &mut x.value {
            self.visit_expr(val);
        }
        self.for_each_layer(|v, ctx| v.visit_return_post(x, ctx));
    }
    pub fn visit_func_decl(&mut self, x: &mut FuncDecl) {
        self.ctx.borrow_mut().push_into(&x.def.id.name).unwrap();
        self.for_each_layer(|v, ctx| v.visit_func_decl_pre(x, ctx));
        for param in x.def.params.iter() {
            self.ctx.borrow_mut().define_var(param.def.clone());
        }
        self.visit_block(&mut x.block);
        self.for_each_layer(|v, ctx| v.visit_func_decl_post(x, ctx));
        self.ctx.borrow_mut().pop();
    }

    pub fn visit_expr(&mut self, x: &mut Expr) {
        self.for_each_layer(|v, ctx| v.visit_expr_pre(x, ctx));
        match x {
            Expr::VarAccess(sym) => self.visit_var_access(sym),
            Expr::UnaryOp(op) => self.visit_unary_op(op),
            Expr::BinaryOp(op) => self.visit_binary_op(op),
            Expr::FuncCall(call) => self.visit_func_call(call),
            Expr::Number(val, _) => self.visit_lit_number(*val),
            Expr::Bool(val, _) => self.visit_lit_bool(*val),
        }
        self.for_each_layer(|v, ctx| v.visit_expr_post(x, ctx));
    }
    pub fn visit_var_access(&mut self, x: &mut SymbolRef) {
        self.for_each_layer(|v, ctx| v.visit_var_access_pre(x, ctx));
        self.for_each_layer(|v, ctx| v.visit_var_access_post(x, ctx));
    }
    pub fn visit_unary_op(&mut self, x: &mut UnaryOp) {
        self.for_each_layer(|v, ctx| v.visit_unary_op_pre(x, ctx));
        self.visit_expr(&mut x.val);
        self.for_each_layer(|v, ctx| v.visit_unary_op_post(x, ctx));
    }
    pub fn visit_binary_op(&mut self, x: &mut BinaryOp) {
        self.for_each_layer(|v, ctx| v.visit_binary_op_pre(x, ctx));
        self.visit_expr(&mut x.lhs);
        self.visit_expr(&mut x.rhs);
        self.for_each_layer(|v, ctx| v.visit_binary_op_post(x, ctx));
    }
    pub fn visit_func_call(&mut self, x: &mut FuncCall) {
        self.for_each_layer(|v, ctx| v.visit_func_call_pre(x, ctx));
        for arg in &mut x.args.items {
            self.visit_expr(&mut arg.expr);
        }
        self.for_each_layer(|v, ctx| v.visit_func_call_post(x, ctx));
    }
    pub fn visit_lit_number(&mut self, x: f64) {
        self.for_each_layer(|v, ctx| v.visit_lit_number_pre(x, ctx));
        self.for_each_layer(|v, ctx| v.visit_lit_number_post(x, ctx));
    }
    pub fn visit_lit_bool(&mut self, x: bool) {
        self.for_each_layer(|v, ctx| v.visit_lit_bool_pre(x, ctx));
        self.for_each_layer(|v, ctx| v.visit_lit_bool_post(x, ctx));
    }

    pub fn visit_block(&mut self, x: &mut Block) {
        self.ctx.borrow_mut().push_into(&x.id.name).unwrap();
        self.for_each_layer(|v, ctx| v.visit_block_pre(x, ctx));
        for item in &mut x.items {
            self.visit_stmt(item);
        }
        self.for_each_layer(|v, ctx| v.visit_block_post(x, ctx));
        self.ctx.borrow_mut().pop();
    }

    fn for_each_layer<F: FnMut(&mut dyn Visitor, Rc<RefCell<ScopeTree>>) -> Result<()>>(&mut self, mut f: F) {
        for (_, v) in &mut self.visitors {
            let res = f(v.as_mut(), self.ctx.clone());
            if let Err(e) = res {
                self.error_count += 1;
                e.print();
            }
        }
    }

    pub fn get_visitor<T: Visitor + 'static>(&self) -> Option<&T> {
        self.visitors.get(&TypeId::of::<T>())
            .map_or(None, |v| v.as_any().downcast_ref::<T>())
    }
    pub fn get_visitor_mut<T: Visitor + 'static>(&mut self) -> Option<&mut T> {
        self.visitors.get_mut(&TypeId::of::<T>())
            .map_or(None, |v| v.as_any_mut().downcast_mut::<T>())
    }

    #[inline]
    pub fn has_errors(&self) -> bool { self.error_count() != 0 }

    #[inline]
    pub fn error_count(&self) -> usize { self.error_count }
}

pub trait Visitor {
    fn visit_package_pre(&mut self, _package: &mut Package, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_package_post(&mut self, _package: &mut Package, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_module_pre(&mut self, _module: &mut Module, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_module_post(&mut self, _module: &mut Module, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_stmt_pre(&mut self, _stmt: &mut Stmt, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_stmt_post(&mut self, _stmt: &mut Stmt, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_var_decl_pre(&mut self, _decl: &mut VarDecl, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_var_decl_post(&mut self, _decl: &mut VarDecl, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_branch_pre(&mut self, _stmt: &mut Branch, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_branch_post(&mut self, _stmt: &mut Branch, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_for_loop_pre(&mut self, _stmt: &mut ForLoop, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_for_loop_post(&mut self, _stmt: &mut ForLoop, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_while_loop_pre(&mut self, _stmt: &mut WhileLoop, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_while_loop_post(&mut self, _stmt: &mut WhileLoop, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_loop_pre(&mut self, _stmt: &mut Loop, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_loop_post(&mut self, _stmt: &mut Loop, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_continue_pre(&mut self, _stmt: &mut Continue, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_continue_post(&mut self, _stmt: &mut Continue, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_break_pre(&mut self, _stmt: &mut Break, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_break_post(&mut self, _stmt: &mut Break, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_return_pre(&mut self, _stmt: &mut Return, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_return_post(&mut self, _stmt: &mut Return, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_func_decl_pre(&mut self, _decl: &mut FuncDecl, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_func_decl_post(&mut self, _decl: &mut FuncDecl, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }

    fn visit_expr_pre(&mut self, _expr: &mut Expr, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_expr_post(&mut self, _expr: &mut Expr, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_var_access_pre(&mut self, _sym: &mut SymbolRef, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_var_access_post(&mut self, _sym: &mut SymbolRef, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_unary_op_pre(&mut self, _op: &mut UnaryOp, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_unary_op_post(&mut self, _op: &mut UnaryOp, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_binary_op_pre(&mut self, _op: &mut BinaryOp, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_binary_op_post(&mut self, _op: &mut BinaryOp, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_func_call_pre(&mut self, _call: &mut FuncCall, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_func_call_post(&mut self, _call: &mut FuncCall, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_lit_number_pre(&mut self, _val: f64, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_lit_number_post(&mut self, _val: f64, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_lit_bool_pre(&mut self, _val: bool, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_lit_bool_post(&mut self, _val: bool, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }

    fn visit_block_pre(&mut self, _block: &mut Block, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }
    fn visit_block_post(&mut self, _block: &mut Block, _ctx: Rc<RefCell<ScopeTree>>) -> Result<()> { Ok(()) }

    fn as_any(&self) -> &dyn std::any::Any;
    fn as_any_mut(&mut self) -> &mut dyn std::any::Any;
}
