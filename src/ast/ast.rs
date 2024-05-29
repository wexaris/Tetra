use display_tree::DisplayTree;
use crate::ast::def::{FuncDef, ModuleDef, VarDef};
use crate::ast::{Ident, SymbolRef};
use crate::parse::{ItemDef, ScopeTree, Span, TokenType};

#[derive(Debug, Clone)]
pub struct Module {
    pub def: ModuleDef,
    pub items: Vec<Box<Stmt>>,
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Block(Block),
    VarDecl(VarDecl),
    Branch(Branch),
    ForLoop(ForLoop),
    WhileLoop(WhileLoop),
    Loop(Loop),
    Continue(Continue),
    Break(Break),
    Return(Return),
    FuncDecl(FuncDecl),
    Expr(Box<Expr>),
}

impl Stmt {
    pub fn get_span(&self) -> Span {
        match self {
            Stmt::Block(block) => block.span.clone(),
            Stmt::VarDecl(decl) => decl.span.clone(),
            Stmt::Branch(stmt) => stmt.span.clone(),
            Stmt::ForLoop(stmt) => stmt.span.clone(),
            Stmt::WhileLoop(stmt) => stmt.span.clone(),
            Stmt::Loop(stmt) => stmt.span.clone(),
            Stmt::Continue(stmt) => stmt.span.clone(),
            Stmt::Break(stmt) => stmt.span.clone(),
            Stmt::Return(ret) => ret.span.clone(),
            Stmt::FuncDecl(decl) => decl.span.clone(),
            Stmt::Expr(expr) => expr.get_span(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct VarDecl {
    pub def: VarDef,
    pub value: Box<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Branch {
    pub cond: Box<Expr>,
    pub true_block: Block,
    pub false_block: Option<Block>,
    pub span: Span,
}

#[derive(DisplayTree, Debug, Clone)]
pub struct ForLoop {
    #[ignore_field]
    pub id: Ident,
    #[tree]
    pub init: Box<Stmt>,
    #[tree]
    pub cond: Box<Expr>,
    #[tree]
    pub update: Box<Expr>,
    #[tree]
    pub block: Block,
    #[ignore_field]
    pub span: Span,
}

#[derive(DisplayTree, Debug, Clone)]
pub struct WhileLoop {
    #[ignore_field]
    pub id: Ident,
    #[tree]
    pub cond: Box<Expr>,
    #[tree]
    pub block: Block,
    #[ignore_field]
    pub span: Span,
}

#[derive(DisplayTree, Debug, Clone)]
pub struct Loop {
    #[ignore_field]
    pub id: Ident,
    #[tree]
    pub block: Block,
    #[ignore_field]
    pub span: Span,
}

#[derive(DisplayTree, Debug, Clone)]
pub struct Continue {
    #[ignore_field]
    pub span: Span,
}

#[derive(DisplayTree, Debug, Clone)]
pub struct Break {
    #[ignore_field]
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Return {
    pub value: Option<Box<Expr>>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct FuncDecl {
    pub def: FuncDef,
    pub block: Block,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum Expr {
    VarAccess(SymbolRef),
    UnaryOp(UnaryOp),
    BinaryOp(BinaryOp),
    FuncCall(FuncCall),
    Number(f64, Span),
    Bool(bool, Span),
}

impl Expr {
    pub fn return_type(&self, ctx: &ScopeTree) -> Type {
        match self {
            Expr::VarAccess(sym) => {
                match ctx.find(&sym.path) {
                    Some(ItemDef::Var(def)) => def.ty.clone(),
                    _ => Type::Undefined,
                }
            },
            Expr::UnaryOp(op) => op.return_type(),
            Expr::BinaryOp(op) => op.return_type(),
            Expr::FuncCall(func) => {
                match ctx.find(&func.symbol.path) {
                    Some(ItemDef::Func(def)) => def.ret.clone(),
                    _ => Type::Undefined,
                }
            },
            Expr::Number(_, _) => Type::Number,
            Expr::Bool(_, _) => Type::Bool,
        }
    }

    pub fn get_span(&self) -> Span {
        match self {
            Expr::VarAccess(path) => path.path.get_span(),
            Expr::UnaryOp(op) => op.span.clone(),
            Expr::BinaryOp(op) => op.span.clone(),
            Expr::FuncCall(call) => call.span.clone(),
            Expr::Number(_, span) => span.clone(),
            Expr::Bool(_, span) => span.clone(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct FuncCall {
    pub symbol: SymbolRef,
    pub args: Args,
    pub span: Span,
}

#[derive(DisplayTree, Debug, Clone)]
pub struct UnaryOp {
    #[node_label]
    pub op: TokenType,
    #[tree]
    pub val: Box<Expr>,
    #[ignore_field]
    pub span: Span,
}

impl UnaryOp {
    pub fn return_type(&self) -> Type {
        match &self.op {
            TokenType::Not => Type::Bool,
            TokenType::Plus | TokenType::Minus => Type::Number,
            _ => panic!("invalid unary operation: {}", self.op),
        }
    }
}

#[derive(DisplayTree, Debug, Clone)]
pub struct BinaryOp {
    #[node_label]
    pub op: TokenType,
    #[tree]
    pub lhs: Box<Expr>,
    #[tree]
    pub rhs: Box<Expr>,
    #[ignore_field]
    pub span: Span,
}

impl BinaryOp {
    pub fn return_type(&self) -> Type {
        if self.op.is_assign() {
            return Type::Void;
        }
        match &self.op {
            TokenType::Eq | TokenType::Neq => Type::Bool,
            TokenType::Lesser | TokenType::LesserEq => Type::Bool,
            TokenType::Greater | TokenType::GreaterEq => Type::Bool,
            TokenType::LogicAnd | TokenType::LogicOr => Type::Bool,
            TokenType::Plus | TokenType::Minus => Type::Number,
            TokenType::Star | TokenType::Slash | TokenType::Percent => Type::Number,
            _ => panic!("invalid binary operation: {}", self.op),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Block {
    pub id: Ident,
    pub items: Vec<Box<Stmt>>,
    pub span: Span,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Params {
    pub items: Vec<Param>,
    pub span: Span,
}
impl std::ops::Deref for Params {
    type Target = Vec<Param>;
    fn deref(&self) -> &Self::Target { &self.items }
}
impl std::ops::DerefMut for Params {
    fn deref_mut(&mut self) -> &mut <Self as std::ops::Deref>::Target { &mut self.items }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Param {
    pub def: VarDef,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Args {
    pub items: Vec<Arg>,
    pub span: Span,
}
impl std::ops::Deref for Args {
    type Target = Vec<Arg>;
    fn deref(&self) -> &Self::Target { &self.items }
}
impl std::ops::DerefMut for Args {
    fn deref_mut(&mut self) -> &mut <Self as std::ops::Deref>::Target { &mut self.items }
}

#[derive(Debug, Clone)]
pub struct Arg {
    pub expr: Box<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Type {
    Undefined, Void, Number, Bool,
}

impl Type {
    pub fn is_void(&self) -> bool { *self == Type::Void }
}
