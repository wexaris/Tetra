use display_tree::DisplayTree;
use crate::ast::def::{FuncDef, ModuleDef, VarDef};
use crate::ast::{Ident, StructDef, SymbolRef};
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
    FuncDecl(FuncDecl),
    StructDecl(StructDecl),
    Branch(Branch),
    ForLoop(ForLoop),
    WhileLoop(WhileLoop),
    Loop(Loop),
    Continue(Continue),
    Break(Break),
    Return(Return),
    Expr(Box<Expr>),
}

impl Stmt {
    pub fn get_span(&self) -> Span {
        match self {
            Stmt::Block(block) => block.span.clone(),
            Stmt::VarDecl(decl) => decl.span.clone(),
            Stmt::FuncDecl(decl) => decl.span.clone(),
            Stmt::StructDecl(decl) => decl.span.clone(),
            Stmt::Branch(stmt) => stmt.span.clone(),
            Stmt::ForLoop(stmt) => stmt.span.clone(),
            Stmt::WhileLoop(stmt) => stmt.span.clone(),
            Stmt::Loop(stmt) => stmt.span.clone(),
            Stmt::Continue(stmt) => stmt.span.clone(),
            Stmt::Break(stmt) => stmt.span.clone(),
            Stmt::Return(ret) => ret.span.clone(),
            Stmt::Expr(expr) => expr.get_span(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Block {
    pub id: Ident,
    pub items: Vec<Box<Stmt>>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct VarDecl {
    pub def: VarDef,
    pub value: Box<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct FuncDecl {
    pub def: FuncDef,
    pub block: Block,
    pub span: Span,
}

#[derive(Debug, Clone, Eq)]
pub struct Params {
    pub items: Vec<Param>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct StructDecl {
    pub def: StructDef,
    pub span: Span,
}

#[derive(Debug, Clone, Eq)]
pub struct FieldDecl {
    pub def: VarDef,
    pub is_public: bool,
    pub span: Span,
}

impl PartialEq for FieldDecl {
    fn eq(&self, other: &Self) -> bool { self.def == other.def && self.is_public == other.is_public }
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
pub enum Expr {
    VarAccess(SymbolRef),
    FieldAccess(FieldAccess),
    FuncCall(FuncCall),
    StructInit(StructInit),
    Assign(Assign),
    UnaryOp(UnaryOp),
    BinaryOp(BinaryOp),
    Number(f64, Span),
    Bool(bool, Span),
}

impl Expr {
    pub fn return_type(&self, ctx: &ScopeTree) -> TypeSymbol {
        match self {
            Expr::VarAccess(sym) => {
                match ctx.find(&sym.path) {
                    Some(ItemDef::Var(def)) => def.ty.ty.clone(),
                    _ => TypeSymbol::Undefined,
                }
            },
            Expr::FieldAccess(op) => {
                let item_ty = op.item.return_type(ctx);
                let item_path = match item_ty {
                    TypeSymbol::Struct(def) => def.path,
                    _ => return TypeSymbol::Undefined,
                };

                match ctx.find(&item_path) {
                    Some(ItemDef::Struct(def)) => {
                        // Get accessed struct field
                        let field = def.fields.iter()
                            .find(|field| field.def.id == op.field);

                        match field {
                            Some(field) => field.def.ty.ty.clone(),
                            None => TypeSymbol::Undefined,
                        }
                    }
                    _ => TypeSymbol::Undefined,
                }
            }
            Expr::FuncCall(func) => {
                match ctx.find(&func.symbol.path) {
                    Some(ItemDef::Func(def)) => def.ret.ty.clone(),
                    _ => TypeSymbol::Undefined,
                }
            },
            Expr::StructInit(init) => {
                let path = &init.ty.get_symbol().unwrap().path;
                match ctx.find(&path) {
                    Some(ItemDef::Struct(def)) => {
                        TypeSymbol::Struct(SymbolRef {
                            path: path.clone(),
                            mangled: Some(def.mangled)
                        })
                    }
                    _ => TypeSymbol::Undefined,
                }
            },
            Expr::Assign(op) => op.target.return_type(ctx),
            Expr::UnaryOp(op) => op.return_type(),
            Expr::BinaryOp(op) => op.return_type(),
            Expr::Number(_, _) => TypeSymbol::Number,
            Expr::Bool(_, _) => TypeSymbol::Bool,
        }
    }

    pub fn get_span(&self) -> Span {
        match self {
            Expr::VarAccess(sym) => sym.path.get_span(),
            Expr::FieldAccess(op) => op.span.clone(),
            Expr::Assign(op) => op.span.clone(),
            Expr::FuncCall(call) => call.span.clone(),
            Expr::StructInit(init) => init.span.clone(),
            Expr::UnaryOp(op) => op.span.clone(),
            Expr::BinaryOp(op) => op.span.clone(),
            Expr::Number(_, span) => span.clone(),
            Expr::Bool(_, span) => span.clone(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct FieldAccess {
    pub item: Box<Expr>,
    pub field: Ident,
    pub span: Span,
}

#[derive(DisplayTree, Debug, Clone)]
pub struct Assign {
    #[tree]
    pub target: Box<Expr>,
    #[tree]
    pub value: Box<Expr>,
    #[ignore_field]
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct FuncCall {
    pub symbol: SymbolRef,
    pub args: Args,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct StructInit {
    pub ty: Type,
    pub fields: Vec<FieldInit>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct FieldInit {
    pub id: Ident,
    pub value: Box<Expr>,
    pub span: Span,
}

#[derive(DisplayTree, Debug, Clone)]
pub struct UnaryOp {
    #[node_label]
    pub op: TokenType,
    #[tree]
    pub value: Box<Expr>,
    #[ignore_field]
    pub span: Span,
}

impl UnaryOp {
    pub fn return_type(&self) -> TypeSymbol {
        match &self.op {
            TokenType::Not => TypeSymbol::Bool,
            TokenType::Plus | TokenType::Minus => TypeSymbol::Number,
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
    pub fn return_type(&self) -> TypeSymbol {
        if self.op.is_assign() {
            return TypeSymbol::Void;
        }
        match &self.op {
            TokenType::Eq | TokenType::Neq => TypeSymbol::Bool,
            TokenType::Lesser | TokenType::LesserEq => TypeSymbol::Bool,
            TokenType::Greater | TokenType::GreaterEq => TypeSymbol::Bool,
            TokenType::LogicAnd | TokenType::LogicOr => TypeSymbol::Bool,
            TokenType::Plus | TokenType::Minus => TypeSymbol::Number,
            TokenType::Star | TokenType::Slash | TokenType::Percent => TypeSymbol::Number,
            _ => panic!("invalid binary operation: {}", self.op),
        }
    }
}

impl PartialEq for Params {
    fn eq(&self, other: &Self) -> bool { self.items == other.items }
}

impl std::ops::Deref for Params {
    type Target = Vec<Param>;
    fn deref(&self) -> &Self::Target { &self.items }
}

#[derive(Debug, Clone, Eq)]
pub struct Param {
    pub def: VarDef,
    pub span: Span,
}

impl PartialEq for Param {
    fn eq(&self, other: &Self) -> bool { self.def == other.def }
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

#[derive(Debug, Clone)]
pub struct Arg {
    pub expr: Box<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, Eq)]
pub struct Type {
    pub ty: TypeSymbol,
    pub span: Span,
}

#[allow(non_snake_case)]
impl Type {
    #[inline]
    pub fn Struct(sym: SymbolRef, span: Span) -> Self { Self { ty: TypeSymbol::Struct(sym), span } }
    #[inline]
    pub fn Number(span: Span) -> Self { Self { ty: TypeSymbol::Number, span } }
    #[inline]
    pub fn Bool(span: Span) -> Self { Self { ty: TypeSymbol::Bool, span } }
    #[inline]
    pub fn Void(span: Span) -> Self { Self { ty: TypeSymbol::Void, span } }

    #[inline]
    pub fn get_symbol(&self) -> Option<&SymbolRef> {
        match &self.ty {
            TypeSymbol::Struct(sym) => Some(sym),
            _ => None,
        }
    }
    #[inline]
    pub fn get_symbol_mut(&mut self) -> Option<&mut SymbolRef> {
        match &mut self.ty {
            TypeSymbol::Struct(sym) => Some(sym),
            _ => None,
        }
    }
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool { self.ty == other.ty }
}

impl std::ops::Deref for Type {
    type Target = TypeSymbol;
    fn deref(&self) -> &Self::Target { &self.ty }
}
impl std::ops::DerefMut for Type {
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.ty }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum TypeSymbol {
    Struct(SymbolRef),
    Number,
    Bool,
    Void,
    Undefined,
}

impl TypeSymbol {
    pub fn is_void(&self) -> bool { *self == Self::Void }
    pub fn is_valid(&self) -> bool { *self != Self::Undefined }
}
