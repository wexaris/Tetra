use crate::ast::{FieldDecl, Ident, Params, Path, SymbolName, Type};
use crate::parse::{ScopeTree, SourceFile, Span};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ModuleDef {
    pub name: String,
    pub path: Path,
    pub source: SourceFile,
}

impl ModuleDef {
    pub fn new(name: String, path: Path, source: SourceFile) -> Self {
        Self {
            source,
            path: path.join(Ident { name: name.clone(), span: Span::initial() }),
            name,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct StructDef {
    pub id: Ident,
    pub fields: Vec<FieldDecl>,
    pub mangled: SymbolName,
}

impl StructDef {
    pub fn new(id: Ident, fields: Vec<FieldDecl>, ctx: &ScopeTree) -> Self {
        let mangled = SymbolName::func(&id, ctx);
        Self { id, fields, mangled }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct FuncDef {
    pub id: Ident,
    pub ret: Type,
    pub params: Params,
    pub mangled: SymbolName,
}

impl FuncDef {
    pub fn new(id: Ident, ret: Type, params: Params, ctx: &ScopeTree) -> Self {
        let mangled = SymbolName::func(&id, ctx);
        Self { id, ret, params, mangled }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct VarDef {
    pub id: Ident,
    pub ty: Type,
}

impl VarDef {
    pub fn new(id: Ident, ty: Type) -> Self {
        Self { id, ty }
    }
}
