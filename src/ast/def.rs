use display_tree::DisplayTree;
use crate::ast::{Ident, Params, Path, SymbolName, Type};
use crate::parse::{ScopeTree, SourceFile, Span};

#[derive(DisplayTree, Debug, Clone, Eq, PartialEq)]
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

#[derive(DisplayTree, Debug, Clone, Eq, PartialEq)]
pub struct FuncDef {
    #[field_label]
    pub id: Ident,
    #[field_label]
    pub ret: Type,
    #[tree]
    pub params: Params,
    #[ignore_field]
    pub mangled: SymbolName,
}

impl FuncDef {
    pub fn new(id: Ident, ret: Type, params: Params, ctx: &ScopeTree) -> Self {
        let mangled = SymbolName::func(&id, ctx);
        Self { id, ret, params, mangled }
    }
}

#[derive(DisplayTree, Debug, Clone, Eq, PartialEq)]
pub struct VarDef {
    #[field_label]
    pub id: Ident,
    #[field_label]
    pub ty: Type,
}

impl VarDef {
    pub fn new(id: Ident, ty: Type) -> Self {
        Self { id, ty }
    }
}
