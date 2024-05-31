use std::fmt::Formatter;
use crate::ast::{Ident, Path};
use crate::parse::{ItemDef, ScopeTree};

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct SymbolName {
    inner: String,
}

impl SymbolName {
    #[inline]
    pub fn new(raw: String) -> Self {
        Self { inner: raw }
    }

    pub fn func(id: &Ident, ctx: &ScopeTree) -> Self {
        let path = Self::mangle_path(ctx.get_path_defs());
        let this = Self::mangle_name(&id.name);
        Self { inner: format!("_T{path}{this}") }
    }

    fn mangle_path(path: &[ItemDef]) -> String {
        path.iter()
            .map(|item| Self::mangle_path_item(item))
            .collect::<String>()
    }

    fn mangle_path_item(item: &ItemDef) -> String {
        match item {
            ItemDef::Package => "P".to_string(),
            ItemDef::Module(def) => Self::mangle_name(&def.name),
            ItemDef::Struct(def) => Self::mangle_name(&def.id.name),
            ItemDef::Func(def) => Self::mangle_name(&def.id.name),
            ItemDef::Var(_) =>
                unreachable!("paths can't contain variables!"),
            ItemDef::Block(_) =>
                String::new(),
        }
    }

    #[inline]
    fn mangle_name(name: &str) -> String {
        format!("{}{}", name.len(), name)
    }

    #[inline]
    pub fn as_str(&self) -> &str { &self.inner }
}

impl std::fmt::Display for SymbolName {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.inner)
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct SymbolRef {
    pub path: Path,
    pub mangled: Option<SymbolName>,
}

impl From<Ident> for SymbolRef {
    fn from(id: Ident) -> Self {
        Self { path: id.into(), mangled: None }
    }
}
impl From<Path> for SymbolRef {
    fn from(path: Path) -> Self {
        Self { path, mangled: None }
    }
}
