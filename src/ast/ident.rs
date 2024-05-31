use std::collections::hash_map::DefaultHasher;
use std::fmt::Formatter;
use std::hash::{Hash, Hasher};
use display_tree_derive::DisplayTree;
use itertools::Itertools;
use crate::parse::Span;

#[derive(DisplayTree, Debug, Clone, Hash, Eq)]
pub struct Ident {
    #[node_label]
    pub name: String,
    #[ignore_field]
    pub span: Span,
}

impl PartialEq for Ident {
    fn eq(&self, other: &Self) -> bool { self.name == other.name }
}

impl Ident {
    pub fn new_initial(name: String) -> Self {
        Self { name, span: Span::initial() }
    }

    pub fn new_unnamed(span: &Span) -> Self {
        let hash = {
            let mut hasher = DefaultHasher::new();
            span.hash(&mut hasher);
            let hash = hasher.finish();
            base_62::encode(&hash.to_ne_bytes())
        };
        Ident { name: hash, span: span.clone() }
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct Path {
    pub items: Vec<Ident>,
}

impl Path {
    #[inline]
    pub fn new(items: Vec<Ident>) -> Self {
        Self { items, }
    }

    pub fn get_span(&self) -> Span {
        assert!(!self.items.is_empty(), "Path has no elements!");
        let first = self.items.first().map(|id| id.span.start.clone());
        let last = self.items.last().map(|id| id.span.clone());
        first.map(|first| {
                let last = last.unwrap();
                Span { len: last.start.idx + last.len - first.idx, start: first }
            })
            .unwrap()
    }

    #[inline]
    pub fn join(mut self, id: Ident) -> Self {
        self.items.push(id);
        self
    }

    #[inline]
    pub fn is_ident(&self) -> bool { self.items.len() == 1 }
}

impl From<Ident> for Path {
    fn from(item: Ident) -> Self { Self { items: vec![item] } }
}
impl From<Vec<Ident>> for Path {
    fn from(items: Vec<Ident>) -> Self { Self { items } }
}

impl std::ops::Deref for Path {
    type Target = Vec<Ident>;
    fn deref(&self) -> &Self::Target { &self.items }
}
impl std::ops::DerefMut for Path {
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.items }
}

impl std::fmt::Display for Path {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let path_str = self.items.iter()
            .map(|id| id.name.as_str())
            .intersperse("::")
            .collect::<String>();
        write!(f, "{path_str}")
    }
}
