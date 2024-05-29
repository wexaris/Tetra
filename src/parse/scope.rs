use std::cell::RefCell;
use std::collections::hash_map::Iter;
use std::collections::HashMap;
use std::rc::{Rc, Weak};
use crate::ast::{FuncDef, Ident, ModuleDef, Path, VarDef};
use crate::log::Log;

#[derive(Debug)]
pub struct ScopeTree {
    root: Rc<RefCell<Scope>>,
    curr: Weak<RefCell<Scope>>,
    curr_path: Vec<ItemDef>,
}

impl ScopeTree {
    pub fn new() -> Self {
        let root = Rc::new(RefCell::new(Scope::new(ItemDef::Package,  Weak::new())));
        Self {
            curr: Rc::downgrade(&root),
            root,
            curr_path: vec![ItemDef::Package],
        }
    }

    pub fn push_into(&mut self, name: &str) -> Result<(), Log> {
        assert!(self.curr.strong_count() > 0, "program scope tracker is out of bounds!");
        match self.find_local_scope(name) {
            Some(scope) => {
                let item = scope.borrow().def.clone();
                self.curr_path.push(item);
                self.curr = Rc::downgrade(&scope);
                Ok(())
            },
            _ => {
                crate::log::error(Error::InvalidScope(name.to_string())).into_result()
            },
        }
    }

    pub fn pop(&mut self) {
        assert!(self.curr.strong_count() > 0, "program scope tracker is out of bounds!");
        let curr = self.curr.upgrade().unwrap();
        curr.borrow_mut().remove_transient();
        let parent = curr.borrow().parent.clone();
        self.curr = parent;
        self.curr_path.pop();
    }

    pub fn define_module(&mut self, def: ModuleDef) -> Option<ItemDef> {
        self.define(ItemDef::Module(def))
    }

    pub fn define_func(&mut self, def: FuncDef) -> Option<ItemDef> {
        self.define(ItemDef::Func(def))
    }

    pub fn define_block(&mut self, id: Ident) -> Option<ItemDef> {
        self.define(ItemDef::Block(id))
    }

    pub fn define_var(&mut self, def: VarDef) -> Option<ItemDef> {
        self.define(ItemDef::Var(def))
    }

    fn define(&mut self, def: ItemDef) -> Option<ItemDef> {
        assert!(self.curr.strong_count() > 0, "program scope tracker is out of bounds!");
        let curr = self.curr.upgrade().unwrap();
        let ret = curr.borrow_mut().define(def, |def| self.new_scope(def));
        ret
    }

    pub fn contains(&self, path: &Path) -> bool {
        assert!(self.curr.strong_count() > 0, "program scope tracker is out of bounds!");
        let curr = self.curr.upgrade().unwrap();
        let ret = curr.borrow_mut().contains(path);
        ret
    }

    pub fn find(&self, path: &Path) -> Option<ItemDef> {
        assert!(self.curr.strong_count() > 0, "program scope tracker is out of bounds!");
        let curr = self.curr.upgrade().unwrap();
        let ret = curr.borrow_mut().find(path);
        ret
    }

    pub fn find_local_scope(&self, name: &str) -> Option<Rc<RefCell<Scope>>> {
        assert!(self.curr.strong_count() > 0, "program scope tracker is out of bounds!");
        let curr = self.curr.upgrade().unwrap();
        let ret = curr.borrow_mut().find_local_scope(name);
        ret
    }

    pub fn current_module(&self) -> ModuleDef {
        assert!(self.curr.strong_count() > 0, "program scope tracker is out of bounds!");
        let curr = self.curr.upgrade().unwrap();
        let ret = curr.borrow_mut().current_module();
        ret
    }

    pub fn current_func(&self) -> FuncDef {
        assert!(self.curr.strong_count() > 0, "program scope tracker is out of bounds!");
        let curr = self.curr.upgrade().unwrap();
        let ret = curr.borrow_mut().current_func();
        ret
    }

    #[inline]
    fn new_scope(&self, def: ItemDef) -> Rc<RefCell<Scope>> {
        Rc::new(RefCell::new(Scope::new(def, self.curr.clone())))
    }

    #[inline]
    pub fn get_root(&self) -> Rc<RefCell<Scope>> {
        self.root.clone()
    }

    pub fn get_path(&self) -> Path {
        let ids = self.curr_path.iter()
            .map(|def| def.id())
            .collect::<Vec<_>>();
        Path::from(ids)
    }

    #[inline]
    pub fn get_path_defs(&self) -> &[ItemDef] { &self.curr_path }
}

#[derive(Debug)]
pub struct Scope {
    def: ItemDef,
    defs: HashMap<String, ItemDef>,
    scopes: HashMap<String, Rc<RefCell<Scope>>>,
    parent: Weak<RefCell<Scope>>,
}

impl Scope {
    pub fn new(def: ItemDef, parent: Weak<RefCell<Scope>>) -> Self {
        Self {
            defs: HashMap::new(),
            scopes: HashMap::new(),
            parent,
            def,
        }
    }

    pub fn define<F: Fn(ItemDef) -> Rc<RefCell<Scope>>>(&mut self, def: ItemDef, f: F) -> Option<ItemDef> {
        if matches!(def, ItemDef::Var(_)) {
            let id = def.id();
            let replaced_def = self.defs.insert(id.name.clone(), def.clone());
            replaced_def
        }
        else if matches!(def, ItemDef::Block(_)) {
            let id = def.id();
            let scope = f(def.clone());
            let replaced_scope = self.scopes.insert(id.name.clone(), scope.clone());
            assert!(replaced_scope.is_none(), "scope has been overriden by {def:?}");
            None
        }
        else {
            let id = def.id();
            let scope = f(def.clone());
            let replaced_scope = self.scopes.insert(id.name.clone(), scope.clone());
            assert!(replaced_scope.is_none(), "scope has been overriden by {def:?}");
            let replaced_def = self.defs.insert(id.name.clone(), def.clone());
            replaced_def
        }
    }

    pub fn contains(&self, path: &Path) -> bool {
        if self.contains_local(&path.items) {
            return true;
        }
        if let Some(parent) = self.parent.upgrade() {
            return parent.borrow().contains(path);
        }
        false
    }

    fn contains_local(&self, path: &[Ident]) -> bool {
        assert!(path.len() > 0, "Scope path has no elements!");
        let id = path.first();
        match path.len() {
            0 => false,
            1 => self.defs.contains_key(&id.unwrap().name),
            _ => {
                if let Some(def) = self.scopes.get(&id.unwrap().name) {
                    let sub_path = &path[1..];
                    return def.borrow().contains_local(sub_path);
                }
                false
            }
        }
    }

    pub fn find(&self, path: &Path) -> Option<ItemDef> {
        if let Some(item) = self.find_local(&path.items) {
            return Some(item);
        }
        if let Some(parent) = self.parent.upgrade() {
            return parent.borrow().find(path);
        }
        None
    }

    fn find_local(&self, path: &[Ident]) -> Option<ItemDef> {
        assert!(path.len() > 0, "Scope path has no elements!");
        let id = path.first();
        match path.len() {
            0 => None,
            1 => self.defs.get(&id.unwrap().name).cloned(),
            _ => {
                if let Some(def) = self.scopes.get(&id.unwrap().name) {
                    let sub_path = &path[1..];
                    return def.borrow().find_local(sub_path);
                }
                None
            }
        }
    }

    #[inline]
    pub fn find_local_scope(&self, name: &str) -> Option<Rc<RefCell<Scope>>> {
        self.scopes.get(name).cloned()
    }

    pub fn current_module(&self) -> ModuleDef {
        match &self.def {
            ItemDef::Module(def) => def.clone(),
            _ => {
                if let Some(parent) = self.parent.upgrade() {
                    parent.borrow().current_module()
                } else {
                    panic!("current module not defined!")
                }
            }
        }
    }

    pub fn current_func(&self) -> FuncDef {
        match &self.def {
            ItemDef::Func(def) => def.clone(),
            _ => {
                if let Some(parent) = self.parent.upgrade() {
                    parent.borrow().current_func()
                } else {
                    panic!("current function not defined!")
                }
            }
        }
    }

    fn remove_transient(&mut self) {
        self.defs = self.defs.iter()
            .filter(|(_, def)| !matches!(def, ItemDef::Var(_)))
            .map(|(key, def)| (key.clone(), def.clone()))
            .collect();
    }

    #[inline]
    pub fn name(&self) -> Ident { self.def.id() }

    #[inline]
    pub fn iter(&self) -> Iter<'_, String, ItemDef> {
        self.defs.iter()
    }
}

#[derive(Debug, Clone)]
pub enum ItemDef {
    Package,
    Module(ModuleDef),
    Func(FuncDef),
    Var(VarDef),
    Block(Ident),
}

impl ItemDef {
    pub fn id(&self) -> Ident {
        match self {
            ItemDef::Package => Ident::new_initial("".to_string()),
            ItemDef::Module(def) => Ident::new_initial(def.name.clone()),
            ItemDef::Func(def) => def.id.clone(),
            ItemDef::Var(def) => def.id.clone(),
            ItemDef::Block(id) => id.clone(),
        }
    }
}

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("invalid target scope: {0}")]
    InvalidScope(String),
}
