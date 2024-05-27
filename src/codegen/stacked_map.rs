use std::collections::HashMap;

#[derive(Debug)]
pub struct StackedMap<V> {
    map: Vec<HashMap<String, V>>,
}

impl<V> StackedMap<V> {
    pub fn new() -> Self {
        Self { map: vec![] }
    }

    pub fn push(&mut self) {
        self.map.push(HashMap::new());
    }

    pub fn pop(&mut self) {
        self.map.pop();
    }

    pub fn insert(&mut self, k: String, v: V) -> Option<V> {
        let map = self.map.last_mut().unwrap();
        map.insert(k, v)
    }

    pub fn find(&self, k: &str) -> Option<&V> {
        for layer in self.map.iter().rev() {
            if let Some(item) = layer.get(k) {
                return Some(item);
            }
        }
        None
    }
}
