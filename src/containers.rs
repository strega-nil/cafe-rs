use std::ptr;
use std::sync::Mutex;

use std::ops::Index;

pub struct Scope<'a, T: 'a> {
    parent: Option<&'a Scope<'a, T>>,
    current: Vec<(String, T)>,
}

impl<'a, T> Scope<'a, T> {
    pub fn new() -> Self {
        Self {
            parent: None,
            current: Vec::new(),
        }
    }

    pub fn with_parent(parent: &'a Scope<'a, T>) -> Self {
        Self {
            parent: Some(parent),
            current: Vec::new(),
        }
    }

    pub fn get(&self, key: &str) -> Option<&T> {
        for &(ref s, ref t) in self.current.iter().rev() {
            if key == s {
                return Some(t);
            }
        }
        if let Some(parent) = self.parent {
            parent.get(key)
        } else {
            None
        }
    }

    pub fn insert(&mut self, key: String, val: T) {
        self.current.push((key, val));
    }
}

impl<'a, 'b, T> Index<&'b str> for Scope<'a, T> {
    type Output = T;

    fn index(&self, key: &'b str) -> &T {
        if let Some(ret) = self.get(key) {
            ret
        } else {
            panic!("Didn't find key: {}", key)
        }
    }
}

pub struct Arena<T> {
    arena: Mutex<(Vec<Vec<T>>, *mut Vec<T>)>,
}

impl<T> Arena<T> {
    pub fn new() -> Self {
        let mut inner = (vec![Vec::with_capacity(16)], ptr::null_mut());
        inner.1 = &mut inner.0[0];
        Arena {
            arena: Mutex::new(inner),
        }
    }

    pub fn push(&self, t: T) -> &T {
        let mut inner = self.arena.lock().unwrap();
        unsafe {
            let mut v = &mut *inner.1;
            let cap = v.capacity();
            if v.len() == cap {
                inner
                    .0
                    .push(Vec::with_capacity(if cap >= 1024 { cap } else { cap * 2 }));
                inner.1 = inner.0.last_mut().unwrap();
                v = &mut *inner.1;
            }
            v.push(t);
            &v[v.len() - 1]
        }
    }

    // calls the function on subsequent things until it hits Some, which it returns
    // hack to deal with the lack of generators
    pub fn call_on_all<F, R>(&self, mut f: F) -> Option<R>
    where
        F: FnMut(&T) -> Option<R>,
    {
        let inner = self.arena.lock().unwrap();
        for v in &inner.0 {
            for el in v {
                if let Some(v) = f(el) {
                    return Some(v);
                }
            }
        }
        None
    }
}
