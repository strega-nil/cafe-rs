use std::ptr;
use std::sync::{self, Mutex, RwLock};

use std::borrow::Borrow;
use std::collections::HashMap;
use std::hash::Hash;

pub struct Arena<T> {
  arena: Mutex<(Vec<Vec<T>>, *mut Vec<T>)>,
}

impl<T> Arena<T> {
  pub fn new() -> Self {
    let mut inner =
      (vec![Vec::with_capacity(10)], ptr::null_mut());
    inner.1 = &mut inner.0[0];
    Arena {
      arena: Mutex::new(inner),
    }
  }

  pub fn push(&self, t: T) -> &T {
    let mut inner = self.arena.lock().unwrap();
    unsafe {
      let mut v = &mut *inner.1;
      if v.len() == v.capacity() {
        inner.0.push(Vec::with_capacity(v.capacity() * 2));
        inner.1 = inner.0.last_mut().unwrap();
        v = &mut *inner.1;
      }
      v.push(t);
      &v[v.len() - 1]
    }
  }
}

pub struct ArenaMap<T, U> {
  arena: Arena<U>,
  // should be &'self U
  map: RwLock<HashMap<T, *const U>>,
}

impl<T: Hash + Eq, U> ArenaMap<T, U> {
  pub fn new() -> Self {
    ArenaMap {
      arena: Arena::new(),
      map: RwLock::new(HashMap::new()),
    }
  }

  pub fn insert_anonymous(&self, val: U) -> &U {
    self.arena.push(val)
  }

  pub fn insert(&self, key: T, val: U) -> &U {
    let ref_ = self.arena.push(val);
    let mut inner = self.map.write().unwrap();
    if !inner.contains_key(&key) {
      inner.insert(key, ref_ as *const _);
      ref_
    } else {
      panic!("attempted to insert a key twice");
    }
  }

  pub fn get<'a, B: ?Sized>(&'a self, key: &B) -> Option<&'a U>
  where
    T: Borrow<B>,
    B: Hash + Eq,
  {
    self.map.read().unwrap().get(key).map(|&r| unsafe { &*r })
  }

  /*
  pub fn contains<B>(&self, key: &B) -> bool
  where
    T: Borrow<B>,
    B: Hash + Eq,
  {
    self.map.read().unwrap().contains_key(key)
  }
  */

  pub fn hashmap(
    &self,
  ) -> sync::RwLockReadGuard<HashMap<T, *const U>> {
    self.map.read().unwrap()
  }
}
