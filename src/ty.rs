use std;
use std::collections::HashSet;
use std::cell::RefCell;
use typed_arena::Arena;

pub struct TypeContext<'t> {
  backing_store: Arena<TypeVariant<'t>>,
  // allows us to get the exact reference in the type Arena
  type_references: RefCell<HashSet<&'t TypeVariant<'t>>>,
}

impl<'t> TypeContext<'t> {
  pub fn new() -> Self {
    TypeContext {
      backing_store: Arena::new(),
      type_references: RefCell::new(HashSet::new()),
    }
  }

  fn get(&'t self, variant: TypeVariant<'t>) -> &'t TypeVariant<'t> {
    if let Some(var) = self.type_references.borrow().get(&variant) {
      return var;
    }

    let var = self.backing_store.alloc(variant);
    self.type_references.borrow_mut().insert(var);
    var
  }
}

#[derive(Copy, Clone)]
pub struct Type<'t>(pub &'t TypeVariant<'t>);

impl<'t> PartialEq for Type<'t> {
  fn eq(&self, rhs: &Self) -> bool {
    self.0 as *const _ == rhs.0 as *const _
  }
}

impl<'t> Eq for Type<'t> { }

impl<'t> std::hash::Hash for Type<'t> {
  fn hash<H>(&self, state: &mut H) where H: std::hash::Hasher {
    (self.0 as *const _).hash(state);
  }
}

impl<'t> std::fmt::Debug for Type<'t> {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
    match *self.0 {
      TypeVariant::SInt(size) => write!(f, "SInt({:?})", size),
      TypeVariant::UInt(size) => write!(f, "SInt({:?})", size),
      TypeVariant::Bool => write!(f, "Bool"),
      TypeVariant::Unit => write!(f, "Unit"),
      TypeVariant::Diverging => write!(f, "Diverging"),
      TypeVariant::Reference(inner) => write!(f, "Ref({:?})", inner),
      TypeVariant::Infer(i) => write!(f, "Infer({:?})", i),
      TypeVariant::InferInt(i) => write!(f, "InferInt({:?})", i),
    }
  }
}

// -- constructors --
impl<'t> Type<'t> {
  pub fn infer(ctxt: &'t TypeContext<'t>) -> Self {
    Type(ctxt.get(TypeVariant::Infer(None)))
  }

  pub fn infer_int(ctxt: &'t TypeContext<'t>) -> Self {
    Type(ctxt.get(TypeVariant::InferInt(None)))
  }

  pub fn sint(int: Int, ctxt: &'t TypeContext<'t>) -> Self {
    Type(ctxt.get(TypeVariant::SInt(int)))
  }
  pub fn uint(int: Int, ctxt: &'t TypeContext<'t>) -> Self {
    Type(ctxt.get(TypeVariant::UInt(int)))
  }
  pub fn bool(ctxt: &'t TypeContext<'t>) -> Self {
    Type(ctxt.get(TypeVariant::Bool))
  }

  pub fn ref_(ty: Type<'t>, ctxt: &'t TypeContext<'t>) -> Self {
    Type(ctxt.get(TypeVariant::Reference(ty)))
  }

  pub fn unit(ctxt: &'t TypeContext<'t>) -> Self {
    Type(ctxt.get(TypeVariant::Unit))
  }

  pub fn diverging(ctxt: &'t TypeContext<'t>) -> Self {
    Type(ctxt.get(TypeVariant::Diverging))
  }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum TypeVariant<'t> {
  SInt(Int),
  UInt(Int),
  Bool,
  Unit,

  Diverging,

  Reference(Type<'t>),
  Infer(Option<u32>),
  InferInt(Option<u32>),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Int {
  I8,
  I16,
  I32,
  I64,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Function<'t> {
  input: Vec<Type<'t>>,
  output: Type<'t>,
}

impl<'t> Function<'t> {
  pub fn new(input: Vec<Type<'t>>, output: Type<'t>) -> Self {
    Function {
      input: input,
      output: output,
    }
  }

  pub fn input(&self) -> &[Type<'t>] {
    &self.input
  }

  pub fn output(&self) -> Type<'t> {
    self.output
  }
}

impl<'t> Type<'t> {
  pub fn is_final_type(&self) -> bool {
    match *self.0 {
      TypeVariant::SInt(_)
      | TypeVariant::UInt(_)
      | TypeVariant::Bool
      | TypeVariant::Unit
      | TypeVariant::Diverging
        => true,
      TypeVariant::Reference(inner) => inner.is_final_type(),
      TypeVariant::Infer(_) | TypeVariant::InferInt(_) => false,
    }
  }

  pub fn generate_inference_id(
    &mut self, uf: &mut UnionFind<'t>, ctxt: &'t TypeContext<'t>
  ) {
    self.0 = self.get_inference_type(uf, ctxt);
  }

  fn get_inference_type(
    &self, uf: &mut UnionFind<'t>, ctxt: &'t TypeContext<'t>
  ) -> &'t TypeVariant<'t> {
    match *self.0 {
      TypeVariant::Infer(None) => {
        ctxt.get(TypeVariant::Infer(Some(uf.next_id())))
      }
      TypeVariant::InferInt(None) => {
        ctxt.get(TypeVariant::InferInt(Some(uf.next_id())))
      }
      TypeVariant::Reference(inner) => {
        ctxt.get(TypeVariant::Reference(Type(
              inner.get_inference_type(uf, ctxt)
        )))
      }
      ref t @ TypeVariant::SInt(_)
      | ref t @ TypeVariant::UInt(_)
      | ref t @ TypeVariant::Bool
      | ref t @ TypeVariant::Unit
      | ref t @ TypeVariant::Diverging
      | ref t @ TypeVariant::Infer(Some(_))
      | ref t @ TypeVariant::InferInt(Some(_))
        => t,
    }
  }

  pub fn finalize(
    &mut self, uf: &mut UnionFind<'t>, ctxt: &'t TypeContext<'t>
  ) -> Result<(), ()> {
    *self = match self.get_final_ty(uf, ctxt) {
      Some(t) => t,
      None => return Err(())
    };
    Ok(())
  }

  fn get_final_ty(
    &self, uf: &mut UnionFind<'t>, ctxt: &'t TypeContext<'t>
  ) -> Option<Type<'t>> {
    match *self.0 {
      TypeVariant::SInt(_)
      | TypeVariant::UInt(_)
      | TypeVariant::Bool
      | TypeVariant::Diverging
      | TypeVariant::Unit => {
        Some(*self)
      }
      TypeVariant::Reference(inner) => {
        match inner.get_final_ty(uf, ctxt) {
          Some(inner) => Some(Type::ref_(inner, ctxt)),
          None => None,
        }
      }
      TypeVariant::Infer(_) | TypeVariant::InferInt(_) => {
        match uf.resolve(*self) {
          Some(t) => t.get_final_ty(uf, ctxt),
          None => return None,
        }
      }
    }
  }
}

impl<'t> std::fmt::Display for Type<'t> {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
    let s = match *self.0 {
      TypeVariant::SInt(Int::I8) => "s8",
      TypeVariant::SInt(Int::I16) => "s16",
      TypeVariant::SInt(Int::I32) => "s32",
      TypeVariant::SInt(Int::I64) => "s64",
      TypeVariant::UInt(Int::I8) => "u8",
      TypeVariant::UInt(Int::I16) => "u16",
      TypeVariant::UInt(Int::I32) => "u32",
      TypeVariant::UInt(Int::I64) => "u64",
      TypeVariant::Bool => "bool",
      TypeVariant::Unit => "()",
      TypeVariant::Diverging => "!",
      TypeVariant::Reference(inner) => return write!(f, "&{}", inner),
      TypeVariant::Infer(_) | TypeVariant::InferInt(_) => "_",
    };
    write!(f, "{}", s)
  }
}

impl Int {
  #[allow(dead_code)]
  pub fn shift_mask(&self) -> u64 {
    match *self {
      Int::I8 => (1 << 3) - 1,
      Int::I16 => (1 << 4) - 1,
      Int::I32 => (1 << 5) - 1,
      Int::I64 => (1 << 6) - 1,
    }
  }

  #[allow(dead_code)]
  pub fn size(&self) -> u32 {
    match *self {
      Int::I8 => 8,
      Int::I16 => 16,
      Int::I32 => 32,
      Int::I64 => 64,
    }
  }
}

pub struct UnionFind<'t> {
  current_id: u32,
  group_parents: Vec<u32>,
  parents_ty: Vec<Option<Type<'t>>>,
}

impl<'t> UnionFind<'t> {
  pub fn new() -> Self {
    UnionFind {
      current_id: 0,
      group_parents: Vec::new(),
      parents_ty: Vec::new(),
    }
  }

  fn union(&mut self, a: u32, b: u32) {
    let b = self.find(b) as usize;
    self.group_parents[b] = self.find(a);
  }

  fn find(&self, mut n: u32) -> u32 {
    while self.group_parents[n as usize] != n {
      n = self.group_parents[n as usize];
    }
    n
  }

  pub fn unify(&mut self, a: Type<'t>, b: Type<'t>) -> Result<(), ()> {
    let a_actual = self.resolve(a);
    let b_actual = self.resolve(b);
    match (a_actual, b_actual) {
      (Some(a), Some(b)) => {
        if a.is_final_type() && b.is_final_type() && a == b {
          Ok(())
        } else {
          match (a.0, b.0) {
            (&TypeVariant::Reference(lhs), &TypeVariant::Reference(rhs)) =>
              self.unify(lhs, rhs),
            _ => Err(())
          }
        }
      }
      (None, None) => {
        match (a.0, b.0) {
          (&TypeVariant::Infer(Some(lid)), &TypeVariant::Infer(Some(rid)))
          | (&TypeVariant::Infer(Some(lid)), &TypeVariant::InferInt(Some(rid)))
          | (&TypeVariant::InferInt(Some(lid)), &TypeVariant::Infer(Some(rid)))
          | (
              &TypeVariant::InferInt(Some(lid)),
              &TypeVariant::InferInt(Some(rid)),
            )
            => {
              self.union(lid, rid);
              Ok(())
            },
          (lhs @ &TypeVariant::Infer(None), rhs)
          | (lhs @ &TypeVariant::InferInt(None), rhs)
          | (rhs, lhs @ &TypeVariant::Infer(None))
          | (lhs, rhs @ &TypeVariant::InferInt(None))
            => panic!(
              "ICE: attempted to unify {:?} with {:?}",
              lhs, rhs
            ),
          (l, r) => {
            panic!("actual ty isn't working: {:?}, {:?}", l, r)
          },
        }
      }
      (Some(ty), None) => {
        match *b.0 {
          TypeVariant::Infer(Some(id)) => {
            let id = self.find(id) as usize;
            self.parents_ty[id] = Some(ty);
            Ok(())
          },
          TypeVariant::InferInt(Some(id)) => {
            match *ty.0 {
              TypeVariant::UInt(_) | TypeVariant::SInt(_) => {
                let id = self.find(id) as usize;
                self.parents_ty[id] = Some(ty);
                Ok(())
              },
              _ => Err(()),
            }
          },
          ref t @ TypeVariant::Infer(None)
          | ref t @ TypeVariant::InferInt(None)
            => panic!("ICE: attempted to unify {:?} with {:?}", ty, t),
          ref t => panic!("ICE: resolve isn't working: {:?}", t),
        }
      }
      (None, Some(ty)) => {
        match *a.0 {
          TypeVariant::Infer(Some(id)) => {
            let id = self.find(id) as usize;
            self.parents_ty[id] = Some(ty);
            Ok(())
          },
          TypeVariant::InferInt(Some(id)) => {
            match *ty.0 {
              TypeVariant::UInt(_) | TypeVariant::SInt(_) => {
                let id = self.find(id) as usize;
                self.parents_ty[id] = Some(ty);
                Ok(())
              }
              _ => {
                Err(())
              }
            }
          },
          ref t @ TypeVariant::Infer(None)
          | ref t @ TypeVariant::InferInt(None)
            => panic!("ICE: attempted to unify {:?} with {:?}", ty, t),
          ref t => panic!("ICE: resolve isn't working: {:?}", t)
        }
      }
    }
  }

  pub fn resolve(&self, ty: Type<'t>) -> Option<Type<'t>> {
    match *ty.0 {
      TypeVariant::Infer(Some(id)) | TypeVariant::InferInt(Some(id))
        => self.parents_ty[self.find(id) as usize],
      TypeVariant::Infer(None) | TypeVariant::InferInt(None) => None,
      _ => Some(ty)
    }
  }

  fn next_id(&mut self) -> u32 {
    if self.current_id == u32::max_value() {
      panic!()
    } else {
      self.group_parents.push(self.current_id);
      self.parents_ty.push(None);
      self.current_id += 1;
      self.current_id - 1
    }
  }
}
