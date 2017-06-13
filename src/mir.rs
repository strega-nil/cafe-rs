#![allow(dead_code)]

use containers::{Arena, ArenaMap};
use parse::Spanned;
use ast::{Ast, StringlyType};


#[derive(Debug)]
pub enum IntSize {
  //I8,
  //I16,
  I32,
  //I64,
  // ISize,
  // I128,
}
#[derive(Debug)]
pub enum BuiltinType {
  SInt(IntSize),
  //UInt(IntSize),
  //Bool,
}

#[derive(Debug)]
pub enum TypeVariant {
  Builtin(BuiltinType),
}
impl TypeVariant {
  pub fn s32() -> Self {
    TypeVariant::Builtin(BuiltinType::SInt(IntSize::I32))
  }
}

#[derive(Copy, Clone, Debug)]
pub struct Type<'ctx>(&'ctx TypeVariant /* <'ctx> */);

#[derive(Debug)]
struct Function<'ctx> {
  ret_ty: Type<'ctx>,
  //blks: Vec<BlockData>,
}

#[derive(Debug)]
enum ItemVariant<'ctx> {
  Function(Function<'ctx>),
  Type(Type<'ctx>),
}
type Item<'ctx> = Spanned<ItemVariant<'ctx>>;

struct ItemIdx(usize);

pub struct MirCtxt {
  types: Arena<TypeVariant>,
}

impl MirCtxt {
  pub fn new() -> Self {
    MirCtxt {
      types: Arena::new(),
    }
  }
}

pub struct Mir<'ctx> {
  // NOTE(ubsan): when I get namespacing, I should probably
  // use paths for this?
  items: ArenaMap<String, Item<'ctx>>,
  types: &'ctx Arena<TypeVariant/* <'ctx> */>,
}

impl<'ctx> Mir<'ctx> {
  pub fn new(ctx: &'ctx MirCtxt, mut ast: Ast) -> Self {
    let mut self_: Mir<'ctx> = Mir {
      types: &ctx.types,
      items: ArenaMap::new(),
    };

    ast.build_mir(&mut self_);

    self_
  }

  pub fn print(&self) {
    for (name, item) in &*self.items.hashmap() {
      println!("{:?} :: {:?}", name, unsafe { &**item });
    }
  }

  pub fn run(&self) {
    unimplemented!()
  }
}

impl<'ctx> Mir<'ctx> {
  pub fn type_(
    &self,
    name: Option<String>,
    ty: Spanned<TypeVariant> /* <'ctx> */,
  ) -> Type<'ctx> {
    let thing = Type(self.types.push(ty.thing));
    let item = Item {
      thing: ItemVariant::Type(thing),
      start: ty.start,
      end: ty.end,
    };
    if let Some(name) = name {
      self.items.insert(name, item);
    } else {
      self.items.insert_anonymous(item);
    }
    thing
  }

  pub fn get_type(
    &self,
    stype: &StringlyType,
  ) -> Option<Type<'ctx>> {
    match *stype {
      StringlyType::UserDefinedType(ref name) => {
        if let Some(ty) = self.items.get(name) {
          if let ItemVariant::Type(ty) = ty.thing {
            return Some(ty);
          } else {
            unimplemented!()
          }
        } else {
          None
        }
      },
      _ => unimplemented!(),
    }
  }
}
