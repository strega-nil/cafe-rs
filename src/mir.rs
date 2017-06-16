// TODO(ubsan): make sure to start dealing with Spanneds
// whee errors are fun

use ast::{Ast, StringlyType};
use containers::ArenaMap;


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

#[derive(Debug)]
struct Function<'ctx> {
  ret_ty: Type<'ctx>,
  //blks: Vec<BlockData>,
}

#[derive(Debug)]
enum ValueVariant<'ctx> {
  Function(Function<'ctx>),
}

#[derive(Copy, Clone, Debug)]
pub struct Type<'ctx>(&'ctx TypeVariant /* <'ctx> */);
#[derive(Copy, Clone, Debug)]
pub struct Value<'ctx>(&'ctx ValueVariant<'ctx>);

// NOTE(ubsan): when I get namespacing, I should probably
// use paths instead of names?

pub struct MirCtxt<'a> {
  types: ArenaMap<String, TypeVariant /*<'a>*/>,
  values: ArenaMap<String, ValueVariant<'a>>,
}

impl<'a> MirCtxt<'a> {
  pub fn new() -> Self {
    MirCtxt {
      types: ArenaMap::new(),
      values: ArenaMap::new(),
    }
  }
}

pub struct Mir<'ctx> {
  values: &'ctx ArenaMap<String, ValueVariant<'ctx>>,
  types: &'ctx ArenaMap<String, TypeVariant /*<'ctx>*/>,
}

impl<'ctx> Mir<'ctx> {
  pub fn new(ctx: &'ctx MirCtxt<'ctx>, mut ast: Ast) -> Self {
    let mut self_: Mir<'ctx> = Mir {
      values: &ctx.values,
      types: &ctx.types,
    };

    ast.build_mir(&mut self_);

    self_
  }

  pub fn print(&self) {
    for (name, ty) in &*self.types.hashmap() {
      println!("{:?} :: {:?}", name, unsafe { &**ty });
    }
    for (name, value) in &*self.values.hashmap() {
      println!("{:?} :: {:?}", name, unsafe { &**value });
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
    ty: TypeVariant, /* <'ctx> */
  ) -> Type<'ctx> {
    if let Some(name) = name {
      Type(self.types.insert(name, ty))
    } else {
      Type(self.types.insert_anonymous(ty))
    }
  }

  pub fn get_type(
    &self,
    stype: &StringlyType,
  ) -> Option<Type<'ctx>> {
    match *stype {
      StringlyType::UserDefinedType(ref name) => {
        self.types.get(name).map(|t| Type(t))
      }
      _ => unimplemented!(),
    }
  }
}
