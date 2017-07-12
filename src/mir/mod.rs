// TODO(ubsan): make sure to start dealing with Spanneds
// whee errors are fun

mod runner;

use ast::{Ast, StringlyType};
use containers::ArenaMap;

use self::runner::Runner;

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
struct FunctionValue<'ctx> {
  ret_ty: Type<'ctx>,
  //blks: Vec<BlockData>,
}

#[derive(Copy, Clone, Debug)]
pub struct Type<'ctx>(&'ctx TypeVariant /* <'ctx> */);
#[derive(Copy, Clone, Debug)]
pub struct Function<'ctx>(&'ctx FunctionValue<'ctx>);

// NOTE(ubsan): when I get namespacing, I should probably
// use paths instead of names?

pub struct MirCtxt<'a> {
  types: ArenaMap<String, TypeVariant /*<'a>*/>,
  funcs: ArenaMap<String, FunctionValue<'a>>,
}

impl<'a> MirCtxt<'a> {
  pub fn new() -> Self {
    MirCtxt {
      types: ArenaMap::new(),
      funcs: ArenaMap::new(),
    }
  }
}

pub struct Mir<'ctx> {
  funcs: &'ctx ArenaMap<String, FunctionValue<'ctx>>,
  types: &'ctx ArenaMap<String, TypeVariant /*<'ctx>*/>,
}

impl<'ctx> Mir<'ctx> {
  pub fn new(ctx: &'ctx MirCtxt<'ctx>, mut ast: Ast) -> Self {
    let mut self_: Mir<'ctx> = Mir {
      funcs: &ctx.funcs,
      types: &ctx.types,
    };

    ast.build_mir(&mut self_);

    self_
  }

  pub fn print(&self) {
    for (name, ty) in &*self.types.hashmap() {
      println!("type {} = {:?}", name, unsafe { &**ty });
    }
    for (name, value) in &*self.funcs.hashmap() {
      println!("fn {} = {:?}", name, unsafe { &**value });
    }
  }

  pub fn run(&self) -> i32 {
    Runner::new(self).call("main")
  }
}

impl<'ctx> Mir<'ctx> {
  pub fn insert_type(
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

  pub fn insert_function(
    &self,
    name: Option<String>,
    ret_ty: Type<'ctx>,
  ) -> Function<'ctx> {
    let value = FunctionValue { ret_ty };
    if let Some(name) = name {
      Function(self.funcs.insert(name, value))
    } else {
      Function(self.funcs.insert_anonymous(value))
    }
  }

  pub fn get_type(&self, stype: &StringlyType) -> Option<Type<'ctx>> {
    match *stype {
      StringlyType::UserDefinedType(ref name) => {
        self.types.get(name).map(|t| Type(t))
      }
      _ => unimplemented!(),
    }
  }
}
