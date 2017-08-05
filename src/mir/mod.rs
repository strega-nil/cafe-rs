// TODO(ubsan): make sure to start dealing with Spanneds
// whee errors are fun

mod runner;

use ast::{Ast, StringlyType};
use containers::ArenaMap;

use self::runner::Runner;

use std::fmt::{self, Display};

#[derive(Copy, Clone, Debug)]
pub enum IntSize {
  //I8,
  //I16,
  I32,
  //I64,
  // ISize,
  // I128,
}
impl IntSize {
  fn size(self) -> u32 {
    match self {
      IntSize::I32 => 32,
    }
  }
}
#[derive(Debug)]
pub enum BuiltinType {
  SInt(IntSize),
  //UInt(IntSize),
  //Bool,
}
impl Display for BuiltinType {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match *self {
      BuiltinType::SInt(size) => write!(f, "s{}", size.size()),
    }
  }
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
impl Display for TypeVariant {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match *self {
      TypeVariant::Builtin(ref builtin) => {
        write!(f, "{}", builtin)
      }
    }
  }
}

#[derive(Copy, Clone, Debug)]
pub struct Reference(u32);

impl Reference {
  pub fn ret() -> Self {
    Reference(0)
  }
}

#[derive(Copy, Clone, Debug)]
pub enum Value {
  Literal(i32),
}

#[derive(Copy, Clone, Debug)]
pub struct Block(u32);

#[derive(Debug)]
pub enum Terminator {
  Goto(Block),
  Return,
}

#[derive(Copy, Clone, Debug)]
struct Statement {
  lhs: Reference,
  rhs: Value,
}

#[derive(Debug)]
struct BlockData {
  num: Block,
  stmts: Vec<Statement>,
  term: Terminator,
}

#[derive(Debug)]
struct FunctionValue<'ctx> {
  ret_ty: Type<'ctx>,
  blks: Vec<BlockData>,
  locals: Vec<Type<'ctx>>,
  bindings: Vec<(Option<String>, Type<'ctx>)>,
}

#[derive(Debug)]
pub struct FunctionBuilder<'ctx> {
  name: Option<String>,
  ret_ty: Type<'ctx>,
  locals: Vec<Type<'ctx>>,
  bindings: Vec<(Option<String>, Type<'ctx>)>,
  blks: Vec<BlockData>,
}

impl<'ctx> FunctionBuilder<'ctx> {
  fn new(name: Option<String>, ret_ty: Type<'ctx>) -> Self {
    let enter_block = BlockData {
      num: Block(0),
      stmts: vec![],
      term: Terminator::Goto(Block(1)),
    };
    let exit_block = BlockData {
      num: Block(1),
      stmts: vec![],
      term: Terminator::Return,
    };
    FunctionBuilder {
      name,
      ret_ty,
      locals: vec![],
      bindings: vec![(Some(String::from("<return>")), ret_ty)],
      blks: vec![enter_block, exit_block],
    }
  }

  pub fn entrance(&self) -> Block {
    Block(0)
  }
}

impl<'ctx> FunctionBuilder<'ctx> {
  pub fn add_stmt(
    &mut self,
    blk: Block,
    lhs: Reference,
    rhs: Value,
  ) {
    let blk_data = &mut self.blks[blk.0 as usize];
    blk_data.stmts.push(Statement { lhs, rhs });
  }

  pub fn anonymous_local(
    &mut self,
    ty: Type<'ctx>,
  ) -> Reference {
    self.locals.push(ty);
    self.bindings.push((None, ty));
    Reference((self.bindings.len() - 1) as u32)
  }
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

  pub fn get_function_builder(
    &self,
    name: Option<String>,
    ret_ty: Type<'ctx>,
  ) -> FunctionBuilder<'ctx> {
    FunctionBuilder::new(name, ret_ty)
  }

  pub fn insert_function(
    &self,
    builder: FunctionBuilder<'ctx>,
  ) -> Function<'ctx> {
    let value = FunctionValue {
      ret_ty: builder.ret_ty,
      blks: builder.blks,
      locals: builder.locals,
      bindings: builder.bindings,
    };
    if let Some(name) = builder.name {
      Function(self.funcs.insert(name, value))
    } else {
      Function(self.funcs.insert_anonymous(value))
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

impl<'ctx> Mir<'ctx> {
  pub fn print(&self) {
    for (name, ty) in &*self.types.hashmap() {
      print!("type {} :: ", name);
      match *unsafe { &**ty } {
        TypeVariant::Builtin(_) => {
          println!("<builtin>;");
        }
      }
    }
    for (name, value) in &*self.funcs.hashmap() {
      print!("{} :: ", name);
      let value = unsafe { &**value };
      println!("() -> {} {{", value.ret_ty.0);

      println!("  locals: {{");
      for loc_ty in &value.locals {
        println!("    {},", loc_ty.0);
      }
      println!("  }}");

      println!("  bindings: {{");
      for (i, binding) in value.bindings.iter().enumerate() {
        println!(
          "    {}_{}: {},",
          // fun hax
          binding.0.as_ref().map(|s| &**s).unwrap_or(""),
          i,
          (binding.1).0,
        );
      }
      println!("  }}");

      for bb in &value.blks {
        println!("  bb{}: {{", bb.num.0);
        for stmt in &bb.stmts {
          let Statement { ref lhs, ref rhs } = *stmt;
          if lhs.0 == 0 {
            print!("    <return> = ");
          } else {
            print!("    ");
            let opt_name = &value.bindings[lhs.0 as usize].0;
            if let Some(ref name) = *opt_name {
              print!("{}_{} = ", name, lhs.0 as usize);
            } else {
              print!("_{} = ", lhs.0 as usize);
            }
          }
          match *rhs {
            Value::Literal(n) => {
              println!("literal {};", n);
            }
          }
        }
        match bb.term {
          Terminator::Goto(blk) => {
            println!("    goto bb{};", blk.0);
          }
          Terminator::Return => {
            println!("    return;");
          }
        }
        println!("  }}");
      }
      println!("}}");
    }
  }
}
