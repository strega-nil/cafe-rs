#![allow(dead_code)]

use containers::{Arena, ArenaMap};
use parse::{Location, Spanned};
use ast::{self, Ast, StringlyType};
use std::collections::HashSet;
use std::sync::RwLock;


mod types {
  #[derive(Debug)]
  pub(super) enum IntSize {
    //I8,
    //I16,
    I32,
    //I64,
    // ISize,
    // I128,
  }
  #[derive(Debug)]
  pub(super) enum BuiltinType {
    SInt(IntSize),
    //UInt(IntSize),
    //Bool,
  }

  #[derive(Debug)]
  pub(super) enum TypeVariant {
    Builtin(BuiltinType),
  }
}
use self::types::*;

#[derive(Copy, Clone, Debug)]
struct Type<'tcx>(&'tcx TypeVariant /* <'tcx> */);

#[derive(Debug)]
struct Function<'tcx> {
  ret_ty: Type<'tcx>,
}

#[derive(Debug)]
enum ItemVariant<'tcx> {
  Function(Function<'tcx>),
  Type(Type<'tcx>),
}
#[derive(Debug)]
struct Item<'tcx> {
  variant: ItemVariant<'tcx>,
  display_name: String,
  start: Location,
  end: Option<Location>,
}

struct ItemIdx(usize);

pub struct MirCtxt(Arena<TypeVariant>);

impl MirCtxt {
  pub fn new() -> Self { MirCtxt(Arena::new()) }
}

pub struct Mir<'tcx> {
  // NOTE(ubsan): when I get namespacing, I should probably
  // use paths for this?
  items: ArenaMap<String, Item<'tcx>>,
  types: &'tcx Arena<TypeVariant/* <'tcx> */>,
  // NOTE(ubsan): make sure we don't create loops
  working: RwLock<HashSet<String>>,
}

impl<'tcx> Mir<'tcx> {
  pub fn new(types: &'tcx MirCtxt, ast: Ast) -> Self {
    let ast = ast;
    let self_: Mir<'tcx> = Mir {
      types: &types.0,
      items: ArenaMap::new(),
      working: RwLock::new(HashSet::new()),
    };

    self_.prelude_types();
    self_.build(ast);

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

impl<'tcx> Mir<'tcx> {
  fn prelude_types(&self) {
    let ref_ = self.types.push(
      TypeVariant::Builtin(BuiltinType::SInt(IntSize::I32)),
    );
    let item = Item {
      variant: ItemVariant::Type(Type(ref_)),
      display_name: String::from("s32"),
      start: Location::new(),
      end: None,
    };
    self.items.insert(String::from("s32"), item);
  }

  fn build(&self, ast: Ast) {
    for (name, item) in &ast.items {
      if self.items.contains(name) {
        continue;
      }

      self.build_item(name, item);
    }
  }

  fn build_item(&self, name: &str, item: &ast::Item) {
    use ast::ItemVariant as IV;
    let Spanned { thing: ref v, start, end } = *item;

    self.working.write().unwrap().insert(name.to_owned());
    match *v {
      IV::Function {
        //ref params,
        ref ret_ty,
        ref blk,
      } => {
        let itm = Item {
          variant: self.build_func(ret_ty, blk),
          display_name: name.to_owned(),
          start,
          end,
        };
        self.items.insert(name.to_owned(), itm);
      }
    }
    self.working.write().unwrap().remove(name);
  }

  fn build_func(
    &self,
    ret_ty: &StringlyType,
    _blk: &ast::Block_,
  ) -> ItemVariant<'tcx> {
    let ret_ty = self.get_type(ret_ty);
    ItemVariant::Function(Function {
      ret_ty
    })
  }

  fn get_type(&self, stype: &StringlyType) -> Type<'tcx> {
    match *stype {
      StringlyType::UserDefinedType(ref name) => {
        if let Some(ty) = self.items.get(name) {
          if let ItemVariant::Type(ty) = ty.variant {
            return ty;
          } else {
            unimplemented!()
          }
        }
        unimplemented!()
      },
      _ => unimplemented!(),
    }
  }
}
