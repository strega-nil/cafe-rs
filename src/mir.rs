#![allow(dead_code)]

use parse::Location;
use ast::Ast;
use std::collections::HashMap;

#[derive(Debug)]
struct Function;

mod types {
  #[derive(Debug)]
  pub(super) enum IntSize {
    I8,
    I16,
    I32,
    I64,
    // ISize,
    // I128,
  }
  #[derive(Debug)]
  pub(super) enum BuiltinType {
    SInt(IntSize),
    UInt(IntSize),
    Bool,
  }

  #[derive(Debug)]
  pub(super) enum Type {
    Builtin(BuiltinType),
  }
}
use self::types::*;

#[derive(Debug)]
enum ItemVariant {
  Function(Function),
  Type(Type),
}
#[derive(Debug)]
struct Item {
  variant: ItemVariant,
  display_name: String,
  start: Location,
  end: Option<Location>,
}

struct ItemIdx(usize);

pub struct Mir {
  items: Vec<Item>,
  // NOTE(ubsan): when I get namespacing, I should probably
  // use paths for this?
  // or maybe a mod is an item...
  named_items: HashMap<String, ItemIdx>,
}

impl Mir {
  pub fn new(ast: Ast) -> Self {
    let _ast = ast;
    let _self = Mir {
      items: vec![],
      named_items: HashMap::new(),
    };
    // build mir
    _self
  }

  pub fn print(&self) {
    unimplemented!()
  }

  pub fn run(&self) {
    unimplemented!()
  }
}
