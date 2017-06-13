use std::collections::HashMap;

use parse::{Location, Parser, ParserErrorVariant, Spanned};
use mir::{self, Mir};
use std::collections::HashSet;

#[derive(Clone, Debug)]
#[allow(dead_code)]
pub enum Category {
  Raw,
  Shared,
  Mut,
  Own,
}

// user defined types will be strings
#[derive(Clone, Debug)]
pub enum StringlyType {
  Tuple(Vec<StringlyType>),
  #[allow(dead_code)]
  Reference(Category, Box<StringlyType>),
  #[allow(dead_code)]
  Pointer(Category, Box<StringlyType>),
  UserDefinedType(String),
}

#[derive(Debug)]
pub enum ExpressionVariant {
  Nullary,
  IntLiteral(u64),
}
pub type Expression = Spanned<ExpressionVariant>;
#[derive(Debug)]
pub enum StatementVariant {
  Expr(Expression),
}
pub type Statement = Spanned<StatementVariant>;


#[derive(Debug)]
pub struct Block_ {
  pub statements: Vec<Statement>,
  pub expr: Expression,
}
pub type Block = Spanned<Block_>;

#[derive(Debug)]
pub enum ItemVariant {
  Function {
    //params: Vec<(String, StringlyType)>,
    ret_ty: StringlyType,
    blk: Block_,
  },
}
pub type Item = Spanned<ItemVariant>;

impl ItemVariant {
  fn build_mir(&self, mir: &Mir) {
    match *self {
      _ => unimplemented!()
    }
  }
}

pub struct Ast {
  items: HashMap<String, Item>,
}

impl Ast {
  pub fn new(file: &str) -> Self {
    let mut parse = Parser::new(file);
    let mut items = HashMap::new();
    loop {
      match parse.next_item() {
        Ok((name, item)) => {
          items.insert(name, item);
        },
        Err(Spanned {
          thing: ParserErrorVariant::ExpectedEof,
          ..
        }) => break,
        Err(e) => panic!("error: {:#?}", e),
      }
    }
    Ast {
      items
    }
  }

  pub fn print(&self) {
    for item in &self.items {
      println!("{} :: {:#?}", item.0, item.1.thing);
    }
  }
}

impl Ast {
  pub fn build_mir<'ctx>(&mut self, mir: &mut Mir<'ctx>) {
    Self::prelude_types(mir);
    for (name, item) in &self.items {
      let mut working = HashSet::new();
      working.insert(name);
      //item.build_mir(name, mir);
    }
  }

  fn prelude_types(mir: &Mir) {
    let ty = Spanned {
      thing: mir::TypeVariant::s32(),
      start: Location::new(),
      end: None,
    };
    mir.type_(Some(String::from("s32")), ty);
  }
}
