use std::collections::HashMap;

use mir::{self, Mir};
use parse::{ItemVariant, Parser, ParserError, ParserErrorVariant,
            Spanned};
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
pub struct FunctionValue {
  //params: Vec<(String, StringlyType)>,
  pub ret_ty: StringlyType,
  pub blk: Block_,
}
pub type Function = Spanned<FunctionValue>;

impl Function {
  fn build_mir(&self, name: &str, mir: &Mir) {
    match self.thing {
      FunctionValue { ref ret_ty, blk: _ } => {
        let ret_ty = mir.get_type(ret_ty).unwrap();
        mir.insert_function(Some(name.to_owned()), ret_ty)
      }
    };
  }
}

#[derive(Debug)]
pub enum AstErrorVariant {
  Parser(ParserErrorVariant),
  MultipleValueDefinitions {
    name: String,
    original: Spanned<()>,
  },
}
pub type AstError = Spanned<AstErrorVariant>;
pub type AstResult<T> = Result<T, AstError>;

impl From<ParserError> for AstError {
  fn from(pe: ParserError) -> AstError {
    Spanned {
      thing: AstErrorVariant::Parser(pe.thing),
      start: pe.start,
      end: pe.end,
    }
  }
}

pub struct Ast {
  funcs: HashMap<String, Function>,
}

impl Ast {
  pub fn new(file: &str) -> AstResult<Self> {
    let mut parse = Parser::new(file);
    let mut funcs = HashMap::<String, Function>::new();
    loop {
      match parse.next_item() {
        Ok((
          name,
          Spanned {
            thing: ItemVariant::Function(thing),
            start,
            end,
          },
        )) => {
          if let Some(orig) = funcs.get(&name) {
            return Err(Spanned {
              thing: AstErrorVariant::MultipleValueDefinitions {
                name: name.clone(),
                original: Spanned {
                  thing: (),
                  start: orig.start,
                  end: orig.end,
                },
              },
              start,
              end,
            });
          };
          funcs.insert(name, Spanned { thing, start, end });
        }
        Err(Spanned {
          thing: ParserErrorVariant::ExpectedEof,
          ..
        }) => break,
        Err(e) => return Err(e.into()),
      }
    }
    Ok(Ast { funcs })
  }

  pub fn print(&self) {
    for value in &self.funcs {
      println!("{} :: {:#?}", value.0, value.1.thing);
    }
  }
}

impl Ast {
  pub fn build_mir<'ctx>(&mut self, mir: &mut Mir<'ctx>) {
    Self::prelude_types(mir);
    for (name, func) in &self.funcs {
      let mut working = HashSet::new();
      working.insert(name);
      func.build_mir(name, mir);
    }
  }

  fn prelude_types(mir: &Mir) {
    mir.insert_type(
      Some(String::from("s32")), mir::TypeVariant::s32()
    );
  }
}
