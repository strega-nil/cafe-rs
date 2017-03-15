use pom::DataInput;

mod lex {
  pub use pom::parser::*;

  use pom::char_class;
  use super::{Block, Expression, Item, Statement};

  pub fn whitespace() -> Parser<'static, u8, ()> {
    is_a(char_class::multispace).repeat(1..).discard()
  }

  pub fn ident() -> Parser<'static, u8, String> {
    (
      is_a(char_class::alpha)
      + is_a(char_class::alphanum).repeat(0..)
    ).name("identifier").map(|(fst, rest)| {
      let mut s = String::with_capacity(rest.len() + 1);
      s.push(fst as char);
      for c in rest { s.push(c as char) }
      s
    })
  }

  pub fn int_lit() -> Parser<'static, u8, Expression> {
    is_a(char_class::digit).repeat(1..).map(|digits| {
      let mut n = 0;
      for c in digits {
        n *= 10;
        n += (c - b'0') as u64;
      }
      Expression::IntegerLiteral(n)
    }).name("int literal")
  }

  pub fn expression() -> Parser<'static, u8, Expression> {
    int_lit().name("expression")
  }

  pub fn statement() -> Parser<'static, u8, Statement> {
    (
      expression()
      - whitespace().opt()
      - sym(b';')
    ).name("statement").map(|expr| Statement::Expression(expr))
  }

  pub fn block() -> Parser<'static, u8, Block> {
    (
      sym(b'{')
      * whitespace().opt()
      * (statement().repeat(0..) - whitespace().opt())
      + expression().opt()
      - whitespace().opt()
      - sym(b'}')
    ).name("block").map(|(stmts, expr)| Block { stmts, expr })
  }

  pub fn func() -> Parser<'static, u8, Item> {
    (
      (
        seq(b"fn")
        * whitespace()
        * ident()
        - whitespace().opt()
        - sym(b'(')
        - whitespace().opt()
        - sym(b')')
        - whitespace().opt()
      ) + block()
    ).name("function").map(|(name, blk)| Item::Function { name, blk })
  }

  pub fn item() -> Parser<'static, u8, Item> {
    func()
  }
}

#[derive(Debug)]
pub enum Expression {
  IntegerLiteral(u64),
}

#[derive(Debug)]
pub enum Statement {
  Expression(Expression),
}

#[derive(Debug)]
pub struct Block {
  pub stmts: Vec<Statement>,
  pub expr: Option<Expression>,
}

#[derive(Debug)]
pub enum Item {
  Function {
    name: String,
    blk: Block,
  },
}

#[derive(Debug)]
pub struct Ast {
  pub items: Vec<Item>,
}

impl Ast {
  pub fn parse(data: &[u8]) -> Ast {
    let mut data = DataInput::new(data.into());
    (
      (lex::item() - lex::whitespace().opt()).repeat(0..)
      - lex::end()
    ).map(|items| Ast { items }).parse(&mut data).unwrap()
  }
}
