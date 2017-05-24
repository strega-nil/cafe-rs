pub mod lexer;

use self::lexer::{Lexer, Token, TokenVariant, LexerError, LexerErrorVariant};

use std::str;

//use ty::{self, Type, TypeContext};

#[derive(Copy, Clone, Debug)]
pub struct Location {
  pub line: u32,
  pub column: u32,
}

impl Location {
  fn next_char(self) -> Self {
    Location {
      column: self.column + 1,
      line: self.line
    }
  }

  fn next_line(self) -> Self {
    Location {
      column: 1,
      line: self.line + 1,
    }
  }
}

#[derive(Copy, Clone, Debug)]
pub struct Spanned<T> {
  pub thing: T,
  pub start: Location,
  pub end: Option<Location>,
}

#[derive(Debug)]
pub enum Expression {
  IntLiteral(u64),
}
#[derive(Debug)]
pub enum Statement {
  Expr(Expression),
}

#[derive(Debug)]
pub struct Block {
  statements: Vec<Statement>,
  expr: Option<Expression>,
}

#[derive(Debug)]
pub enum ItemVariant {
  Function{
    params: Vec<(String, String)>,
    ret_ty: String,
    blk: Block,
  },
}

#[derive(Debug)]
pub struct Item_ {
  name: String,
  variant: ItemVariant,
}
pub type Item = Spanned<Item_>;

#[derive(Debug)]
pub enum ParserErrorVariant {
  ExpectedEof, // not an error

  LexerError(LexerErrorVariant),
  UnexpectedToken {
    found: Token,
    expected: (), // TODO(ubsan): figure out what this should be
  },
}
pub type ParserError = Spanned<ParserErrorVariant>;

impl From<LexerError> for ParserError {
  fn from(le: LexerError) -> Self {
    Spanned {
      thing: ParserErrorVariant::LexerError(le.thing),
      start: le.start,
      end: le.end,
    }
  }
}

pub type ParserResult<T> = Result<T, ParserError>;

pub struct Parser<'src> {
  lexer: Lexer<'src>,
  lookahead: Option<Token>,
}

impl<'src> Parser<'src> {
  pub fn new(file: &'src str) -> Self {
    Parser {
      lexer: Lexer::new(file),
      lookahead: None,
    }
  }

  fn get_token(&mut self) -> ParserResult<Token> {
    match self.lookahead.take() {
      Some(tok) => Ok(tok),
      None => Ok(self.lexer.next_token()?),
    }
  }
  fn peek_token(&mut self) -> ParserResult<&Token> {
    let tok = match self.lookahead {
      Some(ref tok) => return Ok(tok),
      None => self.lexer.next_token()?,
    };
    self.lookahead = Some(tok);
    if let Some(ref tok) = self.lookahead {
      Ok(tok)
    } else {
      unreachable!()
    }
  }

  pub fn next_item(&mut self) -> ParserResult<Item> {
    unimplemented!()
  }
}
