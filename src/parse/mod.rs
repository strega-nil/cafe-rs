pub mod lexer;

use self::lexer::{
  Lexer,
  LexerError,
  LexerErrorVariant,
  Token,
  TokenVariant,
  ItemToken,
};

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

impl<T> Spanned<T> {
  fn map<U, F>(self, f: F) -> Spanned<U>
    where F: Fn(T) -> U
  {
    Spanned {
      thing: f(self.thing),
      start: self.start,
      end: self.end,
    }
  }
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

#[derive(Copy, Clone, Debug)]
pub enum ExpectedToken {
  Ident,
  Colon,
  Item,
}

#[derive(Debug)]
pub enum ParserErrorVariant {
  ExpectedEof, // not an error

  LexerError(LexerErrorVariant),
  UnexpectedToken {
    found: TokenVariant,
    expected: ExpectedToken,
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

macro_rules! unexpected_token {
  ($tok:expr, $expected:ident, $start:expr, $end:expr) => ({
    let thing = ParserErrorVariant::UnexpectedToken {
      found: $tok,
      expected: ExpectedToken::$expected,
    };
    Err(Spanned {
      thing,
      start: $start,
      end: $end,
    })
  });
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

  // TODO(ubsan): maybe should return a ParserResult<Spanned<String>>?
  fn tok_ident(&mut self) -> ParserResult<String> {
    let Spanned { thing, start, end } = self.get_token()?;
    match thing {
      TokenVariant::Ident(s) => Ok(s),
      tok => unexpected_token!(tok, Ident, start, end),
    }
  }

  fn tok_colon(&mut self) -> ParserResult<()> {
    let Spanned { thing, start, end } = self.get_token()?;
    match thing {
      TokenVariant::Colon => Ok(()),
      tok => unexpected_token!(tok, Colon, start, end),
    }
  }

  fn tok_item_kind(&mut self) -> ParserResult<ItemToken> {
    let Spanned { thing, start, end } = self.get_token()?;
    match thing {
      TokenVariant::Item(item) => Ok(item),
      tok => unexpected_token!(tok, Item, start, end),
    }
  }

  pub fn next_item(&mut self) -> ParserResult<Item> {
    let name = self.tok_ident()?;
    self.tok_colon()?;
    /*
      parse type parameters here
    */
    match self.tok_item_kind()? {
      ItemToken::KeywordFn => unimplemented!(),
    }
  }
}
