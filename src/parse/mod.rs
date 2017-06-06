pub mod lexer;

use self::lexer::{
  Lexer,
  LexerError,
  LexerErrorVariant,
  Token,
  TokenVariant,
};

use std::str;


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

#[derive(Copy, Clone, Debug)]
pub struct Location {
  pub line: u32,
  pub column: u32,
}

impl Location {
  fn new() -> Self {
    Location {
      line: 1,
      column: 0,
    }
  }

  fn next_char(self) -> Self {
    Location {
      column: self.column + 1,
      line: self.line
    }
  }

  fn next_line(self) -> Self {
    Location {
      column: 0,
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
  fn new(
    thing: T,
    start: Location,
    end: Option<Location>,
  ) -> Self {
    Spanned {
      thing,
      start,
      end,
    }
  }
}

#[derive(Debug)]
pub enum ExpressionVariant {
  Nullary,
  IntLiteral(u64),
}
type Expression = Spanned<ExpressionVariant>;
#[derive(Debug)]
pub enum StatementVariant {
  Expr(Expression),
}
type Statement = Spanned<StatementVariant>;

enum ExprOrStmt {
  Expr(Expression),
  Stmt(Statement),
}



#[derive(Debug)]
pub struct Block_ {
  statements: Vec<Statement>,
  expr: Expression,
}
type Block = Spanned<Block_>;

#[derive(Debug)]
pub enum ItemVariant {
  Function {
    params: Vec<(String, String)>,
    ret_ty: StringlyType,
    blk: Block_,
  },
}

#[derive(Debug)]
pub struct Item_ {
  name: String,
  definition: ItemVariant,
}
pub type Item = Spanned<Item_>;

#[derive(Clone, Debug)]
pub enum ExpectedToken {
  Ident,
  Item,
  Type,
  ExprEnd,
  SpecificToken(TokenVariant),
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

macro_rules! allow_eof {
  ($tok:expr) => (
    match $tok {
      t @ Ok(_) => t,
      Err(sp) => {
        let Spanned { thing, start, end } = sp;
        match thing {
          ParserErrorVariant::UnexpectedToken {
            found: TokenVariant::Eof,
            ..
          } => Err(Spanned {
            thing: ParserErrorVariant::ExpectedEof,
            start,
            end,
          }),
          thing => Err(Spanned { thing, start, end }),
        }
      },
    }
  )
}

macro_rules! eat_token {
  ($slf:expr, $tok:ident) => (
    match $slf.get_token()? {
      s @ Spanned { thing: TokenVariant::$tok, .. } => s,
      Spanned { thing, start, end } => return Err(Spanned {
        thing: ParserErrorVariant::UnexpectedToken {
          found: thing,
          expected:
            ExpectedToken::SpecificToken(
              TokenVariant::$tok,
            ),
        },
        start,
        end,
      }),
    }
  );
}

macro_rules! maybe_eat_token {
  ($slf:expr, $tok:ident) => ({
    match $slf.peek_token()? {
      &Spanned { thing: TokenVariant::$tok, .. }
      => Some($slf.get_token()?),
      _ => None,
    }
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

  // TODO(ubsan):
  // should maybe return a ParserResult<Spanned<String>>?
  fn parse_ident(&mut self) -> ParserResult<String> {
    let Spanned { thing, start, end } = self.get_token()?;
    match thing {
      TokenVariant::Ident(s) => Ok(s),
      tok => unexpected_token!(tok, Ident, start, end),
    }
  }

  fn parse_type(&mut self) -> ParserResult<StringlyType> {
    let Spanned { thing, start, end } = self.get_token()?;
    match thing {
      TokenVariant::Ident(s) => {
        Ok(StringlyType::UserDefinedType(s))
      },
      TokenVariant::And => unimplemented!(),
      TokenVariant::Star => unimplemented!(),
      TokenVariant::OpenParen => unimplemented!(),
      tok => Err(Spanned {
        thing: ParserErrorVariant::UnexpectedToken {
          found: tok,
          expected: ExpectedToken::Type,
        },
        start,
        end,
      }),
    }
  }

  fn parse_expr(&mut self) -> ParserResult<Expression> {
    match *self.peek_token()? {
      Spanned {
        thing: TokenVariant::Semicolon,
        start,
        ..
      }
      | Spanned {
        thing: TokenVariant::CloseBrace,
        start,
        ..
      } => {
        Ok(Spanned::new(
          ExpressionVariant::Nullary,
          start,
          Some(start)
        ))
      },
      _ => match self.get_token()? {
        Spanned {
          thing: TokenVariant::Integer(u),
          start,
          end,
        } => {
          Ok(Spanned::new(
            ExpressionVariant::IntLiteral(u),
            start,
            end,
          ))
        },
        tok => {
          panic!("unimplemented expression: {:?}", tok)
        },
      },
    }
  }

  fn parse_expr_or_stmt(
    &mut self,
  ) -> ParserResult<ExprOrStmt> {
    match *self.peek_token()? {
      Spanned { thing: TokenVariant::KeywordLet, .. } => {
        unimplemented!()
      },
      _ => {
        let expr = self.parse_expr()?;
        if let Spanned {
          thing: TokenVariant::CloseBrace, ..
        } = *self.peek_token()?  {
          return Ok(ExprOrStmt::Expr(expr))
        }

        match self.get_token()? {
          Spanned {
            thing: TokenVariant::Semicolon,
            end,
            ..
          } => {
            let start = expr.start;
            return Ok(ExprOrStmt::Stmt(Spanned::new(
              StatementVariant::Expr(expr),
              start,
              end,
            )));
          },
          Spanned { thing, start, end } => {
            unexpected_token!(thing, ExprEnd, start, end)
          }
        }
      }
    }
  }

  fn parse_block(&mut self) -> ParserResult<Block> {
    let mut statements = vec![];
    let expr;

    let sp_start = eat_token!(self, OpenBrace);
    loop {
      match self.parse_expr_or_stmt()? {
        ExprOrStmt::Expr(e) => {
          expr = e;
          break;
        },
        ExprOrStmt::Stmt(s) => statements.push(s),
      }
    }
    let sp_end = eat_token!(self, CloseBrace);
    let thing = Block_ {
      statements,
      expr,
    };
    Ok(Spanned::new(thing, sp_start.start, sp_end.end))
  }

  fn parse_item_definition(
    &mut self,
  ) -> ParserResult<Spanned<ItemVariant>> {
    let Spanned { thing, start, end } = self.get_token()?;
    match thing {
      TokenVariant::KeywordFn => {
        let start = eat_token!(self, OpenParen);
        // argument list
        eat_token!(self, CloseParen);
        let ret_ty = {
          if let Some(_) =
            maybe_eat_token!(self, SkinnyArrow)
          {
            self.parse_type()?
          } else {
            StringlyType::Tuple(vec![])
          }
        };
        let blk = self.parse_block()?;
        let thing = ItemVariant::Function {
          params: vec![],
          ret_ty,
          blk: blk.thing,
        };
        Ok(Spanned::new(thing, start.start, blk.end))
      },
      tok => unexpected_token!(tok, Item, start, end),
    }
  }

  pub fn next_item(&mut self) -> ParserResult<Item> {
    let name = allow_eof!(self.parse_ident())?;
    let sp = eat_token!(self, Colon);
    /*
      parse type parameters here
    */
    let def = self.parse_item_definition()?;

    let thing = Item_ {
      name,
      definition: def.thing,
    };
    Ok(Spanned::new(thing, sp.start, def.end))
  }
}
