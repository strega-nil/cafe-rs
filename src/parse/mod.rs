pub mod lexer;

use self::lexer::{Lexer, LexerError, LexerErrorVariant, Token,
                  TokenVariant};
use ast::{BinOp, Block, Block_, Expression, ExpressionVariant,
          FunctionValue, Statement, StatementVariant,
          StringlyType};

use std::ops::{Deref, DerefMut};
use std::str;

#[derive(Copy, Clone, Debug)]
pub struct Location {
  pub line: u32,
  pub column: u32,
}

impl Location {
  pub fn new() -> Self {
    Location { line: 1, column: 0 }
  }

  pub fn next_char(self) -> Self {
    Location {
      column: self.column + 1,
      line: self.line,
    }
  }

  pub fn next_line(self) -> Self {
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
    Spanned { thing, start, end }
  }
}

impl<T> Deref for Spanned<T> {
  type Target = T;
  fn deref(&self) -> &T {
    &self.thing
  }
}
impl<T> DerefMut for Spanned<T> {
  fn deref_mut(&mut self) -> &mut T {
    &mut self.thing
  }
}

enum ExprOrStmt {
  Expr(Expression),
  Stmt(Statement),
}

pub enum ItemVariant {
  Function(FunctionValue),
  //Type(Type),
}
pub type Item = Spanned<ItemVariant>;

#[derive(Clone, Debug)]
pub enum ExpectedToken {
  Item,
  Type,
  ExprEnd,
  Expr,
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

  /*
  // TODO(ubsan):
  // should maybe return a ParserResult<Spanned<String>>?
  fn parse_ident(&mut self) -> ParserResult<String> {
    let Spanned { thing, start, end } = self.get_token()?;
    match thing {
      TokenVariant::Ident(s) => Ok(s),
      tok => unexpected_token!(tok, Ident, start, end),
    }
  }
  */

  fn parse_type(&mut self) -> ParserResult<StringlyType> {
    let Spanned { thing, start, end } = self.get_token()?;
    match thing {
      TokenVariant::Ident(s) => {
        Ok(StringlyType::UserDefinedType(s))
      }
      //TokenVariant::And => unimplemented!(),
      //TokenVariant::Star => unimplemented!(),
      TokenVariant::OpenParen => unimplemented!(),
      tok => {
        unexpected_token!(tok, Type, start, end)
      },
    }
  }

  fn end_of_expr(s: &Token) -> Option<Token> {
    match **s {
      TokenVariant::Semicolon => {
        Some(Spanned::new(
          TokenVariant::Semicolon,
          s.start,
          s.end,
        ))
      }
      TokenVariant::CloseBrace => {
        Some(Spanned::new(
          TokenVariant::CloseBrace,
          s.start,
          s.end,
        ))
      }
      _ => {
        None
      }
    }
  }

  fn parse_single_expr(&mut self) -> ParserResult<Expression> {
    if let Some(tok) = Self::end_of_expr(self.peek_token()?) {
      return
        unexpected_token!(tok.thing, Expr, tok.start, tok.end);
    }
    let Spanned { thing, start, end } = self.get_token()?;
    match thing {
      TokenVariant::Integer(u) => {
        Ok(Spanned::new(
          ExpressionVariant::IntLiteral(u),
          start,
          end,
        ))
      }
      TokenVariant::Ident(s) => {
        Ok(Spanned::new(
          ExpressionVariant::Variable(s),
          start,
          end,
        ))
      }
      tok => {
        panic!(
          "unimplemented expression: {:?}",
          Spanned { thing: tok, start, end },
        )
      }
    }
  }

  // NOTE(ubsan): there's probably a better way to do this
  fn parse_single_expr_or_null(
    &mut self,
  ) -> ParserResult<Expression> {
    let ret = self.parse_single_expr();
    if let Err(ref e) = ret {
      if let ParserErrorVariant::UnexpectedToken {
        ref found,
        expected: ExpectedToken::Expr,
      } = e.thing {
        if (
          *found == TokenVariant::Semicolon
          || *found == TokenVariant::CloseBrace
        ) {
          return Ok(Spanned::new(
            ExpressionVariant::Nullary,
            e.start,
            e.end,
          ));
        }
      }
    }
    ret
  }

  fn parse_binop(
    &mut self,
    lhs: Expression,
    op: BinOp,
  ) -> ParserResult<Expression> {
    let rhs = self.parse_single_expr()?;
    if Self::end_of_expr(self.peek_token()?).is_some() {
      let start = lhs.start;
      let end = rhs.end;
      return Ok(Spanned::new(
        ExpressionVariant::BinOp {
          lhs: Box::new(lhs),
          rhs: Box::new(rhs),
          op,
        },
        start,
        end,
      ));
    }
    unimplemented!()
  }

  fn parse_expr(&mut self) -> ParserResult<Expression> {
    let lhs = self.parse_single_expr_or_null()?;
    if Self::end_of_expr(self.peek_token()?).is_some() {
      return Ok(lhs);
    }

    let Token { thing, .. } = self.get_token()?;
    match thing {
      TokenVariant::OpenParen => { // function call
        let Token { end, .. } = eat_token!(self, CloseParen);
        if let ExpressionVariant::Variable(callee) = lhs.thing {
          Ok(Spanned::new(
            ExpressionVariant::Call {
              callee
            },
            lhs.start,
            end,
          ))
        } else {
          unimplemented!()
        }
      }
      // NOTE(ubsan): should probably be a "is_binop" call
      TokenVariant::Plus => {
        self.parse_binop(lhs, BinOp::Plus)
      }
      _ => unimplemented!()
    }
  }

  fn parse_expr_or_stmt(&mut self) -> ParserResult<ExprOrStmt> {
    let expr = self.parse_expr()?;
    { // NLLs pls
      let Spanned { ref thing, .. } =
        *self.peek_token()?;
      if let TokenVariant::CloseBrace = *thing {
        return Ok(ExprOrStmt::Expr(expr));
      }
    }

    let Spanned { thing, start, end } = self.get_token()?;
    match thing {
      TokenVariant::Semicolon => {
        let start = expr.start;
        Ok(ExprOrStmt::Stmt(Spanned::new(
          StatementVariant::Expr(expr),
          start,
          end,
        )))
      }
      // local variable
      TokenVariant::Colon => {
        let name =
          if let ExpressionVariant::Variable(s) = expr.thing {
            s
          } else {
            panic!("invalid thing as a variable name");
          };
        let ty = self.parse_type()?;
        // I'll allow non-initialized later
        eat_token!(self, Equals);
        let initializer = self.parse_expr()?;
        let Spanned { end, .. } = eat_token!(self, Semicolon);
        Ok(ExprOrStmt::Stmt(Spanned::new(
          StatementVariant::Local {
            name,
            ty,
            initializer,
          },
          expr.start,
          end,
        )))
      }
      _ => {
        unexpected_token!(thing, ExprEnd, start, end)
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
        }
        ExprOrStmt::Stmt(s) => statements.push(s),
      }
    }
    let sp_end = eat_token!(self, CloseBrace);
    let thing = Block_ { statements, expr };
    Ok(Spanned::new(thing, sp_start.start, sp_end.end))
  }

  fn parse_item_definition(
    &mut self,
  ) -> ParserResult<(String, Item)> {
    let Spanned { thing, start, end } = self.get_token()?;
    match thing {
      TokenVariant::Ident(name) => {
        eat_token!(self, ColonColon);
        eat_token!(self, OpenParen);
        // argument list
        eat_token!(self, CloseParen);
        let ret_ty = {
          if let Some(_) = maybe_eat_token!(self, SkinnyArrow) {
            self.parse_type()?
          } else {
            StringlyType::Unit
          }
        };
        let blk = self.parse_block()?;
        let thing = ItemVariant::Function(FunctionValue {
          //params: vec![],
          ret_ty,
          blk: blk.thing,
        });
        Ok((name, Spanned::new(thing, start, blk.end)))
      }
      tok => unexpected_token!(tok, Item, start, end),
    }
  }

  pub fn next_item(&mut self) -> ParserResult<(String, Item)> {
    /*
      parse type parameters here
    */
    let item = allow_eof!(self.parse_item_definition())?;
    Ok(item)
  }
}
