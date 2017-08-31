pub mod lexer;

use self::lexer::{Lexer, LexerError, LexerErrorVariant, Token,
                  TokenVariant};
use ast::{BinOp, Block, Block_, Expression, ExpressionVariant,
          FunctionValue, Statement, StatementVariant,
          StringlyType};

use std::ops::{Deref, DerefMut};
use std::str;

// TODO(ubsan): figure out how to better parse optional comma

enum Either<T, U> {
  Left(T),
  Right(U),
}
use self::Either::{Left, Right};

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

pub enum ItemVariant {
  Function(FunctionValue),
  //Type(Type),
}
pub type Item = Spanned<ItemVariant>;

#[derive(Clone, Debug)]
pub enum ExpectedToken {
  Ident,
  Type,
  Expr,
  Parameter,
  Argument,
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
  (
    $tok:expr,
    $expected:ident,
    $start:expr,
    $end:expr
    $(,)*
  ) => ({
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
  (
    $tok:expr,
    $expected:ident
    $(,)*
  ) => ({
    unexpected_token!(
      $tok.thing,
      $expected,
      $tok.start,
      $tok.end,
    )
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
  ($slf:expr, $tok:ident) => ({
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
  });
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

// NOTE(ubsan): once we get internal blocks, we should really
// have one function for parsing both func and let definitions
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

  fn end_of_expr(s: &Token) -> Option<Token> {
    match **s {
      TokenVariant::Semicolon => Some(
        Spanned::new(TokenVariant::Semicolon, s.start, s.end),
      ),
      TokenVariant::CloseBrace => Some(
        Spanned::new(TokenVariant::CloseBrace, s.start, s.end),
      ),
      TokenVariant::CloseParen => Some(
        Spanned::new(TokenVariant::CloseParen, s.start, s.end),
      ),
      _ => None,
    }
  }

  fn binop(s: &Token) -> Option<BinOp> {
    match **s {
      TokenVariant::Plus => Some(BinOp::Plus),
      _ => None,
    }
  }

  fn parse_type(&mut self) -> ParserResult<StringlyType> {
    let Spanned { thing, start, end } = self.get_token()?;
    match thing {
      TokenVariant::Ident(s) => {
        Ok(StringlyType::UserDefinedType(s))
      }
      //TokenVariant::And => unimplemented!(),
      //TokenVariant::Star => unimplemented!(),
      tok => unexpected_token!(tok, Type, start, end),
    }
  }

  fn maybe_parse_single_expr(
    &mut self,
  ) -> ParserResult<Either<Expression, Token>> {
    if let Some(tok) = Self::end_of_expr(self.peek_token()?) {
      return Ok(Right(tok));
    }
    let Spanned { thing, start, end } = self.get_token()?;

    let mut expr = match thing {
      TokenVariant::Integer(u) => Spanned::new(
        ExpressionVariant::IntLiteral(u),
        start,
        end,
      ),
      TokenVariant::Minus => {
        let expr = self.parse_single_expr()?;
        Spanned::new(
          ExpressionVariant::Negative(Box::new(expr)),
          start,
          end,
        )
      }
      TokenVariant::OpenParen => {
        let end = eat_token!(self, CloseParen).end;
        Spanned::new(
          ExpressionVariant::UnitLiteral,
          start,
          end,
        )
      }
      TokenVariant::Ident(s) => {
        Spanned::new(ExpressionVariant::Variable(s), start, end)
      }
      TokenVariant::KeywordTrue => Spanned::new(
        ExpressionVariant::BoolLiteral(true),
        start,
        end,
      ),
      TokenVariant::KeywordFalse => Spanned::new(
        ExpressionVariant::BoolLiteral(false),
        start,
        end,
      ),
      TokenVariant::KeywordIf => {
        let cond = self.parse_expr()?;
        eat_token!(self, OpenBrace);
        let then = self.parse_expr()?;
        eat_token!(self, CloseBrace);
        eat_token!(self, KeywordElse);
        eat_token!(self, OpenBrace);
        let els = self.parse_expr()?;
        let end = eat_token!(self, CloseBrace).end;
        Spanned::new(
          ExpressionVariant::IfElse {
            cond: Box::new(cond),
            then: Box::new(then),
            els: Box::new(els),
          },
          start,
          end,
        )
      }
      TokenVariant::KeywordElse => {
        return unexpected_token!(
          TokenVariant::KeywordElse,
          Expr,
          start,
          end,
        );
      }
      tok => panic!(
        "unimplemented expression: {:?}",
        Spanned {
          thing: tok,
          start,
          end,
        },
      ),
    };

    // NOTE(ubsan): should be while let, for multiple function
    // calls in a row
    if let TokenVariant::OpenParen = **self.peek_token()? {
      self.get_token()?;

      let mut args = vec![];
      let end;
      loop {
        match self.maybe_parse_expr()? {
          Left(expr) => {
            args.push(expr);
            if let None = maybe_eat_token!(self, Comma) {
              end = eat_token!(self, CloseParen).end;
              break;
            }
          }
          Right(tok) => if let TokenVariant::CloseParen = *tok {
            self.get_token()?;
            end = tok.end;
            break;
          } else {
            return unexpected_token!(tok, Argument);
          },
        }
      }

      if let ExpressionVariant::Variable(callee) = expr.thing {
      // NOTE(ubsan): special handling for logging
        if callee == "log" {
          assert!(args.len() == 1);
          let arg = args.into_boxed_slice();
          let arg = unsafe {
            Box::from_raw(
              Box::into_raw(arg) as *mut Expression,
            )
          };
          expr = Spanned::new(
            ExpressionVariant::Log(arg),
            expr.start,
            end,
          );
        } else {
          expr = Spanned::new(
            ExpressionVariant::Call { callee, args },
            expr.start,
            end,
          );
        }
      } else {
        unimplemented!()
      }
    }

    Ok(Left(expr))
  }

  fn parse_single_expr(&mut self) -> ParserResult<Expression> {
    match self.maybe_parse_single_expr()? {
      Right(tok) => {
        unexpected_token!(tok.thing, Expr, tok.start, tok.end)
      }
      Left(e) => Ok(e),
    }
  }

  fn parse_binop(
    &mut self,
    lhs: Expression,
    left_op: BinOp,
  ) -> ParserResult<Expression> {
    fn op(
      op: BinOp,
      lhs: Expression,
      rhs: Expression,
    ) -> Expression {
      let start = lhs.start;
      let end = rhs.end;
      let expr = ExpressionVariant::BinOp {
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
        op,
      };
      Spanned::new(expr, start, end)
    }

    let rhs = self.parse_single_expr()?;

    if let Some(right_op) = Self::binop(self.peek_token()?) {
      self.get_token()?;
      if left_op.precedence() >= right_op.precedence() {
        let new_lhs = op(left_op, lhs, rhs);
        return self.parse_binop(new_lhs, right_op);
      } else {
        let new_rhs = self.parse_binop(rhs, right_op)?;
        return Ok(op(left_op, lhs, new_rhs));
      }
    } else {
      Ok(op(left_op, lhs, rhs))
    }
  }

  fn maybe_parse_expr(
    &mut self,
  ) -> ParserResult<Either<Expression, Token>> {
    let lhs = match self.maybe_parse_single_expr()? {
      Left(expr) => expr,
      Right(tok) => return Ok(Right(tok)),
    };

    match self.peek_token()?.thing {
      // NOTE(ubsan): should probably be a "is_binop" call
      TokenVariant::Plus => {
        self.get_token()?;
        self.parse_binop(lhs, BinOp::Plus).map(Left)
      }
      TokenVariant::LessEq => {
        self.get_token()?;
        self.parse_binop(lhs, BinOp::LessEq).map(Left)
      }
      _ => Ok(Left(lhs)),
    }
  }

  fn parse_expr_or_null(&mut self) -> ParserResult<Expression> {
    match self.maybe_parse_expr()? {
      Left(expr) => Ok(expr),
      Right(tok) => if Self::end_of_expr(&tok).is_some() {
        Ok(Spanned::new(
          ExpressionVariant::UnitLiteral,
          tok.start,
          tok.end,
        ))
      } else {
        unexpected_token!(tok.thing, Expr, tok.start, tok.end)
      },
    }
  }

  fn parse_expr(&mut self) -> ParserResult<Expression> {
    match self.maybe_parse_expr()? {
      Left(expr) => Ok(expr),
      Right(tok) => {
        unexpected_token!(tok.thing, Expr, tok.start, tok.end)
      }
    }
  }

  fn parse_expr_or_stmt(
    &mut self,
  ) -> ParserResult<Either<Expression, Statement>> {
    if let TokenVariant::KeywordLet = **self.peek_token()? {
      let start = self.get_token()?.start;
      let name = match self.get_token()? {
        Token {
          thing: TokenVariant::Ident(name),
          ..
        } => name,
        t => {
          return unexpected_token!(
            t.thing,
            Ident,
            t.start,
            t.end
          );
        }
      };
      let ty = match maybe_eat_token!(self, Colon) {
        Some(_) => Some(self.parse_type()?),
        None => None,
      };
      eat_token!(self, Equals);
      let initializer = self.parse_expr()?;
      let end = eat_token!(self, Semicolon).end;

      return Ok(Right(Spanned::new(
        StatementVariant::Local {
          name,
          ty,
          initializer,
        },
        start,
        end,
      )));
    }
    let expr = self.parse_expr_or_null()?;

    if let TokenVariant::CloseBrace = **self.peek_token()? {
      return Ok(Left(expr));
    }

    let end = eat_token!(self, Semicolon).end;
    let start = expr.start;
    Ok(Right(
      Spanned::new(StatementVariant::Expr(expr), start, end),
    ))
  }

  fn parse_param_list(
    &mut self,
  ) -> ParserResult<Spanned<Vec<(String, StringlyType)>>> {
    let open = eat_token!(self, OpenParen);

    let mut params = vec![];
    loop {
      let tok = self.get_token()?;
      match tok.thing {
        TokenVariant::Ident(name) => {
          eat_token!(self, Colon);
          let ty = self.parse_type()?;
          params.push((name, ty));
          if let None = maybe_eat_token!(self, Comma) {
            let end = eat_token!(self, CloseParen).end;
            return Ok(Spanned::new(params, open.start, end));
          }
        }
        TokenVariant::CloseParen => {
          return Ok(Spanned::new(params, open.start, tok.end));
        }
        _ => {
          return unexpected_token!(
            tok.thing,
            Parameter,
            tok.start,
            tok.end,
          );
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
        Left(e) => {
          expr = e;
          break;
        }
        Right(s) => statements.push(s),
      }
    }
    let sp_end = eat_token!(self, CloseBrace);
    let thing = Block_ { statements, expr };
    Ok(Spanned::new(thing, sp_start.start, sp_end.end))
  }

  fn parse_item_definition(
    &mut self,
  ) -> ParserResult<(String, Item)> {
    eat_token!(self, KeywordFunc);
    let Spanned { thing, start, end } = self.get_token()?;
    match thing {
      TokenVariant::Ident(name) => {
        let params = self.parse_param_list()?;
        let ret_ty = {
          if let Some(_) = maybe_eat_token!(self, Colon) {
            self.parse_type()?
          } else {
            StringlyType::Unit
          }
        };
        let blk = self.parse_block()?;
        let thing = ItemVariant::Function(FunctionValue {
          params: params.thing,
          ret_ty,
          blk: blk.thing,
        });
        Ok((name, Spanned::new(thing, start, blk.end)))
      }
      tok => unexpected_token!(tok, Ident, start, end),
    }
  }

  pub fn next_item(&mut self) -> ParserResult<(String, Item)> {
    let item = allow_eof!(self.parse_item_definition())?;
    Ok(item)
  }
}
