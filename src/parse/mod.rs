mod lexer;

use self::lexer::{Lexer, Token, TokenVariant, LexerError, LexerErrorVariant};

use std::str;

use ty::{self, Type, TypeContext};
use Either::{self, Left, Right};

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
pub enum ParserErrorVariant {
  ExpectedEof, // not an error

  LexerError(LexerErrorVariant),
  UnknownType {
    found: String,
  },
  DuplicatedFunctionParameter {
    parameter: String,
    function: String,
  },
  DuplicatedFunction {
    function: String,
  },
  UnexpectedToken {
    found: Token,
    expected: (), // TODO(ubsan): figure out what this should be
  },
  ExpectedSemicolon,
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

  /*
  pub fn item<'t>(
    &mut self, ctxt: &'t TypeContext<'t>
  ) -> ParserResult<ast::Item<'t>> {
    match self.get_token()? {
      Token::KeywordFn => self.function(ctxt),
      Token::Eof => Err(ParserError::ExpectedEof),
      tok => Err(ParserError::UnexpectedToken {
        found: tok,
        expected: TokenType::Item,
        line: self.line(),
        compiler: fl!(),
      }),
    }
  }

  fn maybe_peek_ty(
    &mut self, expected: &TokenType
  ) -> ParserResult<Option<Token>> {
    let token = self.peek_token()?;
    match *expected {
      TokenType::Specific(ref t) => if token == *t {
        return Ok(Some(token))
      },
      TokenType::AnyOf(ref t) => if t.contains(&token) {
        return Ok(Some(token))
      },
      ref tt => if token.ty() == *tt {
        return Ok(Some(token))
      },
    }
    Ok(None)
  }

  fn peek_ty(
    &mut self, expected: TokenType, line: u32
  ) -> ParserResult<Token> {
    match self.maybe_peek_ty(&expected) {
      Ok(Some(t)) => return Ok(t),
      Err(e) => return Err(e),
      _ => {},
    }
    Err(ParserError::UnexpectedToken {
      found: self.get_token()?,
      expected: expected,
      line: self.line(),
      compiler: fl!(line),
    })
  }

  fn maybe_eat_ty(
    &mut self, expected: &TokenType
  ) -> ParserResult<Option<Token>> {
    match self.maybe_peek_ty(expected)? {
      Some(_) => self.get_token().map(|t| Some(t)),
      None => Ok(None),
    }
  }

  fn eat_ty(
    &mut self, expected: TokenType, compiler_line: u32
  ) -> ParserResult<Token> {
    match self.maybe_eat_ty(&expected) {
      Ok(Some(t)) => return Ok(t),
      Err(e) => return Err(e),
      _ => {},
    }
    Err(ParserError::UnexpectedToken {
      found: self.get_token()?,
      expected: expected,
      line: self.line(),
      compiler: fl!(compiler_line),
    })
  }


  fn maybe_eat(&mut self, expected: Token) -> ParserResult<Option<Token>> {
    self.maybe_eat_ty(&TokenType::Specific(expected))
  }

  fn eat(&mut self, expected: Token, line: u32) -> ParserResult<Token> {
    self.eat_ty(TokenType::Specific(expected), line)
  }

  fn maybe_peek(&mut self, expected: Token) -> ParserResult<Option<Token>> {
    self.maybe_peek_ty(&TokenType::Specific(expected))
  }

  #[allow(dead_code)]
  fn peek(&mut self, expected: Token, line: u32) -> ParserResult<Token> {
    self.peek_ty(TokenType::Specific(expected), line)
  }

  fn parse_ident(&mut self, line: u32) -> ParserResult<String> {
    match self.get_token()? {
      Token::Ident(s) => Ok(s),
      tok => Err(ParserError::UnexpectedToken {
        found: tok,
        expected: TokenType::Specific(Token::Ident(String::new())),
        line: self.line(),
        compiler: fl!(line),
      }),
    }
  }

  fn parse_ty<'t>(
    &mut self, ctxt: &'t TypeContext<'t>, line: u32
  ) -> ParserResult<Type<'t>> {
    match self.get_token()? {
      Token::Ident(s) => match &*s {
        "s8" => Ok(Type::sint(ty::Int::I8, ctxt)),
        "s16" => Ok(Type::sint(ty::Int::I16, ctxt)),
        "s32" => Ok(Type::sint(ty::Int::I32, ctxt)),
        "s64" => Ok(Type::sint(ty::Int::I64, ctxt)),
        "u8" => Ok(Type::uint(ty::Int::I8, ctxt)),
        "u16" => Ok(Type::uint(ty::Int::I16, ctxt)),
        "u32" => Ok(Type::uint(ty::Int::I32, ctxt)),
        "u64" => Ok(Type::uint(ty::Int::I64, ctxt)),
        "bool" => Ok(Type::bool(ctxt)),
        s => Err(ParserError::UnknownType {
          found: s.to_owned(),
          line: line,
          compiler: fl!(),
        }),
      },
      Token::OpenParen => {
        self.eat(Token::CloseParen, line!())?;
        Ok(Type::unit(ctxt))
      },
      Token::Operand(Operand::And) => {
        let inner = self.parse_ty(ctxt, line)?;
        Ok(Type::ref_(inner, ctxt))
      },
      Token::Operand(Operand::AndAnd) => {
        let inner = self.parse_ty(ctxt, line)?;
        Ok(Type::ref_(Type::ref_(inner, ctxt), ctxt))
      },
      tok => Err(ParserError::UnexpectedToken {
        found: tok,
        expected: TokenType::AnyOf(
          vec![Token::Ident(String::new()), Token::OpenParen]
        ),
        line: self.line(),
        compiler: fl!(line),
      }),
    }
  }

  fn maybe_parse_single_expr<'t>(
    &mut self, ctxt: &'t TypeContext<'t>
  ) -> ParserResult<Option<Expr<'t>>> {
    let ret = match self.get_token()? {
      Token::Ident(name) => {
        if let Some(_) = self.maybe_eat(Token::OpenParen)? {
          let mut args = Vec::new();
          if let Some(e) = self.maybe_parse_expr(ctxt)? {
            args.push(e);
            while let Some(_) = self.maybe_eat(Token::Comma)? {
              args.push(self.parse_expr(ctxt, line!())?);
            }
          }
          self.eat(Token::CloseParen, line!())?;
          if name == "log" {
            assert!(args.len() == 1);
            Some(Expr::log(args.remove(0), ctxt))
          } else {
            Some(Expr::call(name, args, ctxt))
          }
        } else {
          Some(Expr::var(name, ctxt))
        }
      }
      Token::KeywordIf => {
        let condition = self.parse_expr(ctxt, line!())?;
        let if_value = self.parse_block(ctxt)?;
        let else_value = {
          if let Some(_) = self.maybe_eat(Token::KeywordElse)? {
            match {
              self.peek_ty(
                TokenType::AnyOf(
                  vec![Token::OpenBrace, Token::KeywordIf]
                ),
                line!(),
                )?
            } {
              Token::OpenBrace => self.parse_block(ctxt)?,
              Token::KeywordIf => self.parse_block(ctxt)?,
              tok => unreachable!("{:?}", tok),
            }
          } else {
            ast::Block::expr(Expr::unit_lit(ctxt))
          }
        };
        Some(Expr::if_else(condition, if_value, else_value, ctxt))
      },
      Token::OpenBrace => {
        self.unget_token(Token::OpenBrace);
        Some(Expr::block(self.parse_block(ctxt)?, ctxt))
      }

      Token::Integer { value, suffix } => {
        if suffix == "" {
          return Ok(Some(Expr::int_lit(value, ctxt)));
        }
        let ty = match &*suffix {
          "" => return Ok(Some(Expr::int_lit(value, ctxt))),
          "s8" => Type::sint(ty::Int::I8, ctxt),
          "s16" => Type::sint(ty::Int::I16, ctxt),
          "s32" => Type::sint(ty::Int::I32, ctxt),
          "s64" => Type::sint(ty::Int::I64, ctxt),
          "u8" => Type::uint(ty::Int::I8, ctxt),
          "u16" => Type::uint(ty::Int::I16, ctxt),
          "u32" => Type::uint(ty::Int::I32, ctxt),
          "u64" => Type::uint(ty::Int::I64, ctxt),
          _ => return Err(ParserError::InvalidSuffix {
            suffix: suffix.clone(),
            line: self.line(),
            compiler: fl!(),
          })
        };
        Some(Expr::int_lit_with_ty(value, ty))
      }
      Token::OpenParen => {
        if let Some(_) = self.maybe_eat(Token::CloseParen)? {
          Some(Expr::unit_lit(ctxt))
        } else {
          let inner = self.parse_single_expr(ctxt, line!())?;
          self.eat(Token::CloseParen, line!())?;
          Some(inner)
        }
      }
      Token::Operand(Operand::Minus) => {
        let inner = self.parse_single_expr(ctxt, line!())?;
        Some(Expr::neg(inner, ctxt))
      }
      Token::Operand(Operand::Plus) => {
        let inner = self.parse_single_expr(ctxt, line!())?;
        Some(Expr::pos(inner, ctxt))
      }
      Token::Operand(Operand::Not) => {
        let inner = self.parse_single_expr(ctxt, line!())?;
        Some(Expr::not(inner, ctxt))
      }
      Token::Operand(Operand::And) => {
        unimplemented!()
      }
      Token::Operand(Operand::AndAnd) => {
        unimplemented!()
      }
      Token::Operand(Operand::Mul) => {
        unimplemented!()
      }
      Token::KeywordTrue => Some(Expr::bool_lit(true, ctxt)),
      Token::KeywordFalse => Some(Expr::bool_lit(false, ctxt)),
      Token::KeywordReturn => {
        let expr = if let Some(e) = self.maybe_parse_expr(ctxt)? {
          e
        } else {
          Expr::unit_lit(ctxt)
        };
        Some(Expr::ret(expr, ctxt))
      },
      tok => {
        self.unget_token(tok);
        None
      }
    };
    if let Some(ret) = ret {
      match self.maybe_eat(Token::Dot)? {
        Some(_) => if let Token::Integer { value, suffix } = self.get_token()? {
          if suffix != "" {
            Err(ParserError::NoSuffixOnTupleIndex {
              suffix: suffix,
              line: self.line(),
              compiler: fl!(),
            })
          } else if value > (u16::max_value() as u64) {
            Err(ParserError::TupleIndexTooLarge {
              value: value,
              line: self.line(),
              compiler: fl!(),
            })
          } else {
            Ok(Some(Expr::field_access(ret, value as u16, ctxt)))
          }
        } else {
          Err(ParserError::TupleIndexMustBeInt {
            line: self.line(),
            compiler: fl!(),
          })
        },
        None => Ok(Some(ret)),
      }
    } else {
      Ok(None)
    }
  }

  fn parse_single_expr<'t>(
    &mut self, ctxt: &'t TypeContext<'t>, line: u32
  ) -> ParserResult<Expr<'t>> {
    match self.maybe_parse_single_expr(ctxt) {
      Ok(Some(e)) => Ok(e),
      Ok(None) => Err(ParserError::UnexpectedToken {
        found: self.get_token()?,
        expected: TokenType::Expression,
        line: self.line(),
        compiler: fl!(line),
      }),
      Err(e) => Err(e),
    }
  }

  fn maybe_parse_expr<'t>(
    &mut self, ctxt: &'t TypeContext<'t>
  ) -> ParserResult<Option<Expr<'t>>> {
    let lhs = match self.maybe_parse_single_expr(ctxt)? {
      Some(l) => l,
      None => return Ok(None),
    };
    match self.maybe_eat_ty(&TokenType::Operand)? {
      Some(Token::Operand(ref op)) => {
        self.parse_binop(lhs, op, ctxt).map(|e| Some(e))
      }
      Some(tok) => unreachable!("{:?}", tok),
      None => {
        if let Some(_) = self.maybe_eat(Token::Equals)? {
          let assign = Expr::assign(
            lhs, self.parse_expr(ctxt, line!())?, ctxt
          );
          Ok(Some(assign))
        } else {
          Ok(Some(lhs))
        }
      }
    }
  }

  fn parse_expr<'t>(
    &mut self, ctxt: &'t TypeContext<'t>, line: u32
  ) -> ParserResult<Expr<'t>> {
    let lhs = self.parse_single_expr(ctxt, line)?;
    match self.maybe_eat_ty(&TokenType::Operand)? {
      Some(Token::Operand(ref op)) => {
        self.parse_binop(lhs, op, ctxt)
      }
      Some(tok) => unreachable!("{:?}", tok),
      None => {
        Ok(lhs)
      }
    }
  }

  fn parse_stmt<'t>(
    &mut self, ctxt: &'t TypeContext<'t>
  ) -> ParserResult<Option<Either<Stmt<'t>, Expr<'t>>>> {
    match self.maybe_parse_expr(ctxt)? {
      Some(e) => {
        if let Some(_) = self.maybe_eat(Token::Semicolon)? {
          Ok(Some(Left(Stmt::Expr(e))))
        } else if e.is_block() {
          // if the expression is a block, treat it as an expression
          // *unless* it's the last expression in the outer block
          match self.maybe_peek(Token::CloseBrace)? {
            Some(_) => {
              Ok(Some(Right(e)))
            }
            None => {
              Ok(Some(Left(Stmt::Expr(e))))
            }
          }
        } else {
          Ok(Some(Right(e)))
        }
      }
      None => {
        match self.eat_ty(TokenType::Statement, line!())? {
          Token::KeywordLet => {
            let name = self.parse_ident(line!())?;
            let ty = if let
            Some(_) = self.maybe_eat(Token::Colon)?
            {
              self.parse_ty(ctxt, line!())?
            } else {
              Type::infer(ctxt)
            };
            let expr = if let
            Some(_) = self.maybe_eat(Token::Equals)?
            {
              Some(Box::new(self.parse_expr(ctxt, line!())?))
            } else {
              None
            };
            self.eat(Token::Semicolon, line!())?;
            Ok(Some(Left(Stmt::Let {
              name: name,
              ty: ty,
              value: expr,
            })))
          }
          Token::CloseBrace => {
            self.unget_token(Token::CloseBrace);
            Ok(None)
          }
          tok => unreachable!("{:?}", tok),
        }
      }
    }
  }

  fn parse_binop<'t>(
    &mut self, lhs: Expr<'t>, left_op: &Operand, ctxt: &'t TypeContext<'t>
  ) -> ParserResult<Expr<'t>> {
    let rhs = self.parse_single_expr(ctxt, line!())?;
    match self.maybe_eat_ty(&TokenType::Operand)? {
      Some(Token::Operand(ref right_op)) => {
        if left_op.precedence() >= right_op.precedence() {
          let new_lhs = left_op.expr(lhs, rhs, ctxt);
          self.parse_binop(new_lhs, right_op, ctxt)
        } else {
          let new_rhs = self.parse_binop(rhs, right_op, ctxt)?;
          Ok(left_op.expr(lhs, new_rhs, ctxt))
        }
      }
      Some(tok) => unreachable!("{:?}", tok),
      None => Ok(left_op.expr(lhs, rhs, ctxt)),
    }
  }

  fn parse_block<'t>(
    &mut self, ctxt: &'t TypeContext<'t>
  ) -> ParserResult<ast::Block<'t>> {
    self.eat(Token::OpenBrace, line!())?;
    let mut body = Vec::new();
    let mut expr = None;
    while let Some(st) = self.parse_stmt(ctxt)? {
      match st {
        Left(st) => body.push(st),
        Right(e) => {
          expr = Some(e);
          if let Some(_) = self.parse_stmt(ctxt)? {
            println!("{:#?}", expr.unwrap());
            return Err(ParserError::ExpectedSemicolon {
              line: self.line(),
              compiler: fl!(),
            })
          } else {
            break;
          }
        }
      }
    }
    self.eat(Token::CloseBrace, line!())?;
    Ok(ast::Block::new(body, expr))
  }

  fn function<'t>(
    &mut self, ctxt: &'t TypeContext<'t>
  ) -> ParserResult<ast::Item<'t>> {
    let name = self.parse_ident(line!())?;

    self.eat(Token::OpenParen, line!())?;

    let mut params = Vec::new();
    match self.get_token()? {
      Token::Ident(param) => {
        self.eat(Token::Colon, line!())?;
        params.push((param, self.parse_ty(ctxt, line!())?));
        loop {
          let comma_or_close_paren = self.get_token()?;
          if let Token::Comma = comma_or_close_paren {
            let name = self.parse_ident(line!())?;
            self.eat(Token::Colon, line!())?;
            params.push((name, self.parse_ty(ctxt, line!())?));
          } else if let Token::CloseParen = comma_or_close_paren {
            break;
          } else {
            return Err(ParserError::UnexpectedToken {
              found: comma_or_close_paren,
              expected: TokenType::AnyOf(
                vec![Token::Comma, Token::CloseParen]
              ),
              line: self.line(),
              compiler: fl!(),
            });
          }
        }
      }
      Token::CloseParen => {}
      tok => {
        return Err(ParserError::UnexpectedToken {
          found: tok,
          expected: TokenType::AnyOf(
            vec![Token::Ident(String::new()), Token::CloseParen]
          ),
          line: self.line(),
          compiler: fl!(),
        });
      }
    }

    let ret_ty = match self.maybe_eat(Token::SkinnyArrow)? {
      Some(_) => {
        self.parse_ty(ctxt, line!())?
      },
      None => Type::unit(ctxt),
    };


    Ok(ast::Item::Function {
      name,
      ret: ret_ty,
      params,
      body: self.parse_block(ctxt)?,
    })
  }
  */
}
