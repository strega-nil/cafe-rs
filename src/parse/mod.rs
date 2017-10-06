pub mod lexer;

use self::lexer::{Lexer, LexerError, LexerErrorVariant, Token, TokenVariant};
use ast::{BinOp, Block, Block_, Expression, ExpressionVariant, FunctionValue, Statement,
          StatementVariant, StringlyType};

use std::ops::{Deref, DerefMut};
use std::str;
use std::fmt::{self, Display};

enum Either<T, U> {
    Left(T),
    Right(U),
}
use self::Either::{Left, Right};

#[derive(Copy, Clone, Debug)]
pub struct Span {
    pub start_line: u32,
    pub start_column: u32,
    pub end_line: u32,
    pub end_column: u32,
}

impl Span {
    fn union(self, end: Span) -> Self {
        let Span {
            start_line,
            start_column,
            ..
        } = self;
        let Span {
            end_line,
            end_column,
            ..
        } = end;
        Self {
            start_line,
            start_column,
            end_line,
            end_column,
        }
    }
}

impl Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "({}, {}), ({}, {})",
            self.start_line,
            self.start_column,
            self.end_line,
            self.end_column
        )
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Spanned<T> {
    pub thing: T,
    pub span: Span,
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

impl<T: Display> Display for Spanned<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} at {}", self.thing, self.span)
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
impl Display for ParserErrorVariant {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::ParserErrorVariant::*;
        match *self {
            ExpectedEof => write!(f, "expected end of file - not an error..."),
            LexerError(ref le) => le.fmt(f),
            UnexpectedToken {
                ref found,
                ref expected,
            } => write!(
                f,
                "unexpected token: expected {:?}, found {:?}",
                expected,
                found,
            ),
        }
    }
}
pub type ParserError = Spanned<ParserErrorVariant>;

impl From<LexerError> for ParserError {
    fn from(le: LexerError) -> Self {
        Spanned {
            thing: ParserErrorVariant::LexerError(le.thing),
            span: le.span,
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
    $span:expr
    $(,)*
  ) => ({
    let thing = ParserErrorVariant::UnexpectedToken {
      found: $tok,
      expected: ExpectedToken::$expected,
    };
    Err(Spanned { thing, span: $span })
  });
  (
    $tok:expr,
    $expected:ident
    $(,)*
  ) => ({
    unexpected_token!(
      $tok.thing,
      $expected,
      $tok.span,
    )
  });
}

macro_rules! allow_eof {
  ($tok:expr) => (
    match $tok {
      t @ Ok(_) => t,
      Err(sp) => {
        let Spanned { thing, span } = sp;
        match thing {
          ParserErrorVariant::UnexpectedToken {
            found: TokenVariant::Eof,
            ..
          } => Err(Spanned {
            thing: ParserErrorVariant::ExpectedEof,
            span,
          }),
          thing => Err(Spanned { thing, span }),
        }
      },
    }
  )
}

macro_rules! eat_token {
  ($slf:expr, $tok:ident) => ({
    match $slf.get_token()? {
      s @ Spanned { thing: TokenVariant::$tok, .. } => s,
      Spanned { thing, span } => return Err(Spanned {
        thing: ParserErrorVariant::UnexpectedToken {
          found: thing,
          expected:
            ExpectedToken::SpecificToken(
              TokenVariant::$tok,
            ),
        },
        span,
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
            TokenVariant::Semicolon => Some(Spanned {
                thing: TokenVariant::Semicolon,
                span: s.span,
            }),
            TokenVariant::CloseBrace => Some(Spanned {
                thing: TokenVariant::CloseBrace,
                span: s.span,
            }),
            TokenVariant::CloseParen => Some(Spanned {
                thing: TokenVariant::CloseParen,
                span: s.span,
            }),
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
        let Spanned { thing, span } = self.get_token()?;
        match thing {
            TokenVariant::Ident(s) => Ok(StringlyType::UserDefinedType(s)),
            //TokenVariant::And => unimplemented!(),
            //TokenVariant::Star => unimplemented!(),
            tok => unexpected_token!(tok, Type, span),
        }
    }

    fn maybe_parse_single_expr(&mut self) -> ParserResult<Either<Expression, Token>> {
        if let Some(tok) = Self::end_of_expr(self.peek_token()?) {
            return Ok(Right(tok));
        }
        let Spanned { thing, span } = self.get_token()?;

        let mut expr = match thing {
            TokenVariant::Integer(u) => Spanned {
                thing: ExpressionVariant::IntLiteral {
                    is_negative: false,
                    value: u,
                },
                span,
            },
            TokenVariant::Minus => if let &Spanned {
                thing: TokenVariant::Integer(n),
                span: end_span,
            } = self.peek_token()?
            {
                self.get_token()?;
                Spanned {
                    thing: ExpressionVariant::IntLiteral {
                        is_negative: true,
                        value: n,
                    },
                    span: span.union(end_span),
                }
            } else {
                let expr = self.parse_single_expr()?;
                Spanned {
                    thing: ExpressionVariant::Negative(Box::new(expr)),
                    span,
                }
            },
            TokenVariant::OpenParen => {
                let end = eat_token!(self, CloseParen).span;
                Spanned {
                    thing: ExpressionVariant::UnitLiteral,
                    span: span.union(end),
                }
            }
            TokenVariant::Ident(s) => Spanned {
                thing: ExpressionVariant::Variable(s),
                span,
            },
            TokenVariant::KeywordTrue => Spanned {
                thing: ExpressionVariant::BoolLiteral(true),
                span,
            },
            TokenVariant::KeywordFalse => Spanned {
                thing: ExpressionVariant::BoolLiteral(false),
                span,
            },
            TokenVariant::KeywordIf => {
                fn parse(this: &mut Parser, span: Span) -> ParserResult<Expression> {
                    let cond = this.parse_expr()?;
                    let then = this.parse_block()?;
                    eat_token!(this, KeywordElse);
                    let els = if let Some(_) = maybe_eat_token!(this, KeywordIf) {
                        let expr = parse(this, span)?;
                        let span = expr.span;
                        Spanned {
                            thing: Block_ {
                                statements: vec![],
                                expr,
                            },
                            span,
                        }
                    } else {
                        this.parse_block()?
                    };
                    let end = els.span;
                    Ok(Spanned {
                        thing: ExpressionVariant::IfElse {
                            cond: Box::new(cond),
                            then: Box::new(then),
                            els: Box::new(els),
                        },
                        span: span.union(end),
                    })
                };
                parse(self, span)?
            }
            TokenVariant::KeywordElse => {
                return unexpected_token!(TokenVariant::KeywordElse, Expr, span);
            }
            TokenVariant::OpenBrace => {
                let blk = self.parse_block_no_open(span)?;
                let end = blk.span;
                Spanned {
                    thing: ExpressionVariant::Block(Box::new(blk)),
                    span: span.union(end),
                }
            }
            tok => panic!(
                "unimplemented expression: {:?}",
                Spanned { thing: tok, span },
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
                            end = eat_token!(self, CloseParen).span;
                            break;
                        }
                    }
                    Right(tok) => if let TokenVariant::CloseParen = *tok {
                        self.get_token()?;
                        end = tok.span;
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
                    let arg = unsafe { Box::from_raw(Box::into_raw(arg) as *mut Expression) };
                    expr = Spanned {
                        thing: ExpressionVariant::Log(arg),
                        span: expr.span.union(end),
                    };
                } else {
                    expr = Spanned {
                        thing: ExpressionVariant::Call { callee, args },
                        span: expr.span.union(end),
                    };
                }
            } else {
                unimplemented!()
            }
        }

        Ok(Left(expr))
    }

    fn parse_single_expr(&mut self) -> ParserResult<Expression> {
        match self.maybe_parse_single_expr()? {
            Right(tok) => unexpected_token!(tok, Expr),
            Left(e) => Ok(e),
        }
    }

    fn parse_binop(&mut self, lhs: Expression, left_op: BinOp) -> ParserResult<Expression> {
        fn op(op: BinOp, lhs: Expression, rhs: Expression) -> Expression {
            let start = lhs.span;
            let end = rhs.span;
            let expr = ExpressionVariant::BinOp {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                op,
            };
            Spanned {
                thing: expr,
                span: start.union(end),
            }
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

    fn maybe_parse_expr(&mut self) -> ParserResult<Either<Expression, Token>> {
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

    fn parse_expr(&mut self) -> ParserResult<Expression> {
        match self.maybe_parse_expr()? {
            Left(expr) => Ok(expr),
            Right(tok) => unexpected_token!(tok, Expr),
        }
    }

    fn parse_expr_or_stmt(&mut self) -> ParserResult<Either<Expression, Statement>> {
        if let TokenVariant::KeywordLet = **self.peek_token()? {
            let start = self.get_token()?.span;
            let name = match self.get_token()? {
                Token {
                    thing: TokenVariant::Ident(name),
                    ..
                } => name,
                tok => {
                    return unexpected_token!(tok, Ident);
                }
            };
            let ty = match maybe_eat_token!(self, Colon) {
                Some(_) => Some(self.parse_type()?),
                None => None,
            };
            eat_token!(self, Equals);
            let initializer = self.parse_expr()?;
            let end = eat_token!(self, Semicolon).span;

            return Ok(Right(Spanned {
                thing: StatementVariant::Local {
                    name,
                    ty,
                    initializer,
                },
                span: start.union(end),
            }));
        }
        let expr = self.parse_expr()?;

        if let TokenVariant::CloseBrace = **self.peek_token()? {
            return Ok(Left(expr));
        }

        let end = eat_token!(self, Semicolon).span;
        let start = expr.span;
        Ok(Right(Spanned {
            thing: StatementVariant::Expr(expr),
            span: start.union(end),
        }))
    }

    fn parse_param_list(&mut self) -> ParserResult<Spanned<Vec<(String, StringlyType)>>> {
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
                        let end = eat_token!(self, CloseParen).span;
                        return Ok(Spanned {
                            thing: params,
                            span: open.span.union(end),
                        });
                    }
                }
                TokenVariant::CloseParen => {
                    return Ok(Spanned {
                        thing: params,
                        span: open.span.union(tok.span),
                    });
                }
                _ => {
                    return unexpected_token!(tok, Parameter);
                }
            }
        }
    }

    fn parse_block_no_open(&mut self, start: Span) -> ParserResult<Block> {
        let mut statements = vec![];
        let expr;

        loop {
            if let Spanned {
                thing: TokenVariant::CloseBrace,
                span,
            } = *self.peek_token()?
            {
                expr = Spanned {
                    thing: ExpressionVariant::UnitLiteral,
                    span,
                };
                break;
            }
            match self.parse_expr_or_stmt()? {
                Left(e) => {
                    expr = e;
                    break;
                }
                Right(s) => statements.push(s),
            }
        }
        let end = eat_token!(self, CloseBrace).span;
        let thing = Block_ { statements, expr };
        Ok(Spanned {
            thing,
            span: start.union(end),
        })
    }

    fn parse_block(&mut self) -> ParserResult<Block> {
        let span = eat_token!(self, OpenBrace).span;
        self.parse_block_no_open(span)
    }

    fn parse_item_definition(&mut self) -> ParserResult<(String, Item)> {
        eat_token!(self, KeywordVal);
        let Spanned { thing, span } = self.get_token()?;
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
                Ok((
                    name,
                    Spanned {
                        thing,
                        span: span.union(blk.span),
                    },
                ))
            }
            tok => unexpected_token!(tok, Ident, span),
        }
    }

    pub fn next_item(&mut self) -> ParserResult<(String, Item)> {
        let item = allow_eof!(self.parse_item_definition())?;
        Ok(item)
    }
}
