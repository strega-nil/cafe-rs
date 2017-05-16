use std::str;
use parse::{Location, Spanned};

pub type LexResult<T> = Result<T, LexerError>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LexerErrorVariant {
  IdentAfterIntLiteral,
  UnclosedComment,
  UnknownToken(&'static str),
  UnknownChar(char),
}
pub type LexerError = Spanned<LexerErrorVariant>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokenVariant {
  // Item
  KeywordFn,

  // Braces
  OpenBrace,
  CloseBrace,
  OpenParen,
  CloseParen,

  // Expression
  KeywordTrue,
  KeywordFalse,
  KeywordIf,
  KeywordElse,
  Ident(String),
  Integer(u64),

  Unop(Unop),
  Binop(Binop),

  // Declaration/Types/Assignment
  Colon,
  ColonColon,
  ColonEquals,
  Equals,
  SkinnyArrow,

  // Separators
  Semicolon,
  Comma,

  Eof,
}
pub type Token = Spanned<TokenVariant>;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Binop {
  Plus,
  LessThanEquals,
}
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Unop {
  Minus,
}

impl Binop {
  pub fn precedence(&self) -> u8 {
    match *self {
      Binop::Plus => 8,
      Binop::LessThanEquals => 3,
    }
  }
}

impl Location {
  fn new() -> Self {
    Location {
      line: 1,
      column: 1,
    }
  }
}

pub struct Lexer<'src> {
  src: str::Chars<'src>,
  lookahead: Option<char>,
  current_loc: Location,
}

impl<'src> Lexer<'src> {
  pub fn new(src: &str) -> Lexer {
    Lexer {
      src: src.chars(),
      lookahead: None,
      current_loc: Location::new(),
    }
  }

  #[inline]
  fn is_start_of_ident(c: char) -> bool {
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_'
  }

  #[inline]
  fn is_ident(c: char) -> bool {
    Self::is_start_of_ident(c) || Self::is_digit(c)
  }

  #[inline]
  fn is_digit(c: char) -> bool {
    c >= '0' && c <= '9'
  }

  #[inline]
  fn is_whitespace(c: char) -> bool {
    c == '\t' || c == '\n' || c == '\r' || c == ' '
  }

  fn getc(&mut self) -> Option<(char, Location)> {
    if let Some(ret) = self.peekc() {
      self.lookahead.take();
      self.current_loc = ret.1;
      Some(ret)
    } else {
      None
    }
  }

  fn peekc(&mut self) -> Option<(char, Location)> {
    if let Some(ch) = self.lookahead {
      if ch == '\n' {
        Some((ch, self.current_loc.next_line()))
      } else {
        Some((ch, self.current_loc.next_char()))
      }
    } else if let Some(ch) = self.src.next() {
      self.lookahead = Some(ch);
      if ch == '\n' {
        Some((ch, self.current_loc.next_line()))
      } else {
        Some((ch, self.current_loc.next_char()))
      }
    } else {
      None
    }
  }

  fn eat_whitespace(&mut self) {
    loop {
      match self.peekc() {
        Some((c, _)) if Self::is_whitespace(c) => { self.getc(); },
        _ => break,
      }
    }
  }

  fn block_comment(&mut self, loc: Location) -> LexResult<()> {
    let unclosed_err = Err(Spanned {
      thing: LexerErrorVariant::UnclosedComment,
      start: loc,
      end: None,
    });
    loop {
      let c = self.getc();
      if let Some(('*', loc)) = c {
        let c = self.getc();
        if let Some(('/', _)) = c {
          return Ok(());
        } else if let None = c {
          return unclosed_err;
        }
      } else if let Some(('/', loc)) = c {
        let c = self.getc();
        if let Some(('c', _)) = c {
          self.block_comment(loc)?
        } else if let None = c {
          return unclosed_err;
        }
      } else if let None = c {
        return unclosed_err;
      }
    }
  }

  fn line_comment(&mut self) {
    loop {
      match self.getc() {
        Some(('\n', _)) => {
          break;
        }
        None => break,
        Some(_) => {}
      }
    }
  }

  pub fn next_token(&mut self) -> LexResult<Token> {
    self.eat_whitespace();
    let (first, loc) = match self.getc() {
      Some(c) => c,
      None => return Ok(span!(TokenVariant::Eof, self.current_loc)),
    };
    match first {
      '(' => Ok(span!(TokenVariant::OpenParen, loc)),
      ')' => Ok(span!(TokenVariant::CloseParen, loc)),
      '{' => Ok(span!(TokenVariant::OpenBrace, loc)),
      '}' => Ok(span!(TokenVariant::CloseBrace, loc)),
      ';' => Ok(span!(TokenVariant::Semicolon, loc)),
      ':' => match self.peekc() {
        Some((':', end_loc)) => {
          self.getc();
          Ok(span!(TokenVariant::ColonColon, loc, end_loc))
        },
        Some(('=', end_loc)) => {
          self.getc();
          Ok(span!(TokenVariant::ColonEquals, loc, end_loc))
        },
        _ => Ok(span!(TokenVariant::Colon, loc))
      },
      ',' => Ok(span!(TokenVariant::Comma, loc)),
      '+' => Ok(span!(TokenVariant::Binop(Binop::Plus), loc)),
      '-' => match self.peekc() {
        Some(('>', end_loc)) => {
          self.getc();
          Ok(span!(TokenVariant::SkinnyArrow, loc, end_loc))
        },
        _ => Err(span!(LexerErrorVariant::UnknownToken("-"), loc)),
      },
      '/' => match self.peekc() {
        Some(('*', _)) => {
          self.getc();
          self.block_comment(loc)?;
          self.next_token()
        },
        Some(('/', _)) => {
          self.getc();
          self.line_comment();
          self.next_token()
        },
        _ => Err(span!(LexerErrorVariant::UnknownToken("/"), loc)),
      },

      '<' => match self.peekc() {
        Some(('=', end_loc)) => {
          self.getc();
          Ok(span!(TokenVariant::Binop(Binop::LessThanEquals), loc, end_loc))
        },
        _ => Err(span!(LexerErrorVariant::UnknownToken("<"), loc)),
      },
      '=' => {
        match self.peekc() {
          Some(('=', end_loc)) => {
            self.getc();
            Err(span!(LexerErrorVariant::UnknownToken("=="), loc, end_loc))
          },
          _ => Ok(span!(TokenVariant::Equals, loc, loc)),
        }
      },
      c if Self::is_start_of_ident(c) => {
        let mut end_loc = loc;
        let mut ident = String::new();
        ident.push(c);
        loop {
          if let Some((c, loc)) = self.peekc() {
            if Self::is_ident(c) {
              self.getc();
              ident.push(c);
              end_loc = loc;
            } else {
              break;
            }
          } else {
            break;
          }
        }
        let tok = if ident == "fn" {
          TokenVariant::KeywordFn
        } else if ident == "if" {
          TokenVariant::KeywordIf
        } else if ident == "else" {
          TokenVariant::KeywordElse
        } else if ident == "true" {
          TokenVariant::KeywordTrue
        } else if ident == "false" {
          TokenVariant::KeywordFalse
        } else {
          TokenVariant::Ident(ident)
        };

        Ok(span!(tok, loc, end_loc))
      },
      c if Self::is_digit(c) => {
        // TODO(ubsan): support non-decimal integer literals
        let mut string = String::new();
        string.push(c);
        let mut end_loc = loc;
        loop {
          self.eat_whitespace();
          if let Some((c, loc)) = self.peekc() {
            if Self::is_digit(c) {
              self.getc();
              string.push(c);
              end_loc = loc;
            } else if Self::is_start_of_ident(c) {
              return Err(span!(LexerErrorVariant::IdentAfterIntLiteral, loc));
            } else {
              break;
            }
          } else {
            break;
          }
        }
        let value = string.parse::<u64>().expect(
          "we pushed something which wasn't 0...9 onto a string"
        );

        Ok(span!(TokenVariant::Integer(value), loc, end_loc))
      },

      ch => Err(span!(LexerErrorVariant::UnknownChar(ch), loc)),
    }
  }
}
