extern crate ucd;
extern crate unicode_normalization;
extern crate unicode_xid;
use self::unicode_normalization::{Recompositions, UnicodeNormalization};

use parse::Spanned;
use std::str;
use std::fmt::{self, Display};

#[derive(Copy, Clone, Debug)]
struct Location {
    line: u32,
    column: u32,
}

impl Location {
    fn new() -> Self {
        Location { line: 1, column: 0 }
    }

    fn next_char(self) -> Self {
        Location {
            column: self.column + 1,
            line: self.line,
        }
    }

    fn next_line(self) -> Self {
        Location {
            column: 0,
            line: self.line + 1,
        }
    }
}

impl Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}:{})", self.line, self.column)
    }
}

impl<T> Spanned<T> {
    fn single(thing: T, start: Location) -> Self {
        use super::Span;
        let end = start.next_char();
        Spanned {
            thing,
            span: Span {
                start_line: start.line,
                start_column: start.column,
                end_line: end.line,
                end_column: end.column,
            },
        }
    }

    fn span(thing: T, start: Location, end: Location) -> Self {
        use super::Span;
        let end = end.next_char();
        Spanned {
            thing,
            span: Span {
                start_line: start.line,
                start_column: start.column,
                end_line: end.line,
                end_column: end.column,
            },
        }
    }
}


pub type LexerResult<T> = Result<T, LexerError>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LexerErrorVariant {
    IdentAfterIntLiteral,
    UnclosedComment,
    ReservedToken(&'static str),
    UnknownChar(char),
}

impl Display for LexerErrorVariant {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::LexerErrorVariant::*;
        match *self {
            IdentAfterIntLiteral => write!(
                f,
                "found ident after int literal (this is reserved for future extensions"
            ),
            UnclosedComment => write!(f, "unclosed comment"),
            ReservedToken(ref s) => write!(f, "reserved token: '{}'", s),
            UnknownChar(ref c) => write!(f, "unknown character: '{}'", c),
        }
    }
}
pub type LexerError = Spanned<LexerErrorVariant>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokenVariant {
    // Categories
	//KeywordRaw,
	//KeywordMut,
	//KeywordOwn,

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
    KeywordFunc,
    KeywordLet,
    //KeywordVal,
    Ident(String),
    Integer(u64),

    // TODO(ubsan): should be in its own, out-of-line enum
    Plus,
    Minus,
    //Star,
    //And,
    LessEq,

    // Declaration/Types/Assignment
    Colon,
    Equals,

    // Separators
    Semicolon,
    Comma,
    //Comma,
    Eof,
}
pub type Token = Spanned<TokenVariant>;


pub struct Lexer<'src> {
    src: Recompositions<str::Chars<'src>>,
    lookahead: Option<char>,
    current_loc: Location,
}

impl<'src> Lexer<'src> {
    pub fn new(src: &str) -> Lexer {
        Lexer {
            src: src.nfc(),
            lookahead: None,
            current_loc: Location::new(),
        }
    }

    #[inline]
    fn is_start_of_ident(c: char) -> bool {
        unicode_xid::UnicodeXID::is_xid_start(c) || c == '_'
    }

    #[inline]
    fn is_ident(c: char) -> bool {
        unicode_xid::UnicodeXID::is_xid_continue(c)
    }

    #[inline]
    fn is_dec_digit(c: char) -> bool {
        c >= '0' && c <= '9'
    }

    #[inline]
    fn is_whitespace(c: char) -> bool {
        ucd::Codepoint::is_whitespace(c)
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
                Some((c, _)) if Self::is_whitespace(c) => {
                    self.getc();
                }
                _ => break,
            }
        }
    }

    fn block_comment(&mut self, loc: Location) -> LexerResult<()> {
        let unclosed_err = Err(Spanned::single(LexerErrorVariant::UnclosedComment, loc));
        loop {
            let c = self.getc();
            if let Some(('*', _)) = c {
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

    // TODO(ubsan): switch to a more modular thing that
    // follows the lexer files more closely
    pub fn next_token(&mut self) -> LexerResult<Token> {
        self.eat_whitespace();
        let (first, loc) = match self.getc() {
            Some(c) => c,
            None => {
                return Ok(Spanned::single(TokenVariant::Eof, self.current_loc));
            }
        };
        match first {
            '(' => Ok(Spanned::single(TokenVariant::OpenParen, loc)),
            ')' => Ok(Spanned::single(TokenVariant::CloseParen, loc)),
            '{' => Ok(Spanned::single(TokenVariant::OpenBrace, loc)),
            '}' => Ok(Spanned::single(TokenVariant::CloseBrace, loc)),
            ';' => Ok(Spanned::single(TokenVariant::Semicolon, loc)),
            ':' => match self.peekc() {
                Some((':', end_loc)) => {
                    self.getc();
                    Err(Spanned::span(
                        LexerErrorVariant::ReservedToken("::"),
                        loc,
                        end_loc,
                    ))
                }
                Some(('=', end_loc)) => {
                    self.getc();
                    Err(Spanned::span(
                        LexerErrorVariant::ReservedToken(":="),
                        loc,
                        end_loc,
                    ))
                }
                _ => Ok(Spanned::single(TokenVariant::Colon, loc)),
            },
            ',' => Ok(Spanned::single(TokenVariant::Comma, loc)),
            '&' => match self.peekc() {
                Some(('&', end_loc)) => Err(Spanned::span(
                    LexerErrorVariant::ReservedToken("&&"),
                    loc,
                    end_loc,
                )),
                Some(('=', end_loc)) => Err(Spanned::span(
                    LexerErrorVariant::ReservedToken("&="),
                    loc,
                    end_loc,
                )),
                _ => Err(Spanned::single(LexerErrorVariant::ReservedToken("&"), loc)),
            },
            '+' => {
                match self.peekc() {
                    // eventually, concat operator
                    Some(('+', end_loc)) => Err(Spanned::span(
                        LexerErrorVariant::ReservedToken("++"),
                        loc,
                        end_loc,
                    )),
                    Some(('=', end_loc)) => Err(Spanned::span(
                        LexerErrorVariant::ReservedToken("+="),
                        loc,
                        end_loc,
                    )),
                    _ => Ok(Spanned::single(TokenVariant::Plus, loc)),
                }
            }
            '-' => match self.peekc() {
                Some(('>', end_loc)) => {
                    self.getc();
                    Err(Spanned::span(
                        LexerErrorVariant::ReservedToken("->"),
                        loc,
                        end_loc,
                    ))
                }
                Some(('=', end_loc)) => {
                    self.getc();
                    Err(Spanned::span(
                        LexerErrorVariant::ReservedToken("-="),
                        loc,
                        end_loc,
                    ))
                }
                _ => Ok(Spanned::single(TokenVariant::Minus, loc)),
            },
            '*' => match self.peekc() {
                Some(('=', end_loc)) => Err(Spanned::span(
                    LexerErrorVariant::ReservedToken("*="),
                    loc,
                    end_loc,
                )),
                _ => Err(Spanned::single(LexerErrorVariant::ReservedToken("*"), loc)),
            },
            '/' => match self.peekc() {
                Some(('*', _)) => {
                    self.getc();
                    self.block_comment(loc)?;
                    self.next_token()
                }
                Some(('/', _)) => {
                    self.getc();
                    self.line_comment();
                    self.next_token()
                }
                _ => Err(Spanned::single(LexerErrorVariant::ReservedToken("/"), loc)),
            },

            '<' => match self.peekc() {
                Some(('=', end_loc)) => {
                    self.getc();
                    Ok(Spanned::span(TokenVariant::LessEq, loc, end_loc))
                }
                _ => Err(Spanned::single(LexerErrorVariant::ReservedToken("<"), loc)),
            },
            '=' => match self.peekc() {
                Some(('=', end_loc)) => {
                    self.getc();
                    Err(Spanned::span(
                        LexerErrorVariant::ReservedToken("=="),
                        loc,
                        end_loc,
                    ))
                }
                _ => Ok(Spanned::single(TokenVariant::Equals, loc)),
            },
            c if Self::is_start_of_ident(c) => {
                // ident
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
                let err = |tok| {
                    Err(Spanned::span(
                        LexerErrorVariant::ReservedToken(tok),
                        loc,
                        end_loc,
                    ))
                };
                // keyword
                let tok = if ident == "let" {
                    TokenVariant::KeywordLet
                } else if ident == "func" {
                    TokenVariant::KeywordFunc
                } else if ident == "true" {
                    TokenVariant::KeywordTrue
                } else if ident == "false" {
                    TokenVariant::KeywordFalse
                } else if ident == "if" {
                    TokenVariant::KeywordIf
                } else if ident == "else" {
                    TokenVariant::KeywordElse
                } else if ident == "val" {
                    return err("val");
                } else if ident == "type" {
                    return err("type");
                } else if ident == "data" {
                    return err("data");
                } else if ident == "raw" {
                    return err("raw");
                } else if ident == "mut" {
                    return err("mut");
                } else if ident == "own" {
                    return err("own");
                } else {
                    TokenVariant::Ident(ident)
                };

                Ok(Spanned::span(tok, loc, end_loc))
            }
            c if Self::is_dec_digit(c) => {
                // number-literal
                // TODO(ubsan): support non-decimal integer literals
                let mut string = String::new();
                string.push(c);
                let mut end_loc = loc;
                loop {
                    if let Some((' ', _)) = self.peekc() {
                        self.getc();
                    }
                    if let Some((c, loc)) = self.peekc() {
                        if Self::is_dec_digit(c) {
                            self.getc();
                            string.push(c);
                            end_loc = loc;
                        } else if Self::is_start_of_ident(c) {
                            return Err(Spanned::single(
                                LexerErrorVariant::IdentAfterIntLiteral,
                                loc,
                            ));
                        } else {
                            break;
                        }
                    } else {
                        break;
                    }
                }
                let value = string
                    .parse::<u64>()
                    .expect("we pushed something which wasn't 0...9 onto a string");

                Ok(Spanned::span(TokenVariant::Integer(value), loc, end_loc))
            }

            ch => Err(Spanned::single(LexerErrorVariant::UnknownChar(ch), loc)),
        }
    }
}
