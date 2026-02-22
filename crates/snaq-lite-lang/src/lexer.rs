//! Custom lexer: produces Ident or FuncIdent (identifier followed by "(") so the grammar
//! can distinguish sin(1) from sin as a symbol.

use ordered_float::OrderedFloat;
use std::str::FromStr;

pub type Spanned<Tok, Loc, Error> = Result<(Loc, Tok, Loc), Error>;

#[derive(Clone, Debug, PartialEq)]
pub enum Tok {
    Num(OrderedFloat<f64>),
    Ident(String),
    /// Identifier that is immediately followed by "(" (function call).
    FuncIdent(String),
    LParen,
    RParen,
    Plus,
    Minus,
    Star,
    Slash,
    Per,
    /// "as" keyword for unit conversion (e.g. "10 km as m").
    As,
    Pi,
    Comma,
    Colon,
    /// Vector literal start: `[`
    LBracket,
    /// Vector literal end: `]`
    RBracket,
}

#[derive(Clone, Debug)]
pub enum LexicalError {
    InvalidFloat(String),
}

impl std::fmt::Display for LexicalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LexicalError::InvalidFloat(s) => write!(f, "invalid float: {s}"),
        }
    }
}

impl std::error::Error for LexicalError {}

pub struct Lexer<'input> {
    input: &'input str,
    pos: usize,
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input str) -> Self {
        Lexer { input, pos: 0 }
    }

    fn skip_whitespace(&mut self) {
        let rest = &self.input[self.pos..];
        let skipped = rest
            .bytes()
            .take_while(|b| b" \t\n\r".contains(b))
            .count();
        self.pos += skipped;
    }

    fn peek_next_non_space(&self) -> Option<char> {
        let rest = &self.input[self.pos..];
        rest.chars().find(|c| !c.is_whitespace())
    }

    fn take_ident(&mut self) -> Option<String> {
        let rest = &self.input[self.pos..];
        let mut end = 0;
        for (i, c) in rest.char_indices() {
            if i == 0 {
                if c.is_alphabetic() || c == '_' {
                    end = i + c.len_utf8();
                } else {
                    return None;
                }
            } else if c.is_alphanumeric() || c == '_' {
                end = i + c.len_utf8();
            } else {
                break;
            }
        }
        if end > 0 {
            let s = rest[..end].to_string();
            self.pos += end;
            Some(s)
        } else {
            None
        }
    }

    fn take_num(&mut self) -> Option<Result<OrderedFloat<f64>, LexicalError>> {
        let rest = &self.input[self.pos..];
        let mut end = 0;
        let bytes = rest.as_bytes();
        let n = bytes.len();
        // [0-9]+\.?[0-9]* or [0-9]*\.[0-9]+
        if end < n && bytes[end].is_ascii_digit() {
            while end < n && bytes[end].is_ascii_digit() {
                end += 1;
            }
            if end < n && bytes[end] == b'.' {
                end += 1;
                while end < n && bytes[end].is_ascii_digit() {
                    end += 1;
                }
            }
        } else if end < n && bytes[end] == b'.' && end + 1 < n && bytes[end + 1].is_ascii_digit() {
            end += 1;
            while end < n && bytes[end].is_ascii_digit() {
                end += 1;
            }
        } else {
            return None;
        }
        // Optional exponent
        if end < n && (bytes[end] == b'e' || bytes[end] == b'E') {
            let exp_start = end;
            end += 1;
            if end < n && (bytes[end] == b'+' || bytes[end] == b'-') {
                end += 1;
            }
            if end < n && bytes[end].is_ascii_digit() {
                while end < n && bytes[end].is_ascii_digit() {
                    end += 1;
                }
            } else {
                end = exp_start; // no exponent, rewind
            }
        }
        let s = &rest[..end];
        self.pos += end;
        match f64::from_str(s) {
            Ok(v) => Some(Ok(OrderedFloat::from(v))),
            Err(_) => Some(Err(LexicalError::InvalidFloat(s.to_string()))),
        }
    }
}

impl<'input> Iterator for Lexer<'input> {
    type Item = Spanned<Tok, usize, LexicalError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.skip_whitespace();
        if self.pos >= self.input.len() {
            return None;
        }
        let start = self.pos;
        let rest = &self.input[self.pos..];

        // Single chars / fixed strings (longer first); "as" before "per" so "aspect" stays Ident
        if rest.starts_with("as") && !rest[2..].chars().next().is_some_and(|c| c.is_alphanumeric() || c == '_') {
            self.pos += 2;
            return Some(Ok((start, Tok::As, self.pos)));
        }
        if rest.starts_with("per") && !rest[3..].chars().next().is_some_and(|c| c.is_alphanumeric() || c == '_') {
            self.pos += 3;
            return Some(Ok((start, Tok::Per, self.pos)));
        }
        if rest.starts_with("π") {
            self.pos += "π".len();
            return Some(Ok((start, Tok::Pi, self.pos)));
        }

        let mut it = rest.chars();
        let c = it.next()?;
        self.pos += c.len_utf8();

        let tok = match c {
            '(' => Tok::LParen,
            ')' => Tok::RParen,
            '[' => Tok::LBracket,
            ']' => Tok::RBracket,
            '+' => Tok::Plus,
            '-' => Tok::Minus,
            '*' => Tok::Star,
            '/' => Tok::Slash,
            ',' => Tok::Comma,
            ':' => Tok::Colon,
            'a'..='z' | 'A'..='Z' | '_' => {
                self.pos -= c.len_utf8(); // put back
                if let Some(s) = self.take_ident() {
                    let next_non_space = self.peek_next_non_space();
                    if next_non_space == Some('(') {
                        Tok::FuncIdent(s)
                    } else {
                        Tok::Ident(s)
                    }
                } else {
                    return None;
                }
            }
            '0'..='9' | '.' => {
                self.pos -= c.len_utf8();
                match self.take_num()? {
                    Ok(n) => Tok::Num(n),
                    Err(e) => return Some(Err(e)),
                }
            }
            _ => {
                return Some(Err(LexicalError::InvalidFloat(
                    rest.chars().take(5).collect::<String>(),
                )));
            }
        };
        let end = self.pos;
        Some(Ok((start, tok, end)))
    }
}

