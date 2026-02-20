//! Minimal parser: expression string → `ExprDef`.
//!
//! Grammar: `expr := "a" | "b" | "(" expr ")" | expr "+" expr | expr "-" expr`

use crate::error::ParseError;
use crate::ir::ExprDef;
use std::iter::Peekable;
use std::str::Chars;

/// Parse a single expression. Leading/trailing whitespace is trimmed; no trailing tokens allowed.
pub fn parse(input: &str) -> Result<ExprDef, ParseError> {
    let mut p = Parser {
        chars: input.trim().chars().peekable(),
    };
    p.parse_expr().and_then(|e| {
        if p.chars.next().is_some() {
            Err(ParseError::new("trailing input"))
        } else {
            Ok(e)
        }
    })
}

struct Parser<'a> {
    chars: Peekable<Chars<'a>>,
}

impl Parser<'_> {
    fn parse_expr(&mut self) -> Result<ExprDef, ParseError> {
        self.parse_add_sub()
    }

    fn parse_add_sub(&mut self) -> Result<ExprDef, ParseError> {
        let mut left = self.parse_primary()?;
        loop {
            self.skip_whitespace();
            match self.chars.peek().copied() {
                Some('+') => {
                    self.chars.next();
                    self.skip_whitespace();
                    let right = self.parse_primary()?;
                    left = ExprDef::Add(Box::new(left), Box::new(right));
                }
                Some('-') => {
                    self.chars.next();
                    self.skip_whitespace();
                    let right = self.parse_primary()?;
                    left = ExprDef::Sub(Box::new(left), Box::new(right));
                }
                _ => break,
            }
        }
        Ok(left)
    }

    fn parse_primary(&mut self) -> Result<ExprDef, ParseError> {
        self.skip_whitespace();
        match self.chars.peek().copied() {
            Some('(') => {
                self.chars.next();
                let e = self.parse_expr()?;
                self.skip_whitespace();
                if self.chars.next() != Some(')') {
                    return Err(ParseError::new("expected ')'"));
                }
                Ok(e)
            }
            Some('a') => {
                self.chars.next();
                Ok(ExprDef::LitA)
            }
            Some('b') => {
                self.chars.next();
                Ok(ExprDef::LitB)
            }
            Some(c) => Err(ParseError::new(format!("unexpected '{c}'"))),
            None => Err(ParseError::new("unexpected end of input")),
        }
    }

    fn skip_whitespace(&mut self) {
        while self.chars.next_if(|c| c.is_ascii_whitespace()).is_some() {}
    }
}
