//! Custom lexer: produces Ident or FuncIdent (identifier followed by "(") so the grammar
//! can distinguish sin(1) from sin as a symbol.

use crate::ir::NumLiteral;
use ordered_float::OrderedFloat;
use std::str::FromStr;

pub type Spanned<Tok, Loc, Error> = Result<(Loc, Tok, Loc), Error>;

#[derive(Clone, Debug, PartialEq)]
pub enum Tok {
    Num(NumLiteral),
    Ident(String),
    /// Identifier that is immediately followed by "(" (function call).
    FuncIdent(String),
    /// Identifier after "." that is immediately followed by "(" (method call, e.g. V.map(...)).
    MethodIdent(String),
    LParen,
    RParen,
    Plus,
    Minus,
    Star,
    Slash,
    Per,
    /// "as" keyword for unit conversion (e.g. "10 km as m").
    As,
    /// "if" / "then" / "else" for conditional expressions.
    If,
    Then,
    Else,
    /// "input" for declarative graph node input (e.g. input revenue: ProbabilisticTensor).
    Input,
    /// `@` separator for input param id (e.g. input revenue@p1: Vector).
    At,
    Pi,
    Comma,
    Colon,
    /// Vector literal start: `[`
    LBracket,
    /// Vector literal end: `]`
    RBracket,
    /// Bracket key: content between `[` and `]` when used as index/key (e.g. m[foo bar]); trimmed.
    BracketKey(String),
    /// Property/index access: `V.0`, `V.1` (dot before integer).
    Dot,
    /// Postfix transpose: `'` (e.g. [1,2,3]')
    Apostrophe,
    /// Variable binding: `=` (e.g. x = 10). Distinct from comparison `==`.
    Assign,
    /// Lambda / function body: `=>`. Keyword: `fn` for anonymous or named function.
    Arrow,
    Fn,
    /// Comparison: `==`, `!=`, `<`, `<=`, `>`, `>=`
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    /// Explicit precision/error bound: `~` (e.g. 10 ~ 2 => value 10 with ±2 error).
    Tilde,
    /// Exponentiation: `^` (e.g. 2^10 => pow(2, 10)).
    Caret,
    /// Modulo: `%` (e.g. 7 % 3 => mod(7, 3)).
    Percent,
    /// Factorial (postfix): `!` (e.g. 5! => factorial(5)).
    Bang,
    /// Square root (prefix): `√` (U+221A) => sqrt(expr).
    SqrtPrefix,
    /// Cube root (prefix): `∛` (U+221B) => cbrt(expr).
    CbrtPrefix,
    /// Absolute value: `|` (e.g. |x| => abs(x)).
    Bar,
    /// Block start: `{`
    LBrace,
    /// Block end: `}`
    RBrace,
    /// Expression separator: `;`
    Semicolon,
    /// Newline (expression separator; \n or \r\n).
    Newline,
    /// Temporal literal: `@` followed by ISO 8601 date/time (e.g. @2026, @2026-02-26T14:30). Raw string without the @.
    TemporalLiteral(String),
    /// External stream input: `$` followed by identifier (e.g. $sales_data). Name is used to look up the stream handle in the stream input registry.
    DollarIdent(String),
}

/// Lexer error with optional byte span (start, end) for source snippet.
#[derive(Clone, Debug)]
pub enum LexicalError {
    InvalidFloat {
        snippet: String,
        start: usize,
        end: usize,
    },
    /// Malformed temporal literal after `@` (e.g. @20, incomplete or invalid ISO 8601).
    InvalidTemporal {
        snippet: String,
        start: usize,
        end: usize,
    },
}

impl LexicalError {
    /// Byte span for this error, if any.
    pub fn span(&self) -> Option<(usize, usize)> {
        match self {
            LexicalError::InvalidFloat { start, end, .. } => Some((*start, *end)),
            LexicalError::InvalidTemporal { start, end, .. } => Some((*start, *end)),
        }
    }
}

impl std::fmt::Display for LexicalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LexicalError::InvalidFloat { snippet, .. } => write!(f, "invalid float: {snippet}"),
            LexicalError::InvalidTemporal { snippet, .. } => {
                write!(f, "invalid temporal literal: @{snippet}")
            }
        }
    }
}

impl std::error::Error for LexicalError {}

pub struct Lexer<'input> {
    input: &'input str,
    pos: usize,
    /// True after emitting Num; used so ".3" after "1.2" is one number (1.2.3) and ".0" after "]" is Dot then Num.
    last_was_number: bool,
    /// True after we have returned at least one token; so ".5" at start of input is Num (no token yet) and "[1,2].0" gets Dot after ].
    any_token_emitted: bool,
    /// True after emitting Dot; so ". map (" yields MethodIdent("map") and ". length" yields Ident("length").
    after_dot: bool,
    /// True after a token that can end a PostfixFactor (Ident, Num, RParen, RBracket, RBrace); next `[` emits BracketKey(content until `]` trimmed) instead of LBracket.
    after_postfix_factor: bool,
    /// When we emit BracketKey we produce multiple tokens; buffer (start, tok, end) to return in order.
    token_buffer: Vec<(usize, Tok, usize)>,
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input str) -> Self {
        Lexer {
            input,
            pos: 0,
            last_was_number: false,
            any_token_emitted: false,
            after_dot: false,
            after_postfix_factor: false,
            token_buffer: Vec::new(),
        }
    }

    /// Skip only space and tab (not newlines; newlines are tokens for expression separation).
    fn skip_whitespace(&mut self) {
        let rest = &self.input[self.pos..];
        let skipped = rest.bytes().take_while(|b| *b == b' ' || *b == b'\t').count();
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

    fn take_num(&mut self) -> Option<Result<NumLiteral, LexicalError>> {
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
        let raw = rest[..end].to_string();
        let start = self.pos;
        self.pos += end;
        match f64::from_str(&raw) {
            Ok(v) => Some(Ok(NumLiteral {
                raw,
                value: OrderedFloat::from(v),
            })),
            Err(_) => Some(Err(LexicalError::InvalidFloat {
                snippet: raw,
                start,
                end: self.pos,
            })),
        }
    }

    /// Consume `@` and an ISO 8601 date/time sequence. Caller must have verified rest starts with `@`.
    /// Returns the raw string without `@` (e.g. "2026", "2026-02-26T14:30") or InvalidTemporal.
    fn take_temporal_literal(&mut self, start: usize) -> Result<String, LexicalError> {
        let rest = &self.input[self.pos..];
        if !rest.starts_with('@') {
            return Err(LexicalError::InvalidTemporal {
                snippet: String::new(),
                start,
                end: self.pos,
            });
        }
        self.pos += 1;
        let rest = &self.input[self.pos..];
        let bytes = rest.as_bytes();
        let n = bytes.len();

        fn take_digits(b: &[u8], from: usize, count: usize) -> bool {
            from + count <= b.len() && b[from..from + count].iter().all(|&c| c.is_ascii_digit())
        }
        if !take_digits(bytes, 0, 4) {
            return Err(LexicalError::InvalidTemporal {
                snippet: rest.chars().take(10).collect(),
                start,
                end: self.pos + rest.len().min(10),
            });
        }
        let mut end = 4usize;
        // Optional -MM
        if end + 3 <= n && bytes[end] == b'-' && take_digits(bytes, end + 1, 2) {
            end += 3;
            // Optional -DD
            if end + 3 <= n && bytes[end] == b'-' && take_digits(bytes, end + 1, 2) {
                end += 3;
                // Optional THH
                if end + 3 <= n && (bytes[end] == b'T' || bytes[end] == b't') && take_digits(bytes, end + 1, 2) {
                    end += 3;
                    // Optional :MM
                    if end + 3 <= n && bytes[end] == b':' && take_digits(bytes, end + 1, 2) {
                        end += 3;
                        // Optional :SS
                        if end + 3 <= n && bytes[end] == b':' && take_digits(bytes, end + 1, 2) {
                            end += 3;
                        }
                    }
                }
            }
        }
        let raw = rest[..end].to_string();
        self.pos += end;
        Ok(raw)
    }
}

impl<'input> Iterator for Lexer<'input> {
    type Item = Spanned<Tok, usize, LexicalError>;

    #[allow(clippy::cognitive_complexity)]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((start, tok, end)) = self.token_buffer.pop() {
            self.after_postfix_factor = matches!(&tok, Tok::RBracket);
            return Some(Ok((start, tok, end)));
        }
        self.skip_whitespace();
        if self.pos >= self.input.len() {
            return None;
        }
        let start = self.pos;
        let rest = &self.input[self.pos..];

        // Newline: \n or \r\n (expression separator); next token may start new expression (e.g. [1, 2]).
        if rest.starts_with('\n') {
            self.last_was_number = false;
            self.any_token_emitted = true;
            self.after_postfix_factor = false;
            self.pos += 1;
            return Some(Ok((start, Tok::Newline, self.pos)));
        }
        if rest.starts_with("\r\n") {
            self.last_was_number = false;
            self.any_token_emitted = true;
            self.after_postfix_factor = false;
            self.pos += 2;
            return Some(Ok((start, Tok::Newline, self.pos)));
        }
        if rest.starts_with('\r') {
            self.last_was_number = false;
            self.any_token_emitted = true;
            self.after_postfix_factor = false;
            self.pos += 1;
            return Some(Ok((start, Tok::Newline, self.pos)));
        }

        // Single chars / fixed strings (longer first); "as" before "per" so "aspect" stays Ident
        if rest.starts_with("as") && !rest[2..].chars().next().is_some_and(|c| c.is_alphanumeric() || c == '_') {
            self.last_was_number = false;
            self.any_token_emitted = true;
            self.pos += 2;
            return Some(Ok((start, Tok::As, self.pos)));
        }
        if rest.starts_with("per") && !rest[3..].chars().next().is_some_and(|c| c.is_alphanumeric() || c == '_') {
            self.last_was_number = false;
            self.any_token_emitted = true;
            self.pos += 3;
            return Some(Ok((start, Tok::Per, self.pos)));
        }
        if rest.starts_with("if") && !rest[2..].chars().next().is_some_and(|c| c.is_alphanumeric() || c == '_') {
            self.last_was_number = false;
            self.any_token_emitted = true;
            self.after_postfix_factor = false; // next token may start an expression (e.g. condition)
            self.pos += 2;
            return Some(Ok((start, Tok::If, self.pos)));
        }
        if rest.starts_with("then") && !rest[4..].chars().next().is_some_and(|c| c.is_alphanumeric() || c == '_') {
            self.last_was_number = false;
            self.any_token_emitted = true;
            self.after_postfix_factor = false; // next token may start an expression (then branch)
            self.pos += 4;
            return Some(Ok((start, Tok::Then, self.pos)));
        }
        if rest.starts_with("else") && !rest[4..].chars().next().is_some_and(|c| c.is_alphanumeric() || c == '_') {
            self.last_was_number = false;
            self.any_token_emitted = true;
            self.after_postfix_factor = false; // next token may start an expression (else branch, e.g. [1, 2])
            self.pos += 4;
            return Some(Ok((start, Tok::Else, self.pos)));
        }
        if rest.starts_with("input") && !rest[5..].chars().next().is_some_and(|c| c.is_alphanumeric() || c == '_') {
            self.last_was_number = false;
            self.any_token_emitted = true;
            self.pos += 5;
            return Some(Ok((start, Tok::Input, self.pos)));
        }
        if rest.starts_with("fn") && !rest[2..].chars().next().is_some_and(|c| c.is_alphanumeric() || c == '_') {
            self.last_was_number = false;
            self.any_token_emitted = true;
            self.pos += 2;
            return Some(Ok((start, Tok::Fn, self.pos)));
        }
        if rest.starts_with("π") {
            self.last_was_number = false;
            self.any_token_emitted = true;
            self.pos += "π".len();
            return Some(Ok((start, Tok::Pi, self.pos)));
        }
        // Two-char comparison tokens before single '<' or '>'. Next token may start an expression (e.g. RHS vector literal).
        if rest.starts_with("==") {
            self.last_was_number = false;
            self.any_token_emitted = true;
            self.after_postfix_factor = false;
            self.pos += 2;
            return Some(Ok((start, Tok::Eq, self.pos)));
        }
        if rest.starts_with("!=") {
            self.last_was_number = false;
            self.any_token_emitted = true;
            self.after_postfix_factor = false;
            self.pos += 2;
            return Some(Ok((start, Tok::Ne, self.pos)));
        }
        if rest.starts_with("<=") {
            self.last_was_number = false;
            self.any_token_emitted = true;
            self.after_postfix_factor = false;
            self.pos += 2;
            return Some(Ok((start, Tok::Le, self.pos)));
        }
        if rest.starts_with(">=") {
            self.last_was_number = false;
            self.any_token_emitted = true;
            self.after_postfix_factor = false;
            self.pos += 2;
            return Some(Ok((start, Tok::Ge, self.pos)));
        }
        if rest.starts_with("=>") {
            self.last_was_number = false;
            self.any_token_emitted = true;
            self.pos += 2;
            return Some(Ok((start, Tok::Arrow, self.pos)));
        }
        // Temporal literal: @YYYY, @YYYY-MM, @YYYY-MM-DD, @YYYY-MM-DDTHH, @YYYY-MM-DDTHH:MM, @YYYY-MM-DDTHH:MM:SS
        if rest.starts_with('@') {
            let is_temporal = rest
                .chars()
                .nth(1)
                .is_some_and(|c| c.is_ascii_digit());
            if is_temporal {
                match self.take_temporal_literal(start) {
                    Ok(raw) => {
                        self.last_was_number = false;
                        self.any_token_emitted = true;
                        self.after_postfix_factor = true;
                        let end = self.pos;
                        return Some(Ok((start, Tok::TemporalLiteral(raw), end)));
                    }
                    Err(e) => return Some(Err(e)),
                }
            }
            self.last_was_number = false;
            self.any_token_emitted = true;
            self.after_postfix_factor = false;
            self.pos += 1;
            return Some(Ok((start, Tok::At, self.pos)));
        }

        if rest.starts_with('$') {
            self.pos += 1;
            if let Some(name) = self.take_ident() {
                self.last_was_number = false;
                self.any_token_emitted = true;
                self.after_postfix_factor = true;
                let end = self.pos;
                return Some(Ok((start, Tok::DollarIdent(name), end)));
            }
            // $ not followed by identifier: treat as invalid (e.g. "$" or "$1")
            let error_end = (self.pos + rest.chars().take(5).map(|c| c.len_utf8()).sum::<usize>().min(rest.len())).min(self.input.len());
            let snippet = self.input[self.pos..error_end].to_string();
            return Some(Err(LexicalError::InvalidFloat {
                snippet,
                start: self.pos,
                end: error_end,
            }));
        }

        let mut it = rest.chars();
        let c = it.next()?;
        self.pos += c.len_utf8();

        // When after a PostfixFactor, `[` starts bracket-key: read until `]`, trim, emit LBracket + BracketKey + RBracket.
        if c == '[' && self.after_postfix_factor {
            let lbracket_end = self.pos;
            let key_start = self.pos;
            let mut depth = 1u32;
            let mut key_end = self.pos;
            while depth > 0 && self.pos < self.input.len() {
                let rest_inner = &self.input[self.pos..];
                let ch = rest_inner.chars().next()?;
                self.pos += ch.len_utf8();
                match ch {
                    '[' => depth += 1,
                    ']' => {
                        depth -= 1;
                        if depth == 0 {
                            key_end = self.pos - ch.len_utf8();
                        }
                    }
                    _ => {}
                }
            }
            let key = self.input[key_start..key_end].trim().to_string();
            self.token_buffer.push((key_end, Tok::RBracket, self.pos));
            self.token_buffer.push((key_start, Tok::BracketKey(key), key_end));
            self.token_buffer.push((start, Tok::LBracket, lbracket_end));
            self.after_postfix_factor = false;
            return self.next();
        }

        let tok = match c {
            '(' => Tok::LParen,
            ')' => Tok::RParen,
            '[' => Tok::LBracket,
            ']' => Tok::RBracket,
            '{' => Tok::LBrace,
            '}' => Tok::RBrace,
            ';' => Tok::Semicolon,
            '+' => Tok::Plus,
            '-' => Tok::Minus,
            '*' => Tok::Star,
            '/' => Tok::Slash,
            ',' => Tok::Comma,
            ':' => Tok::Colon,
            '\'' => Tok::Apostrophe,
            '~' => Tok::Tilde,
            '^' => Tok::Caret,
            '%' => Tok::Percent,
            '!' => Tok::Bang,
            '√' => Tok::SqrtPrefix,
            '∛' => Tok::CbrtPrefix,
            '|' => Tok::Bar,
            '=' => Tok::Assign,
            '<' => Tok::Lt,
            '>' => Tok::Gt,
            'a'..='z' | 'A'..='Z' | '_' => {
                self.pos -= c.len_utf8(); // put back
                if let Some(s) = self.take_ident() {
                    let next_non_space = self.peek_next_non_space();
                    let tok = if self.after_dot && next_non_space == Some('(') {
                        Tok::MethodIdent(s)
                    } else if next_non_space == Some('(') {
                        Tok::FuncIdent(s)
                    } else {
                        Tok::Ident(s)
                    };
                    self.last_was_number = false;
                    self.after_dot = false;
                    tok
                } else {
                    return None;
                }
            }
            '.' => {
                if self.last_was_number {
                    self.pos -= c.len_utf8();
                    match self.take_num()? {
                        Ok(lit) => Tok::Num(lit),
                        Err(e) => return Some(Err(e)),
                    }
                } else if !self.any_token_emitted {
                    // ".5" at start of input: no token emitted yet, so treat as number
                    self.pos -= c.len_utf8();
                    match self.take_num()? {
                        Ok(lit) => Tok::Num(lit),
                        Err(e) => return Some(Err(e)),
                    }
                } else {
                    self.last_was_number = false;
                    self.after_dot = true;
                    Tok::Dot
                }
            }
            '0'..='9' => {
                self.last_was_number = true;
                self.pos -= c.len_utf8();
                match self.take_num()? {
                    Ok(lit) => Tok::Num(lit),
                    Err(e) => return Some(Err(e)),
                }
            }
            _ => {
                let error_start = self.pos - c.len_utf8();
                let snippet = rest.chars().take(5).collect::<String>();
                return Some(Err(LexicalError::InvalidFloat {
                    snippet,
                    start: error_start,
                    end: self.pos,
                }));
            }
        };
        self.last_was_number = matches!(&tok, Tok::Num(_));
        self.any_token_emitted = true;
        self.after_dot = matches!(&tok, Tok::Dot);
        self.after_postfix_factor = matches!(
            &tok,
            Tok::Num(_) | Tok::Ident(_) | Tok::FuncIdent(_) | Tok::MethodIdent(_)
                | Tok::RParen | Tok::RBracket | Tok::RBrace
                | Tok::TemporalLiteral(_) | Tok::DollarIdent(_)
        );
        let end = self.pos;
        Some(Ok((start, tok, end)))
    }
}

