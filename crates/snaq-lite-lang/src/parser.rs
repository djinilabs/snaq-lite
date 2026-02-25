//! Parser: expression string → `ExprDef`.
//! Uses LALRPOP-generated grammar with custom lexer (Ident vs FuncIdent for calls).

use crate::error::{ParseError, Span};
use crate::ir::{SpannedExprDef, SpannedExprDefKind};
use crate::lexer;
use lalrpop_util::lalrpop_mod;

lalrpop_mod!(
    #[allow(clippy::ptr_arg)]
    #[allow(clippy::empty_line_after_outer_attr)]
    #[allow(clippy::uninlined_format_args)]
    #[allow(clippy::type_complexity)]
    #[allow(clippy::cognitive_complexity)] // generated token match grows with grammar
    #[allow(dead_code)]
    #[allow(unused_imports)] // generated code imports Tok; type is used via full path in extern enum
    expr
);

fn lalrpop_error_to_parse_error(
    e: lalrpop_util::ParseError<usize, lexer::Tok, lexer::LexicalError>,
    input_len: usize,
) -> ParseError {
    use lalrpop_util::ParseError as LalrpopParseError;
    match e {
        LalrpopParseError::UnrecognizedToken {
            token: (start, ref tok, end),
            ref expected,
        } => {
            let expected_str = if expected.is_empty() {
                "unexpected token".to_string()
            } else if expected.len() == 1 {
                format!("expected {}", expected[0])
            } else {
                format!("expected one of {}", expected.join(", "))
            };
            let msg = format!("{expected_str}: {tok:?}");
            ParseError::with_span(msg, Span { start, end })
        }
        LalrpopParseError::ExtraToken {
            token: (start, ref tok, end),
        } => {
            let msg = format!("extra token: {tok:?}");
            ParseError::with_span(msg, Span { start, end })
        }
        LalrpopParseError::UnrecognizedEof { ref expected, location } => {
            let expected_str = if expected.is_empty() {
                "unexpected end of input".to_string()
            } else if expected.len() == 1 {
                format!("expected {} before end of input", expected[0])
            } else {
                format!("expected one of {} before end of input", expected.join(", "))
            };
            let end = location.max(input_len);
            ParseError::with_span(expected_str, Span { start: location, end })
        }
        LalrpopParseError::InvalidToken { location } => {
            ParseError::with_span("invalid token".to_string(), Span { start: location, end: location })
        }
        LalrpopParseError::User { error: lex_err } => {
            if let Some((start, end)) = lex_err.span() {
                ParseError::with_span(lex_err.to_string(), Span { start, end })
            } else {
                ParseError::new(lex_err.to_string())
            }
        }
    }
}

/// Parse a program (expression list, possibly with blocks). Returns a [SpannedExprDef] that is a Block at top level.
/// Uses custom lexer so "sin(1)" is a call and "sin" is a symbol.
/// Empty or whitespace-only input returns Block([]) without invoking the grammar (avoids conflict with non-empty Program).
pub fn parse(input: &str) -> Result<SpannedExprDef, ParseError> {
    if input.trim().is_empty() {
        return Ok(SpannedExprDef {
            span: crate::error::Span::default(),
            value: SpannedExprDefKind::Block(vec![]),
        });
    }
    let lexer = lexer::Lexer::new(input);
    let len = input.len();
    expr::ProgramParser::new()
        .parse(lexer)
        .map_err(|e| lalrpop_error_to_parse_error(e, len))
}
