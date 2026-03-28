//! Map snaq-lite spans and errors to LSP types.

use crate::position;
use snaq_lite_lang::{RunError, RunErrorKind, Span};
use tower_lsp::lsp_types::{Diagnostic, DiagnosticSeverity, Position, Range};

/// Source identifier for diagnostics and server info.
pub const SERVER_NAME: &str = "snaq-lite";

/// Convert a byte span to an LSP range.
/// LSP uses 0-based UTF-16 line/character.
pub fn span_to_range(span: &Span, source: &str) -> Range {
    position::span_to_range(span, source)
}

/// Fallback range when no span is available: first line of the document so the user sees an error decoration.
pub(crate) fn fallback_range(source: &str) -> Range {
    let end_char = source
        .lines()
        .next()
        .map(|line| line.len() as u32)
        .unwrap_or(1)
        .max(1);
    Range {
        start: Position {
            line: 0,
            character: 0,
        },
        end: Position {
            line: 0,
            character: end_char,
        },
    }
}

/// Convert a RunError to an LSP Diagnostic.
pub fn run_error_to_diagnostic(err: &RunError, source: &str) -> Diagnostic {
    let (range, message) = match &err.kind {
        RunErrorKind::Parse(pe) => {
            let range = err
                .span
                .or(pe.span)
                .map(|s| span_to_range(&s, source))
                .unwrap_or_else(|| fallback_range(source));
            (range, pe.message.clone())
        }
        _ => {
            let range = err
                .span
                .map(|s| span_to_range(&s, source))
                .unwrap_or_else(|| fallback_range(source));
            (range, format!("{err}"))
        }
    };
    Diagnostic {
        range,
        message,
        severity: Some(DiagnosticSeverity::ERROR),
        code: None,
        code_description: None,
        source: Some(SERVER_NAME.to_string()),
        related_information: None,
        tags: None,
        data: None,
    }
}
