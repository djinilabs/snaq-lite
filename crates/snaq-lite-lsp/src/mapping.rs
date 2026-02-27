//! Map snaq-lite spans and errors to LSP types.

use tower_lsp::lsp_types::{Diagnostic, DiagnosticSeverity, Position, Range};
use snaq_lite_lang::{RunError, RunErrorKind, Span};

/// Source identifier for diagnostics and server info.
pub const SERVER_NAME: &str = "snaq-lite";

/// Convert a byte span to an LSP range.
/// LSP uses 0-based line and 0-based character (we use byte offset as character).
pub fn span_to_range(span: &Span, source: &str) -> Range {
    // Lang returns 1-based line; column is already byte offset from line start (effectively 0-based for LSP).
    let (line_1, col_1) = span.line_col(source);
    let line_0 = line_1.saturating_sub(1);
    let col_0 = col_1;
    let start = Position {
        line: line_0,
        character: col_0,
    };
    let end_line = if span.end <= source.len() {
        let prefix = source.get(..span.end).unwrap_or("");
        let lines = prefix.lines().count() as u32;
        lines.saturating_sub(1)
    } else {
        line_0
    };
    let end_col = if span.end <= source.len() {
        let prefix = source.get(..span.end).unwrap_or("");
        let last_nl = prefix.rfind('\n').map(|i| i + 1).unwrap_or(0);
        (span.end - last_nl) as u32
    } else {
        col_0
    };
    Range {
        start,
        end: Position {
            line: end_line,
            character: end_col,
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
                .unwrap_or(Range {
                    start: Position { line: 0, character: 0 },
                    end: Position { line: 0, character: 0 },
                });
            (range, pe.message.clone())
        }
        _ => {
            let range = err
                .span
                .map(|s| span_to_range(&s, source))
                .unwrap_or(Range {
                    start: Position { line: 0, character: 0 },
                    end: Position { line: 0, character: 0 },
                });
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
