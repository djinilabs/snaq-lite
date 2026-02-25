/// Byte-range span in the source (inclusive start, exclusive end).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    /// 1-based (line, column) for the start of this span. Column is in bytes.
    pub fn line_col(&self, source: &str) -> (u32, u32) {
        let prefix = source.get(..self.start).unwrap_or("");
        let line = prefix.lines().count() as u32;
        let last_newline = prefix.rfind('\n').map(|i| i + 1).unwrap_or(0);
        let column = (self.start - last_newline) as u32;
        (line.max(1), column.max(1))
    }

    /// Slice of source for this span, truncated to max_len with "..." if needed.
    pub fn snippet(&self, source: &str, max_len: usize) -> String {
        let slice = source.get(self.start..self.end.min(self.start + source.len())).unwrap_or("");
        if slice.len() <= max_len {
            slice.to_string()
        } else {
            format!("{}...", &slice[..max_len.saturating_sub(3)])
        }
    }

    /// Line of source containing this span and a squiggle line (spaces then ~ under the span).
    /// Returns None if source is empty or span is invalid. Column is 1-based for display.
    pub fn snippet_with_squiggle(&self, source: &str) -> Option<(String, String)> {
        if source.is_empty() {
            return None;
        }
        let start = self.start.min(source.len());
        let (line_1based, _col_1based) = self.line_col(source);
        let line_idx = (line_1based as usize).saturating_sub(1);
        let line_content = source.lines().nth(line_idx)?;
        let last_newline = source.get(..start)?.rfind('\n').map(|i| i + 1).unwrap_or(0);
        let col_byte = start - last_newline;
        let span_len_byte = (self.end.saturating_sub(self.start)).min(line_content.len().saturating_sub(col_byte));
        let squiggle_len = span_len_byte.max(1);
        let spaces = " ".repeat(col_byte);
        let squiggle = "~".repeat(squiggle_len);
        Some((line_content.to_string(), format!("{spaces}{squiggle}")))
    }
}

/// Kind of run error (no source location).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RunErrorKind {
    Parse(ParseError),
    UnknownUnit(String),
    DimensionMismatch {
        left: crate::unit::Unit,
        right: crate::unit::Unit,
    },
    DivisionByZero,
    SymbolHasNoValue(String),
    UnknownFunction(String),
    ExpectedAngle { actual: crate::unit::Unit },
    UnsupportedVectorOperation,
    ExpectedVector,
    VectorLengthMismatch { left_len: usize, right_len: usize },
    BooleanResult,
    ExpectedCondition,
    IfBranchTypeMismatch,
    TildeRequiresNumeric,
    PrecisionMustBePositive,
    UndefinedResult,
    BindingValueNotSupported(String),
    CannotObfuscateBuiltin(String),
    InvalidIndex(String),
    IndexOutOfBounds { index: usize, length: usize },
    UnknownProperty(String),
    UnknownMethod(String),
    EmptyVectorReduction(String),
    InvalidArgument(String),
}

/// Errors that can occur when running a snaq-lite expression.
/// Carries an optional source span for runtime errors (e.g. division by zero at a specific `/`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RunError {
    pub span: Option<Span>,
    pub kind: RunErrorKind,
}

impl RunError {
    /// Build a runtime error with no location.
    pub fn new(kind: RunErrorKind) -> Self {
        Self { span: None, kind }
    }

    /// Build a runtime error at a source location.
    pub fn at(span: Span, kind: RunErrorKind) -> Self {
        Self {
            span: Some(span),
            kind,
        }
    }

    /// Attach a span to an existing error (e.g. when propagating from a subcall).
    pub fn with_span(mut self, span: Span) -> Self {
        self.span = Some(span);
        self
    }
}

/// Parse error for expression strings.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub message: String,
    pub span: Option<Span>,
}

impl ParseError {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            span: None,
        }
    }

    pub fn with_span(message: impl Into<String>, span: Span) -> Self {
        Self {
            message: message.into(),
            span: Some(span),
        }
    }

    /// Format error with optional source for line/column, snippet, and squiggle under the error span.
    pub fn format_with_source(&self, source: Option<&str>) -> String {
        let mut out = String::new();
        if let Some(span) = self.span {
            if let Some(s) = source {
                let (line, col) = span.line_col(s);
                out.push_str(&format!("parse error at line {line}, column {col}: "));
            } else {
                out.push_str(&format!("parse error at byte {}-{}: ", span.start, span.end));
            }
        } else {
            out.push_str("parse error: ");
        }
        out.push_str(&self.message);
        if let (Some(span), Some(s)) = (self.span, source) {
            if let Some((line_content, squiggle_line)) = span.snippet_with_squiggle(s) {
                out.push_str("\n\n");
                let (line, _col) = span.line_col(s);
                let line_num_width = (line.max(1)).to_string().len();
                let padding = " ".repeat(line_num_width);
                out.push_str(&format!("  {padding} |\n"));
                out.push_str(&format!("  {line} | {line_content}\n"));
                out.push_str(&format!("  {padding} | {squiggle_line}\n"));
            }
        }
        out
    }
}

impl From<ParseError> for RunError {
    fn from(e: ParseError) -> Self {
        RunError {
            span: e.span,
            kind: RunErrorKind::Parse(e),
        }
    }
}

impl From<RunErrorKind> for RunError {
    fn from(kind: RunErrorKind) -> Self {
        RunError::new(kind)
    }
}

/// Format a run error for display. When source is provided, includes line/column and
/// a snippet with squiggle for both parse and runtime errors (when span is present).
pub fn format_run_error_with_source(err: &RunError, source: Option<&str>) -> String {
    if let RunErrorKind::Parse(pe) = &err.kind {
        return pe.format_with_source(source);
    }
    let msg = format!("{err}");
    let span = err.span;
    if let (Some(span), Some(s)) = (span, source) {
        if let Some((line_content, squiggle_line)) = span.snippet_with_squiggle(s) {
            let (line, col) = span.line_col(s);
            let line_num_width = (line.max(1)).to_string().len();
            let padding = " ".repeat(line_num_width);
            return format!(
                "at line {line}, column {col}: {msg}\n\n  {padding} |\n  {line} | {line_content}\n  {padding} | {squiggle_line}\n"
            );
        }
    }
    msg
}

impl std::fmt::Display for RunError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            RunErrorKind::Parse(e) => write!(f, "{e}"),
            RunErrorKind::UnknownUnit(name) => write!(f, "unknown unit: {name}"),
            RunErrorKind::DimensionMismatch { left, right } => {
                write!(f, "dimension mismatch: {left} vs {right}")
            }
            RunErrorKind::DivisionByZero => write!(f, "division by zero"),
            RunErrorKind::SymbolHasNoValue(name) => {
                write!(f, "symbol '{name}' has no numeric value")
            }
            RunErrorKind::UnknownFunction(name) => write!(f, "unknown function: {name}"),
            RunErrorKind::ExpectedAngle { actual } => {
                write!(f, "expected angle (rad or degree), got ")?;
                if actual.is_scalar() {
                    write!(f, "(dimensionless)")?;
                    write!(
                        f,
                        " — if your value is in radians, add the rad unit (e.g. sin(pi * rad))"
                    )?;
                } else {
                    write!(f, "{actual}")?;
                }
                Ok(())
            }
            RunErrorKind::UnsupportedVectorOperation => {
                write!(f, "operation not supported for vector (expected scalar)")
            }
            RunErrorKind::ExpectedVector => {
                write!(f, "transpose (') requires a vector (got scalar or symbolic)")
            }
            RunErrorKind::VectorLengthMismatch { left_len, right_len } => {
                write!(
                    f,
                    "vector length mismatch: left has {left_len} elements, right has {right_len}"
                )
            }
            RunErrorKind::BooleanResult => {
                write!(f, "result is boolean (e.g. comparison), cannot convert to quantity")
            }
            RunErrorKind::ExpectedCondition => {
                write!(f, "if condition must evaluate to true, false, or uncertain (got number or symbolic)")
            }
            RunErrorKind::IfBranchTypeMismatch => {
                write!(f, "if branches must both be numeric or symbolic (cannot blend boolean or vector)")
            }
            RunErrorKind::TildeRequiresNumeric => {
                write!(f, "both sides of ~ (explicit precision) must be numeric")
            }
            RunErrorKind::PrecisionMustBePositive => {
                write!(f, "precision (right side of ~) must be strictly positive")
            }
            RunErrorKind::UndefinedResult => {
                write!(f, "result is undefined (e.g. empty block), cannot convert to quantity")
            }
            RunErrorKind::BindingValueNotSupported(msg) => {
                write!(f, "variable binding: {msg}")
            }
            RunErrorKind::CannotObfuscateBuiltin(name) => {
                write!(f, "cannot shadow built-in function: {name}")
            }
            RunErrorKind::InvalidIndex(msg) => write!(f, "invalid index: {msg}"),
            RunErrorKind::IndexOutOfBounds { index, length } => {
                write!(f, "index {index} out of bounds (vector length {length})")
            }
            RunErrorKind::UnknownProperty(name) => {
                write!(f, "unknown property: {name}")
            }
            RunErrorKind::UnknownMethod(name) => {
                write!(f, "unknown method: {name}")
            }
            RunErrorKind::EmptyVectorReduction(method) => {
                write!(f, "empty vector: {method} requires at least one element")
            }
            RunErrorKind::InvalidArgument(msg) => write!(f, "invalid argument: {msg}"),
        }
    }
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.format_with_source(None))
    }
}

impl std::error::Error for RunError {}
impl std::error::Error for ParseError {}
