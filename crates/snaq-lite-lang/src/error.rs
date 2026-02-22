/// Errors that can occur when running a snaq-lite expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RunError {
    Parse(ParseError),
    UnknownUnit(String),
    DimensionMismatch {
        left: crate::unit::Unit,
        right: crate::unit::Unit,
    },
    DivisionByZero,
    /// A symbol in the expression has no numeric value in the symbol registry (cannot substitute).
    SymbolHasNoValue(String),
    /// Unknown function name at call site.
    UnknownFunction(String),
    /// Trig function (sin, cos, tan) received an argument that is not an angle (rad or degree).
    ExpectedAngle { actual: crate::unit::Unit },
    /// Operation not supported for vector (e.g. arithmetic or to_quantity).
    UnsupportedVectorOperation,
}

/// Parse error for expression strings.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub message: String,
}

impl ParseError {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl From<ParseError> for RunError {
    fn from(e: ParseError) -> Self {
        RunError::Parse(e)
    }
}

impl std::fmt::Display for RunError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RunError::Parse(e) => write!(f, "parse error: {}", e.message),
            RunError::UnknownUnit(name) => write!(f, "unknown unit: {name}"),
            RunError::DimensionMismatch { left, right } => {
                write!(f, "dimension mismatch: {left} vs {right}")
            }
            RunError::DivisionByZero => write!(f, "division by zero"),
            RunError::SymbolHasNoValue(name) => {
                write!(f, "symbol '{name}' has no numeric value")
            }
            RunError::UnknownFunction(name) => write!(f, "unknown function: {name}"),
            RunError::ExpectedAngle { actual } => {
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
            RunError::UnsupportedVectorOperation => {
                write!(f, "operation not supported for vector (expected scalar)")
            }
        }
    }
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for RunError {}
impl std::error::Error for ParseError {}
