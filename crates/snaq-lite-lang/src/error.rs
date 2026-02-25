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
    /// Transpose operator (') applied to a non-vector (scalar or symbolic).
    ExpectedVector,
    /// Vector operation (element-wise or dot) requires same length; left and right lengths differ.
    VectorLengthMismatch { left_len: usize, right_len: usize },
    /// Result is boolean (e.g. comparison); cannot convert to quantity.
    BooleanResult,
    /// If condition must evaluate to a boolean (FuzzyBool), not a number or symbolic.
    ExpectedCondition,
    /// Both branches of if/then/else must be numeric or symbolic (blendable); got boolean or vector.
    IfBranchTypeMismatch,
    /// Both sides of ~ (explicit precision) must be numeric (not symbolic, boolean, or vector).
    TildeRequiresNumeric,
    /// Right-hand side of ~ (explicit precision) must be strictly positive.
    PrecisionMustBePositive,
    /// Result is undefined (e.g. empty block or empty program); cannot convert to quantity.
    UndefinedResult,
    /// Variable binding RHS cannot be stored in scope (e.g. symbolic or vector in v1).
    BindingValueNotSupported(String),
    /// Cannot bind a name that shadows a built-in function (sin, cos, tan, max, min).
    CannotObfuscateBuiltin(String),
    /// Index or slice start/length must be a non-negative integer (e.g. take(V, start, length) or V[i]).
    InvalidIndex(String),
    /// Vector index out of bounds (single-element access V[i]).
    IndexOutOfBounds { index: usize, length: usize },
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
            RunError::ExpectedVector => {
                write!(f, "transpose (') requires a vector (got scalar or symbolic)")
            }
            RunError::VectorLengthMismatch { left_len, right_len } => {
                write!(
                    f,
                    "vector length mismatch: left has {left_len} elements, right has {right_len}"
                )
            }
            RunError::BooleanResult => {
                write!(f, "result is boolean (e.g. comparison), cannot convert to quantity")
            }
            RunError::ExpectedCondition => {
                write!(f, "if condition must evaluate to true, false, or uncertain (got number or symbolic)")
            }
            RunError::IfBranchTypeMismatch => {
                write!(f, "if branches must both be numeric or symbolic (cannot blend boolean or vector)")
            }
            RunError::TildeRequiresNumeric => {
                write!(f, "both sides of ~ (explicit precision) must be numeric")
            }
            RunError::PrecisionMustBePositive => {
                write!(f, "precision (right side of ~) must be strictly positive")
            }
            RunError::UndefinedResult => {
                write!(f, "result is undefined (e.g. empty block), cannot convert to quantity")
            }
            RunError::BindingValueNotSupported(msg) => {
                write!(f, "variable binding: {msg}")
            }
            RunError::CannotObfuscateBuiltin(name) => {
                write!(f, "cannot shadow built-in function: {name}")
            }
            RunError::InvalidIndex(msg) => write!(f, "invalid index: {msg}"),
            RunError::IndexOutOfBounds { index, length } => {
                write!(f, "index {index} out of bounds (vector length {length})")
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
