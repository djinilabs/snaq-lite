/// Errors that can occur when running a snaq-lite expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RunError {
    Parse(ParseError),
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
