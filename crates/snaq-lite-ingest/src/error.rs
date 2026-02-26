//! Parse errors for ingest (format-specific). Convert to [snaq_lite_lang::RunError] at the chunk boundary if needed.

use std::fmt;

/// Error from parsing a stream source (CSV, Parquet, etc.).
#[derive(Debug, Clone)]
pub struct ParseError {
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for ParseError {}

impl ParseError {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}
