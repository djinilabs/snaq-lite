//! Host-agnostic parsers for tabular and scalar stream sources.
//!
//! Parsers accept a byte source (`impl Read`) and produce [Record]s (tabular) or scalars.
//! The host (CLI or WASM) owns I/O; this crate only parses. Add new formats by implementing
//! [TabularParser] and extending [StreamFormat] and [detect_format].

mod csv_parser;
mod error;
mod format;

pub use error::ParseError;
pub use format::{detect_format, parse_tabular, StreamFormat};
pub use csv_parser::CsvParser;

use snaq_lite_lang::Record;
use std::io::Read;

/// Parser that produces tabular rows (records) from a byte source.
/// Implement this trait to add a new tabular format (e.g. NDJSON, Excel).
/// Takes [Box<dyn Read + Send>] so the trait is object-safe (no generic method).
pub trait TabularParser {
    /// Parse the reader into an iterator of records. Each record is one row (column name → value).
    /// The iterator owns the reader (or a wrapper around it).
    fn parse(
        &self,
        reader: Box<dyn Read + Send>,
    ) -> Result<Box<dyn Iterator<Item = Result<Record, ParseError>> + Send>, ParseError>;
}

/// Optional: return true if this parser can handle the given extension and/or magic bytes.
/// Used by [detect_format] to select a parser.
pub trait TabularParserDetect {
    fn can_detect(&self, extension: &str, magic: Option<&[u8]>) -> bool;
}
