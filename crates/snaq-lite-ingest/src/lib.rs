//! Host-agnostic parsers for tabular and scalar stream sources.
//!
//! Parsers accept a byte source (`impl Read`) and produce [Record]s (tabular) or scalars.
//! The host (CLI or WASM) owns I/O; this crate only parses. Add new formats by implementing
//! [TabularParser] and extending [StreamFormat] and [detect_format].

mod csv_parser;
mod error;
mod format;
#[cfg(feature = "parquet")]
mod arrow_parser;
#[cfg(feature = "parquet")]
mod parquet_parser;
#[cfg(feature = "parquet")]
mod record_batch;

#[cfg(feature = "parquet")]
pub use arrow_parser::ArrowParser;
#[cfg(feature = "parquet")]
pub use parquet_parser::ParquetParser;

pub use csv_parser::CsvParser;
pub use error::ParseError;
pub use format::{detect_format, parse_tabular, StreamFormat};

use snaq_lite_lang::Record;
use std::io::{Read, Seek};

/// Trait alias for a reader that is both [Read] and [Seek] and [Send].
/// Used so we can have a single object-safe trait (Rust allows only one non-auto trait in a trait object).
pub trait ReadSeek: Read + Seek + Send {}
impl<T: Read + Seek + Send> ReadSeek for T {}

/// Parser that produces tabular rows (records) from a byte source.
/// Implement this trait to add a new tabular format (e.g. NDJSON, Excel).
/// Takes [Box<dyn ReadSeek>] so the trait is object-safe and supports formats that need Seek (e.g. Parquet, Arrow IPC file).
pub trait TabularParser {
    /// Parse the reader into an iterator of records. Each record is one row (column name → value).
    /// The iterator owns the reader (or a wrapper around it).
    fn parse(
        &self,
        reader: Box<dyn ReadSeek>,
    ) -> Result<Box<dyn Iterator<Item = Result<Record, ParseError>> + Send>, ParseError>;
}

/// Optional: return true if this parser can handle the given extension and/or magic bytes.
/// Used by [detect_format] to select a parser.
pub trait TabularParserDetect {
    fn can_detect(&self, extension: &str, magic: Option<&[u8]>) -> bool;
}
