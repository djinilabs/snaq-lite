//! Stream format enum and detection (extension + optional magic).
//! Add a new variant and extend [detect_format] to support another format.

use super::ParseError;
use super::{CsvParser, TabularParser};
use snaq_lite_lang::Record;
use std::io::Read;
use std::path::Path;

/// Known tabular or scalar stream formats. Add variants (e.g. Ndjson, Excel) and implement [TabularParser].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StreamFormat {
    /// CSV: first row = headers, rest = rows; cells → numeric or undefined.
    Csv,
    /// Parquet (optional feature). Not supported in this build.
    Parquet,
    /// Arrow IPC / stream (optional feature). Not supported in this build.
    Arrow,
    /// Newline-delimited numbers (one scalar per line). Handled by CLI, not a tabular parser.
    NumericLines,
}

impl StreamFormat {
    /// Whether this format is tabular (rows as records) and has a tabular parser in this crate.
    pub fn is_tabular(self) -> bool {
        matches!(self, StreamFormat::Csv | StreamFormat::Parquet | StreamFormat::Arrow)
    }

    /// Whether this format is supported in the current build (e.g. Parquet/Arrow may be feature-gated).
    pub fn is_supported(self) -> bool {
        matches!(self, StreamFormat::Csv)
    }
}

/// Detect format from file path (extension) and optionally magic bytes.
/// Returns [StreamFormat::NumericLines] for unknown or missing extension (backward compatibility).
pub fn detect_format(path: &Path, magic: Option<&[u8]>) -> StreamFormat {
    let ext = path
        .extension()
        .and_then(|e| e.to_str())
        .map(|s| s.to_lowercase())
        .unwrap_or_default();

    if ext == "csv" {
        return StreamFormat::Csv;
    }
    if ext == "parquet" {
        return StreamFormat::Parquet;
    }
    if ext == "arrow" || ext == "ipc" {
        return StreamFormat::Arrow;
    }

    // Parquet magic without extension
    if magic.map(|m| m.starts_with(b"PAR1")).unwrap_or(false) {
        return StreamFormat::Parquet;
    }

    // Default: numeric lines (current CLI behavior)
    StreamFormat::NumericLines
}

/// Get a tabular parser for the format. Returns None if format is not tabular or not supported.
pub fn parser_for_format(format: StreamFormat) -> Option<Box<dyn TabularParser + Send>> {
    match format {
        StreamFormat::Csv => Some(Box::new(CsvParser::new())),
        StreamFormat::Parquet | StreamFormat::Arrow => None,
        StreamFormat::NumericLines => None,
    }
}

/// Parse a reader with the given format into an iterator of records.
/// Returns Err if the format is not tabular or not supported.
pub fn parse_tabular(
    format: StreamFormat,
    reader: Box<dyn Read + Send>,
) -> Result<Box<dyn Iterator<Item = Result<Record, ParseError>> + Send>, ParseError> {
    let parser = parser_for_format(format)
        .ok_or_else(|| ParseError::new(format!("format {format:?} is not supported")))?;
    parser.parse(reader)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    #[test]
    fn detect_format_csv_extension() {
        assert_eq!(detect_format(Path::new("data.csv"), None), StreamFormat::Csv);
        assert_eq!(detect_format(Path::new("x.CSV"), None), StreamFormat::Csv);
        assert_eq!(detect_format(Path::new("/a/b/file.csv"), None), StreamFormat::Csv);
    }

    #[test]
    fn detect_format_parquet_arrow_ipc() {
        assert_eq!(detect_format(Path::new("x.parquet"), None), StreamFormat::Parquet);
        assert_eq!(detect_format(Path::new("x.arrow"), None), StreamFormat::Arrow);
        assert_eq!(detect_format(Path::new("x.ipc"), None), StreamFormat::Arrow);
    }

    #[test]
    fn detect_format_numeric_lines_default() {
        assert_eq!(detect_format(Path::new("x.txt"), None), StreamFormat::NumericLines);
        assert_eq!(detect_format(Path::new("numbers"), None), StreamFormat::NumericLines);
        assert_eq!(detect_format(Path::new("/a/b"), None), StreamFormat::NumericLines);
    }

    #[test]
    fn detect_format_parquet_magic() {
        assert_eq!(
            detect_format(Path::new("x"), Some(b"PAR1something")),
            StreamFormat::Parquet
        );
        assert_eq!(
            detect_format(Path::new("x.parquet"), Some(b"PAR1")),
            StreamFormat::Parquet
        );
    }

    #[test]
    fn stream_format_is_tabular_and_supported() {
        assert!(StreamFormat::Csv.is_tabular() && StreamFormat::Csv.is_supported());
        assert!(StreamFormat::Parquet.is_tabular() && !StreamFormat::Parquet.is_supported());
        assert!(StreamFormat::Arrow.is_tabular() && !StreamFormat::Arrow.is_supported());
        assert!(!StreamFormat::NumericLines.is_tabular() && !StreamFormat::NumericLines.is_supported());
    }

    #[test]
    fn parser_for_format_csv_only() {
        assert!(parser_for_format(StreamFormat::Csv).is_some());
        assert!(parser_for_format(StreamFormat::Parquet).is_none());
        assert!(parser_for_format(StreamFormat::Arrow).is_none());
        assert!(parser_for_format(StreamFormat::NumericLines).is_none());
    }

    #[test]
    fn parse_tabular_csv_success() {
        let reader: Box<dyn Read + Send> = Box::new("a,b\n1,2".as_bytes());
        let iter = parse_tabular(StreamFormat::Csv, reader).expect("parse");
        let rows: Vec<_> = iter.collect();
        assert_eq!(rows.len(), 1);
        let record = rows[0].as_ref().expect("row ok");
        assert_eq!(record.len(), 2);
    }

    #[test]
    fn parse_tabular_unsupported_format_returns_err() {
        let reader: Box<dyn Read + Send> = Box::new(b"".as_ref());
        let result = parse_tabular(StreamFormat::Parquet, reader);
        let err = match result {
            Err(e) => e,
            Ok(_) => panic!("expected Err for unsupported Parquet format"),
        };
        assert!(err.to_string().contains("not supported"));
    }
}
