//! Stream format enum and detection (extension + optional magic).
//! Add a new variant and extend [detect_format] to support another format.

use super::ParseError;
use super::ReadSeek;
use super::{CsvParser, TabularParser};
use snaq_lite_lang::{Record, StreamVarianceMode};
use std::path::Path;

#[cfg(feature = "parquet")]
use crate::{ArrowParser, ParquetParser};

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
        match self {
            StreamFormat::Csv => true,
            #[cfg(feature = "parquet")]
            StreamFormat::Parquet | StreamFormat::Arrow => true,
            #[cfg(not(feature = "parquet"))]
            StreamFormat::Parquet | StreamFormat::Arrow => false,
            StreamFormat::NumericLines => false,
        }
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
    // Arrow IPC magic without extension
    if magic.map(|m| m.starts_with(b"ARROW1")).unwrap_or(false) {
        return StreamFormat::Arrow;
    }

    // Default: numeric lines (current CLI behavior)
    StreamFormat::NumericLines
}

/// Get a tabular parser for the format. Returns None if format is not tabular or not supported.
/// Variance mode applies to text formats (CSV); Parquet/Arrow always use zero variance.
pub fn parser_for_format(
    format: StreamFormat,
    variance_mode: StreamVarianceMode,
) -> Option<Box<dyn TabularParser + Send>> {
    match format {
        StreamFormat::Csv => Some(Box::new(CsvParser::with_variance_mode(variance_mode))),
        #[cfg(feature = "parquet")]
        StreamFormat::Parquet => Some(Box::new(ParquetParser::new())),
        #[cfg(feature = "parquet")]
        StreamFormat::Arrow => Some(Box::new(ArrowParser::new())),
        #[cfg(not(feature = "parquet"))]
        StreamFormat::Parquet | StreamFormat::Arrow => None,
        StreamFormat::NumericLines => None,
    }
}

/// Parse a reader with the given format into an iterator of records.
/// Returns Err if the format is not tabular or not supported.
/// Variance mode affects CSV (infer from decimal places); Parquet/Arrow ignore it and use zero variance.
pub fn parse_tabular(
    format: StreamFormat,
    reader: Box<dyn ReadSeek>,
    variance_mode: StreamVarianceMode,
) -> Result<Box<dyn Iterator<Item = Result<Record, ParseError>> + Send>, ParseError> {
    let parser = parser_for_format(format, variance_mode)
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
    fn detect_format_arrow_magic() {
        assert_eq!(
            detect_format(Path::new("x"), Some(b"ARROW1")),
            StreamFormat::Arrow
        );
        assert_eq!(
            detect_format(Path::new("data"), Some(b"ARROW1padding")),
            StreamFormat::Arrow
        );
    }

    #[test]
    fn stream_format_is_tabular_and_supported() {
        assert!(StreamFormat::Csv.is_tabular() && StreamFormat::Csv.is_supported());
        assert!(StreamFormat::Parquet.is_tabular());
        assert!(StreamFormat::Arrow.is_tabular());
        #[cfg(feature = "parquet")]
        {
            assert!(StreamFormat::Parquet.is_supported());
            assert!(StreamFormat::Arrow.is_supported());
        }
        #[cfg(not(feature = "parquet"))]
        {
            assert!(!StreamFormat::Parquet.is_supported());
            assert!(!StreamFormat::Arrow.is_supported());
        }
        assert!(!StreamFormat::NumericLines.is_tabular() && !StreamFormat::NumericLines.is_supported());
    }

    #[test]
    fn parser_for_format_csv_only() {
        assert!(parser_for_format(StreamFormat::Csv, StreamVarianceMode::Zero).is_some());
        #[cfg(not(feature = "parquet"))]
        {
            assert!(parser_for_format(StreamFormat::Parquet, StreamVarianceMode::Zero).is_none());
            assert!(parser_for_format(StreamFormat::Arrow, StreamVarianceMode::Zero).is_none());
        }
        #[cfg(feature = "parquet")]
        {
            assert!(parser_for_format(StreamFormat::Parquet, StreamVarianceMode::Zero).is_some());
            assert!(parser_for_format(StreamFormat::Arrow, StreamVarianceMode::Zero).is_some());
        }
        assert!(parser_for_format(StreamFormat::NumericLines, StreamVarianceMode::Zero).is_none());
    }

    #[test]
    fn parse_tabular_csv_success() {
        let reader: Box<dyn ReadSeek> =
            Box::new(std::io::Cursor::new("a,b\n1,2".as_bytes().to_vec()));
        let iter = parse_tabular(StreamFormat::Csv, reader, StreamVarianceMode::Zero).expect("parse");
        let rows: Vec<_> = iter.collect();
        assert_eq!(rows.len(), 1);
        let record = rows[0].as_ref().expect("row ok");
        assert_eq!(record.len(), 2);
    }

    #[test]
    fn parse_tabular_csv_with_infer_yields_nonzero_variance() {
        use snaq_lite_lang::Value;
        let reader: Box<dyn ReadSeek> =
            Box::new(std::io::Cursor::new("x\n10.5".as_bytes().to_vec()));
        let iter = parse_tabular(
            StreamFormat::Csv,
            reader,
            StreamVarianceMode::InferFromDecimalPlaces,
        )
        .expect("parse");
        let rows: Vec<_> = iter.collect();
        assert_eq!(rows.len(), 1);
        let record = rows[0].as_ref().expect("row ok");
        assert_eq!(record.len(), 1);
        if let Value::Numeric(q) = &record[0].1 {
            assert!(q.variance() > 0.0, "infer mode should give non-zero variance for 10.5");
        } else {
            panic!("expected numeric cell");
        }
    }

    #[test]
    fn parse_tabular_unsupported_format_returns_err() {
        let reader: Box<dyn ReadSeek> = Box::new(std::io::Cursor::new(vec![]));
        let result = parse_tabular(StreamFormat::Parquet, reader, StreamVarianceMode::Zero);
        let err = match result {
            Err(e) => e,
            Ok(_) => panic!("expected Err for Parquet with empty input"),
        };
        #[cfg(not(feature = "parquet"))]
        assert!(err.to_string().contains("not supported"));
        #[cfg(feature = "parquet")]
        assert!(!err.to_string().is_empty());
    }

    #[cfg(feature = "parquet")]
    #[test]
    fn parse_tabular_arrow_invalid_bytes_returns_err() {
        let reader: Box<dyn ReadSeek> =
            Box::new(std::io::Cursor::new(b"not arrow ipc data".to_vec()));
        let result = parse_tabular(StreamFormat::Arrow, reader, StreamVarianceMode::Zero);
        assert!(result.is_err());
    }

    #[cfg(feature = "parquet")]
    #[test]
    fn parse_tabular_arrow_success() {
        use arrow::array::Int64Array;
        use arrow::datatypes::{DataType, Field, Schema};
        use arrow_ipc::writer::StreamWriter;
        use std::sync::Arc;

        let schema = Schema::new(vec![
            Field::new("x", DataType::Int64, false),
            Field::new("y", DataType::Int64, false),
        ]);
        let batch = arrow::record_batch::RecordBatch::try_new(
            Arc::new(schema),
            vec![
                Arc::new(Int64Array::from(vec![1_i64, 2])),
                Arc::new(Int64Array::from(vec![10_i64, 20])),
            ],
        )
        .expect("batch");
        let mut buf = Vec::new();
        let mut writer =
            StreamWriter::try_new(&mut buf, batch.schema().as_ref()).expect("stream writer");
        writer.write(&batch).expect("write");
        writer.finish().expect("finish");

        let reader: Box<dyn ReadSeek> = Box::new(std::io::Cursor::new(buf));
        let iter = parse_tabular(StreamFormat::Arrow, reader, StreamVarianceMode::Zero).expect("parse");
        let rows: Vec<_> = iter.collect();
        assert_eq!(rows.len(), 2);
        let r0 = rows[0].as_ref().expect("row 0");
        assert_eq!(r0.len(), 2);
        assert_eq!(r0[0].0, "x");
        assert_eq!(r0[1].0, "y");
    }

    #[cfg(feature = "parquet")]
    #[test]
    fn parse_tabular_parquet_success() {
        use arrow::array::Int64Array;
        use arrow::datatypes::{DataType, Field, Schema};
        use arrow::record_batch::RecordBatch;
        use parquet::arrow::ArrowWriter;
        use std::sync::Arc;

        let schema = Schema::new(vec![Field::new("n", DataType::Int64, false)]);
        let batch = RecordBatch::try_new(
            Arc::new(schema),
            vec![Arc::new(Int64Array::from(vec![7_i64]))],
        )
        .expect("batch");
        let mut buffer = Vec::new();
        let mut writer =
            ArrowWriter::try_new(&mut buffer, batch.schema().clone(), None).expect("writer");
        writer.write(&batch).expect("write");
        writer.close().expect("close");

        let reader: Box<dyn ReadSeek> = Box::new(std::io::Cursor::new(buffer));
        let iter = parse_tabular(StreamFormat::Parquet, reader, StreamVarianceMode::Zero).expect("parse");
        let rows: Vec<_> = iter.collect();
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].as_ref().expect("row").len(), 1);
        assert_eq!(rows[0].as_ref().expect("row")[0].0, "n");
    }
}
