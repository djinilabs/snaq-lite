//! Arrow IPC tabular parser: streams row-by-row from RecordBatches.
//! Supports both IPC file format (with footer) and IPC stream format (sequential).
//! Reads the input into memory so we can try both formats; rows are then streamed out.

use super::ParseError;
use super::ReadSeek;
use super::TabularParser;
use crate::record_batch::row_to_record;
use arrow_ipc::reader::FileReader;
use arrow_ipc::reader::StreamReader;
use snaq_lite_lang::Record;
use std::io::Read;

/// Arrow IPC parser. Tries file format (with footer) first, then stream format.
/// Yields one [Record] per row from each RecordBatch.
pub struct ArrowParser;

impl ArrowParser {
    pub fn new() -> Self {
        Self
    }
}

impl Default for ArrowParser {
    fn default() -> Self {
        Self::new()
    }
}

impl TabularParser for ArrowParser {
    fn parse(
        &self,
        reader: Box<dyn ReadSeek>,
    ) -> Result<Box<dyn Iterator<Item = Result<Record, ParseError>> + Send>, ParseError> {
        let mut buf = Vec::new();
        reader
            .take(usize::MAX as u64)
            .read_to_end(&mut buf)
            .map_err(|e| ParseError::new(e.to_string()))?;

        // Try file format first (has footer; requires Seek)
        if let Ok(file_reader) = FileReader::try_new(std::io::Cursor::new(buf.clone()), None) {
            return Ok(Box::new(ArrowRowIter {
                batch_iter: ArrowBatchSource::File(file_reader),
                current_batch: None,
                row_index: 0,
            }));
        }
        // Try stream format
        let stream_reader = StreamReader::try_new(std::io::Cursor::new(buf), None)
            .map_err(|e| ParseError::new(e.to_string()))?;
        Ok(Box::new(ArrowRowIter {
            batch_iter: ArrowBatchSource::Stream(stream_reader),
            current_batch: None,
            row_index: 0,
        }))
    }
}

enum ArrowBatchSource {
    File(FileReader<std::io::Cursor<Vec<u8>>>),
    Stream(StreamReader<std::io::Cursor<Vec<u8>>>),
}

struct ArrowRowIter {
    batch_iter: ArrowBatchSource,
    current_batch: Option<arrow::record_batch::RecordBatch>,
    row_index: usize,
}

impl Iterator for ArrowRowIter {
    type Item = Result<Record, ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(ref batch) = self.current_batch {
                if self.row_index < batch.num_rows() {
                    let row_index = self.row_index;
                    self.row_index += 1;
                    return Some(row_to_record(batch, row_index));
                }
            }
            let next_batch = match &mut self.batch_iter {
                ArrowBatchSource::File(r) => r.next(),
                ArrowBatchSource::Stream(r) => r.next(),
            };
            self.current_batch = match next_batch {
                Some(Ok(batch)) => Some(batch),
                Some(Err(e)) => return Some(Err(ParseError::new(e.to_string()))),
                None => return None,
            };
            self.row_index = 0;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use arrow::array::{Float64Array, Int64Array, RecordBatch};
    use arrow::datatypes::{DataType, Field, Schema};
    use arrow_ipc::writer::{FileWriter, StreamWriter};
    use snaq_lite_lang::Value;
    use std::io::Cursor;
    use std::sync::Arc;

    fn numeric_value(v: &Value) -> Option<f64> {
        match v {
            Value::Numeric(q) => Some(q.value()),
            _ => None,
        }
    }

    fn write_arrow_stream(batch: &RecordBatch) -> Vec<u8> {
        let mut buf = Vec::new();
        let mut writer =
            StreamWriter::try_new(&mut buf, batch.schema().as_ref()).expect("stream writer");
        writer.write(batch).expect("write");
        writer.finish().expect("finish");
        buf
    }

    fn write_arrow_file(batch: &RecordBatch) -> Vec<u8> {
        let mut buf = Vec::new();
        let mut writer =
            FileWriter::try_new(&mut buf, batch.schema().as_ref()).expect("file writer");
        writer.write(batch).expect("write");
        writer.finish().expect("finish");
        buf
    }

    #[test]
    fn arrow_parser_stream_format_yields_records() {
        let schema = Schema::new(vec![
            Field::new("a", DataType::Int64, false),
            Field::new("b", DataType::Int64, false),
        ]);
        let a = Int64Array::from(vec![1_i64, 3]);
        let b = Int64Array::from(vec![2_i64, 4]);
        let batch = RecordBatch::try_new(
            Arc::new(schema),
            vec![Arc::new(a), Arc::new(b)],
        )
        .expect("batch");
        let buf = write_arrow_stream(&batch);
        let reader: Box<dyn ReadSeek> = Box::new(Cursor::new(buf));
        let parser = ArrowParser::new();
        let iter = parser.parse(reader).expect("parse");
        let rows: Vec<_> = iter.collect();
        assert_eq!(rows.len(), 2, "two rows");
        let r0 = rows[0].as_ref().expect("row 0");
        assert_eq!(r0[0].0, "a");
        assert_eq!(numeric_value(&r0[0].1), Some(1.0));
        assert_eq!(r0[1].0, "b");
        assert_eq!(numeric_value(&r0[1].1), Some(2.0));
        let r1 = rows[1].as_ref().expect("row 1");
        assert_eq!(numeric_value(&r1[0].1), Some(3.0));
        assert_eq!(numeric_value(&r1[1].1), Some(4.0));
    }

    #[test]
    fn arrow_parser_float64_column() {
        let schema = Schema::new(vec![
            Field::new("i", DataType::Int64, false),
            Field::new("f", DataType::Float64, false),
        ]);
        let batch = RecordBatch::try_new(
            Arc::new(schema),
            vec![
                Arc::new(Int64Array::from(vec![1_i64])),
                Arc::new(Float64Array::from(vec![2.5])),
            ],
        )
        .expect("batch");
        let buf = write_arrow_stream(&batch);
        let reader: Box<dyn ReadSeek> = Box::new(Cursor::new(buf));
        let iter = ArrowParser::new().parse(reader).expect("parse");
        let rows: Vec<_> = iter.collect();
        assert_eq!(rows.len(), 1);
        assert_eq!(numeric_value(&rows[0].as_ref().expect("row")[0].1), Some(1.0));
        assert_eq!(numeric_value(&rows[0].as_ref().expect("row")[1].1), Some(2.5));
    }

    #[test]
    fn arrow_parser_null_becomes_undefined() {
        let schema = Schema::new(vec![Field::new("a", DataType::Int64, true)]);
        let batch = RecordBatch::try_new(
            Arc::new(schema),
            vec![Arc::new(Int64Array::from(vec![Some(1), None]))],
        )
        .expect("batch");
        let buf = write_arrow_stream(&batch);
        let reader: Box<dyn ReadSeek> = Box::new(Cursor::new(buf));
        let iter = ArrowParser::new().parse(reader).expect("parse");
        let rows: Vec<_> = iter.collect();
        assert_eq!(rows.len(), 2);
        assert_eq!(numeric_value(&rows[0].as_ref().expect("row")[0].1), Some(1.0));
        assert!(matches!(
            rows[1].as_ref().expect("row")[0].1,
            Value::Undefined
        ));
    }

    #[test]
    fn arrow_parser_empty_batch_yields_no_rows() {
        let schema = Schema::new(vec![Field::new("a", DataType::Int64, false)]);
        let batch = RecordBatch::try_new(
            Arc::new(schema),
            vec![Arc::new(Int64Array::from(vec![] as Vec<i64>))],
        )
        .expect("batch");
        let buf = write_arrow_stream(&batch);
        let reader: Box<dyn ReadSeek> = Box::new(Cursor::new(buf));
        let iter = ArrowParser::new().parse(reader).expect("parse");
        let rows: Vec<_> = iter.collect();
        assert_eq!(rows.len(), 0);
    }

    /// Exercises the file-format path (FileReader) in ArrowParser::parse.
    #[test]
    fn arrow_parser_file_format_yields_records() {
        let schema = Schema::new(vec![
            Field::new("p", DataType::Int64, false),
            Field::new("q", DataType::Int64, false),
        ]);
        let batch = RecordBatch::try_new(
            Arc::new(schema),
            vec![
                Arc::new(Int64Array::from(vec![10_i64, 20])),
                Arc::new(Int64Array::from(vec![1_i64, 2])),
            ],
        )
        .expect("batch");
        let buf = write_arrow_file(&batch);
        let reader: Box<dyn ReadSeek> = Box::new(Cursor::new(buf));
        let iter = ArrowParser::new().parse(reader).expect("parse");
        let rows: Vec<_> = iter.collect();
        assert_eq!(rows.len(), 2);
        let r0 = rows[0].as_ref().expect("row 0");
        assert_eq!(r0[0].0, "p");
        assert_eq!(r0[1].0, "q");
        assert_eq!(numeric_value(&r0[0].1), Some(10.0));
        assert_eq!(numeric_value(&r0[1].1), Some(1.0));
        let r1 = rows[1].as_ref().expect("row 1");
        assert_eq!(numeric_value(&r1[0].1), Some(20.0));
        assert_eq!(numeric_value(&r1[1].1), Some(2.0));
    }
}
