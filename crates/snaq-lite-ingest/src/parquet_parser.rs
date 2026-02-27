//! Parquet tabular parser: streams row-by-row from RecordBatches.
//! Requires the full input in memory (Parquet metadata is at end of file); rows are streamed.

use super::ParseError;
use super::ReadSeek;
use super::TabularParser;
use crate::record_batch::row_to_record;
use parquet::arrow::arrow_reader::ParquetRecordBatchReaderBuilder;
use snaq_lite_lang::Record;
use std::io::Read;

/// Parquet parser. Reads the input into memory (Parquet format requires footer access), then yields one [Record] per row from each RecordBatch.
pub struct ParquetParser;

impl ParquetParser {
    pub fn new() -> Self {
        Self
    }
}

impl Default for ParquetParser {
    fn default() -> Self {
        Self::new()
    }
}

impl TabularParser for ParquetParser {
    fn parse(
        &self,
        reader: Box<dyn ReadSeek>,
    ) -> Result<Box<dyn Iterator<Item = Result<Record, ParseError>> + Send>, ParseError> {
        let mut buf = Vec::new();
        reader
            .take(usize::MAX as u64)
            .read_to_end(&mut buf)
            .map_err(|e| ParseError::new(e.to_string()))?;
        let bytes = bytes::Bytes::from(buf);
        let builder = ParquetRecordBatchReaderBuilder::try_new(bytes)
            .map_err(|e| ParseError::new(e.to_string()))?;
        let batch_reader = builder
            .build()
            .map_err(|e| ParseError::new(e.to_string()))?;
        Ok(Box::new(ParquetRowIter {
            batch_reader,
            current_batch: None,
            row_index: 0,
        }))
    }
}

struct ParquetRowIter {
    batch_reader: parquet::arrow::arrow_reader::ParquetRecordBatchReader,
    current_batch: Option<arrow::record_batch::RecordBatch>,
    row_index: usize,
}

impl Iterator for ParquetRowIter {
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
            self.current_batch = match self.batch_reader.next() {
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
    use parquet::arrow::ArrowWriter;
    use snaq_lite_lang::Value;
    use std::io::Cursor;
    use std::sync::Arc;

    fn numeric_value(v: &Value) -> Option<f64> {
        match v {
            Value::Numeric(q) => Some(q.value()),
            _ => None,
        }
    }

    #[test]
    fn parquet_parser_empty_input_returns_err() {
        let reader: Box<dyn ReadSeek> = Box::new(Cursor::new(vec![]));
        let result = ParquetParser::new().parse(reader);
        assert!(result.is_err());
    }

    #[test]
    fn parquet_parser_invalid_bytes_returns_err() {
        let reader: Box<dyn ReadSeek> = Box::new(Cursor::new(b"not parquet".to_vec()));
        let result = ParquetParser::new().parse(reader);
        assert!(result.is_err());
    }

    #[test]
    fn parquet_parser_round_trip_yields_records() {
        let schema = Schema::new(vec![
            Field::new("a", DataType::Int64, false),
            Field::new("b", DataType::Float64, false),
        ]);
        let batch = RecordBatch::try_new(
            Arc::new(schema),
            vec![
                Arc::new(Int64Array::from(vec![1_i64, 3])),
                Arc::new(Float64Array::from(vec![2.0, 4.0])),
            ],
        )
        .expect("batch");
        let mut buffer = Vec::new();
        {
            let mut writer =
                ArrowWriter::try_new(&mut buffer, batch.schema().clone(), None).expect("writer");
            writer.write(&batch).expect("write");
            writer.close().expect("close");
        }
        let reader: Box<dyn ReadSeek> = Box::new(Cursor::new(buffer));
        let iter = ParquetParser::new().parse(reader).expect("parse");
        let rows: Vec<_> = iter.collect();
        assert_eq!(rows.len(), 2);
        let r0 = rows[0].as_ref().expect("row 0");
        assert_eq!(r0[0].0, "a");
        assert_eq!(r0[1].0, "b");
        assert_eq!(numeric_value(&r0[0].1), Some(1.0));
        assert_eq!(numeric_value(&r0[1].1), Some(2.0));
        let r1 = rows[1].as_ref().expect("row 1");
        assert_eq!(numeric_value(&r1[0].1), Some(3.0));
        assert_eq!(numeric_value(&r1[1].1), Some(4.0));
    }
}
