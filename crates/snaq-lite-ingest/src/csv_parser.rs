//! CSV tabular parser: first row = headers, rest = rows; cells → numeric or undefined.

use super::ParseError;
use super::TabularParser;
use snaq_lite_lang::{
    decimal_string_to_quantity, Quantity, Record, SnaqNumber, StreamVarianceMode, Unit, Value,
};
use super::ReadSeek;
use std::io::{Read, Seek};

/// CSV parser. First row is headers; each data row becomes a [Record] (column name → value).
pub struct CsvParser {
    variance_mode: StreamVarianceMode,
}

impl CsvParser {
    pub fn new() -> Self {
        Self {
            variance_mode: StreamVarianceMode::Zero,
        }
    }

    /// Parser that infers variance from decimal places in cell text when parsing numbers.
    pub fn with_variance_mode(mode: StreamVarianceMode) -> Self {
        Self {
            variance_mode: mode,
        }
    }
}

impl Default for CsvParser {
    fn default() -> Self {
        Self::new()
    }
}

impl TabularParser for CsvParser {
    fn parse(
        &self,
        reader: Box<dyn ReadSeek>,
    ) -> Result<Box<dyn Iterator<Item = Result<Record, ParseError>> + Send>, ParseError> {
        let mut rdr = csv::ReaderBuilder::new()
            .has_headers(true)
            .trim(csv::Trim::All)
            .from_reader(reader);
        let headers: Vec<String> = rdr
            .headers()
            .map_err(|e| ParseError::new(e.to_string()))?
            .iter()
            .map(|s| s.to_string())
            .collect();
        if headers.is_empty() {
            return Err(ParseError::new("CSV has no headers"));
        }
        let scalar = Unit::scalar();
        let variance_mode = self.variance_mode;
        let iter = CsvRowIter {
            inner: rdr.into_records(),
            headers,
            scalar,
            variance_mode,
        };
        Ok(Box::new(iter))
    }
}

struct CsvRowIter<R> {
    inner: csv::StringRecordsIntoIter<R>,
    headers: Vec<String>,
    scalar: Unit,
    variance_mode: StreamVarianceMode,
}

impl<R: Read + Seek + Send> Iterator for CsvRowIter<R> {
    type Item = Result<Record, ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        let record = self.inner.next()?;
        match record {
            Ok(string_record) => {
                let mut row = Record::with_capacity(self.headers.len());
                for (i, name) in self.headers.iter().enumerate() {
                    let s = string_record.get(i).unwrap_or("").trim();
                    let value = if s.is_empty() {
                        Value::Undefined
                    } else {
                        let (n, variance) = match self.variance_mode {
                            StreamVarianceMode::Zero => {
                                match s.parse::<f64>() {
                                    Ok(v) => (v, 0.0),
                                    Err(_) => {
                                        return Some(Err(ParseError::new(format!(
                                            "stream feeder: invalid number: {s:?}"
                                        ))));
                                    }
                                }
                            }
                            StreamVarianceMode::InferFromDecimalPlaces => {
                                match decimal_string_to_quantity(s) {
                                    Some((v, var)) => (v, var),
                                    None => {
                                        return Some(Err(ParseError::new(format!(
                                            "stream feeder: invalid number: {s:?}"
                                        ))));
                                    }
                                }
                            }
                        };
                        Value::Numeric(Quantity::with_number(
                            SnaqNumber::new(n, variance),
                            self.scalar.clone(),
                        ))
                    };
                    row.push((name.clone(), value));
                }
                Some(Ok(row))
            }
            Err(e) => Some(Err(ParseError::new(e.to_string()))),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snaq_lite_lang::Value;
    use std::io::Cursor;

    fn numeric_value(v: &Value) -> Option<f64> {
        match v {
            Value::Numeric(q) => Some(q.value()),
            _ => None,
        }
    }

    fn reader_from_bytes(b: &[u8]) -> Box<dyn ReadSeek> {
        Box::new(Cursor::new(b.to_vec()))
    }

    #[test]
    fn csv_parser_headers_and_rows() {
        let csv = "a,b,c\n1,2,3\n4,5,6";
        let parser = CsvParser::new();
        let iter = parser.parse(reader_from_bytes(csv.as_bytes())).expect("parse");
        let rows: Vec<_> = iter.collect();
        assert_eq!(rows.len(), 2);
        let r0 = rows[0].as_ref().expect("row 0");
        assert_eq!(r0.len(), 3);
        assert_eq!(numeric_value(&r0[0].1), Some(1.0));
        assert_eq!(numeric_value(&r0[1].1), Some(2.0));
        assert_eq!(numeric_value(&r0[2].1), Some(3.0));
        let r1 = rows[1].as_ref().expect("row 1");
        assert_eq!(numeric_value(&r1[0].1), Some(4.0));
        assert_eq!(numeric_value(&r1[1].1), Some(5.0));
        assert_eq!(numeric_value(&r1[2].1), Some(6.0));
    }

    #[test]
    fn csv_parser_empty_cell_is_undefined() {
        let csv = "x,y\n1,\n,2";
        let parser = CsvParser::new();
        let iter = parser.parse(reader_from_bytes(csv.as_bytes())).expect("parse");
        let rows: Vec<_> = iter.collect();
        assert_eq!(rows.len(), 2);
        let r0 = rows[0].as_ref().expect("row 0");
        assert_eq!(numeric_value(&r0[0].1), Some(1.0));
        assert!(matches!(&r0[1].1, Value::Undefined));
        let r1 = rows[1].as_ref().expect("row 1");
        assert!(matches!(&r1[0].1, Value::Undefined));
        assert_eq!(numeric_value(&r1[1].1), Some(2.0));
    }

    #[test]
    fn csv_parser_invalid_number_in_cell_returns_err() {
        let csv = "a,b\n1,not_a_number";
        let parser = CsvParser::new();
        let iter = parser.parse(reader_from_bytes(csv.as_bytes())).expect("parse");
        let rows: Vec<_> = iter.collect();
        assert_eq!(rows.len(), 1);
        assert!(rows[0].is_err());
        let err = rows[0].as_ref().unwrap_err();
        assert!(err.to_string().contains("invalid number"));
    }

    #[test]
    fn csv_parser_headers_only_yields_zero_rows() {
        let csv = "x,y\n";
        let parser = CsvParser::new();
        let iter = parser.parse(reader_from_bytes(csv.as_bytes())).expect("parse");
        let rows: Vec<_> = iter.collect();
        assert_eq!(rows.len(), 0);
    }

    #[test]
    fn csv_parser_single_data_row() {
        let csv = "col\n42";
        let parser = CsvParser::new();
        let iter = parser.parse(reader_from_bytes(csv.as_bytes())).expect("parse");
        let rows: Vec<_> = iter.collect();
        assert_eq!(rows.len(), 1);
        let r = rows[0].as_ref().expect("row");
        assert_eq!(r[0].0, "col");
        assert_eq!(numeric_value(&r[0].1), Some(42.0));
    }

    #[test]
    fn csv_parser_trimmed_whitespace_in_cells() {
        let csv = "a,b\n  1  ,  2  ";
        let parser = CsvParser::new();
        let iter = parser.parse(reader_from_bytes(csv.as_bytes())).expect("parse");
        let rows: Vec<_> = iter.collect();
        assert_eq!(rows.len(), 1);
        let r = rows[0].as_ref().expect("row");
        assert_eq!(numeric_value(&r[0].1), Some(1.0));
        assert_eq!(numeric_value(&r[1].1), Some(2.0));
    }

    #[test]
    fn csv_parser_empty_file_returns_err() {
        let parser = CsvParser::new();
        let result = parser.parse(Box::new(Cursor::new(vec![])));
        let err = match result {
            Err(e) => e,
            Ok(_) => panic!("expected Err for empty CSV file"),
        };
        assert!(err.to_string().contains("header") || err.to_string().contains("CSV"));
    }

    fn numeric_variance(v: &Value) -> Option<f64> {
        match v {
            Value::Numeric(q) => Some(q.variance()),
            _ => None,
        }
    }

    #[test]
    fn csv_parser_zero_mode_variance_is_zero() {
        let csv = "x,y\n1,2.5";
        let parser = CsvParser::new();
        let iter = parser.parse(reader_from_bytes(csv.as_bytes())).expect("parse");
        let rows: Vec<_> = iter.collect();
        assert_eq!(rows.len(), 1);
        let r0 = rows[0].as_ref().expect("row 0");
        assert_eq!(numeric_value(&r0[0].1), Some(1.0));
        assert_eq!(numeric_value(&r0[1].1), Some(2.5));
        assert_eq!(numeric_variance(&r0[0].1), Some(0.0));
        assert_eq!(numeric_variance(&r0[1].1), Some(0.0));
    }

    #[test]
    fn csv_parser_infer_variance_from_decimal_places() {
        let csv = "a,b\n10.5,10.50";
        let parser = CsvParser::with_variance_mode(StreamVarianceMode::InferFromDecimalPlaces);
        let iter = parser.parse(reader_from_bytes(csv.as_bytes())).expect("parse");
        let rows: Vec<_> = iter.collect();
        assert_eq!(rows.len(), 1);
        let r0 = rows[0].as_ref().expect("row 0");
        assert_eq!(numeric_value(&r0[0].1), Some(10.5));
        assert_eq!(numeric_value(&r0[1].1), Some(10.5));
        let var_a = numeric_variance(&r0[0].1).expect("numeric");
        let var_b = numeric_variance(&r0[1].1).expect("numeric");
        assert!(var_b < var_a, "10.50 should have smaller variance than 10.5");
    }
}
