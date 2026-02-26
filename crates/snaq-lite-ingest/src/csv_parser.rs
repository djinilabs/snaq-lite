//! CSV tabular parser: first row = headers, rest = rows; cells → numeric or undefined.

use super::ParseError;
use super::TabularParser;
use snaq_lite_lang::{
    Quantity, Record, SnaqNumber, Unit, Value,
};
use std::io::Read;

/// CSV parser. First row is headers; each data row becomes a [Record] (column name → value).
pub struct CsvParser;

impl CsvParser {
    pub fn new() -> Self {
        Self
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
        reader: Box<dyn Read + Send>,
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
        let iter = CsvRowIter {
            inner: rdr.into_records(),
            headers,
            scalar,
        };
        Ok(Box::new(iter))
    }
}

struct CsvRowIter<R> {
    inner: csv::StringRecordsIntoIter<R>,
    headers: Vec<String>,
    scalar: Unit,
}

impl<R: Read + Send> Iterator for CsvRowIter<R> {
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
                        match s.parse::<f64>() {
                            Ok(n) => Value::Numeric(Quantity::with_number(
                                SnaqNumber::new(n, 0.0),
                                self.scalar.clone(),
                            )),
                            Err(_) => {
                                return Some(Err(ParseError::new(format!(
                                    "stream feeder: invalid number: {s:?}"
                                ))));
                            }
                        }
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

    fn numeric_value(v: &Value) -> Option<f64> {
        match v {
            Value::Numeric(q) => Some(q.value()),
            _ => None,
        }
    }

    #[test]
    fn csv_parser_headers_and_rows() {
        let csv = "a,b,c\n1,2,3\n4,5,6";
        let parser = CsvParser::new();
        let iter = parser.parse(Box::new(csv.as_bytes())).expect("parse");
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
        let iter = parser.parse(Box::new(csv.as_bytes())).expect("parse");
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
        let iter = parser.parse(Box::new(csv.as_bytes())).expect("parse");
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
        let iter = parser.parse(Box::new(csv.as_bytes())).expect("parse");
        let rows: Vec<_> = iter.collect();
        assert_eq!(rows.len(), 0);
    }

    #[test]
    fn csv_parser_single_data_row() {
        let csv = "col\n42";
        let parser = CsvParser::new();
        let iter = parser.parse(Box::new(csv.as_bytes())).expect("parse");
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
        let iter = parser.parse(Box::new(csv.as_bytes())).expect("parse");
        let rows: Vec<_> = iter.collect();
        assert_eq!(rows.len(), 1);
        let r = rows[0].as_ref().expect("row");
        assert_eq!(numeric_value(&r[0].1), Some(1.0));
        assert_eq!(numeric_value(&r[1].1), Some(2.0));
    }

    #[test]
    fn csv_parser_empty_file_returns_err() {
        let parser = CsvParser::new();
        let result = parser.parse(Box::new(std::io::empty()));
        let err = match result {
            Err(e) => e,
            Ok(_) => panic!("expected Err for empty CSV file"),
        };
        assert!(err.to_string().contains("header") || err.to_string().contains("CSV"));
    }
}
