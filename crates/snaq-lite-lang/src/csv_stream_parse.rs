//! CSV line parsing for stream feeders (WASM and native).
//! Delimiter detection, line → record, and BOM stripping. Used by LSP WASM CSV feeder.

use crate::error::{RunError, RunErrorKind};
use crate::map_registry::Record;
use crate::quantity::{Quantity, SnaqNumber};
use crate::unit::Unit;
use crate::symbolic::Value;

/// CSV delimiter: comma or semicolon (semicolon common in European locales).
pub fn csv_delimiter_from_line(line: &str) -> char {
    if line.contains(';') {
        ';'
    } else {
        ','
    }
}

/// Parse one CSV data line into a Record using headers. Empty cell → Undefined; invalid number → Err.
pub fn parse_csv_line_to_record(
    line: &str,
    headers: &[String],
    delimiter: char,
    scalar: &Unit,
) -> Result<Record, RunError> {
    let cells: Vec<&str> = line.split(delimiter).map(|s| s.trim()).collect();
    let mut record = Vec::with_capacity(headers.len());
    for (i, col) in headers.iter().enumerate() {
        let cell = cells.get(i).copied().unwrap_or("");
        let value = if cell.is_empty() {
            Value::Undefined
        } else {
            match cell.parse::<f64>() {
                Ok(n) if n.is_finite() => {
                    Value::Numeric(Quantity::with_number(
                        SnaqNumber::new(n, 0.0),
                        scalar.clone(),
                    ))
                }
                _ => {
                    return Err(RunError::new(RunErrorKind::InvalidArgument(
                        format!("CSV: invalid number in column {col:?}: {cell:?}"),
                    )));
                }
            }
        };
        record.push((col.clone(), value));
    }
    Ok(record)
}

/// Strip UTF-8 BOM from start of buffer if present.
pub fn strip_bom(buffer: &[u8]) -> &[u8] {
    if buffer.len() >= 3 && buffer[0] == 0xEF && buffer[1] == 0xBB && buffer[2] == 0xBF {
        &buffer[3..]
    } else {
        buffer
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn csv_delimiter_comma_when_no_semicolon() {
        assert_eq!(csv_delimiter_from_line("a,b,c"), ',');
        assert_eq!(csv_delimiter_from_line("x"), ',');
    }

    #[test]
    fn csv_delimiter_semicolon_when_semicolon_present() {
        assert_eq!(csv_delimiter_from_line("a;b;c"), ';');
        assert_eq!(csv_delimiter_from_line("a,b;c"), ';');
    }

    #[test]
    fn parse_csv_line_to_record_ok() {
        let scalar = Unit::scalar();
        let headers = vec!["x".to_string(), "y".to_string()];
        let record = parse_csv_line_to_record("1,2", &headers, ',', &scalar).unwrap();
        assert_eq!(record.len(), 2);
        match &record[0].1 {
            Value::Numeric(q) => assert_eq!(q.value(), 1.0),
            _ => panic!("expected numeric"),
        }
        match &record[1].1 {
            Value::Numeric(q) => assert_eq!(q.value(), 2.0),
            _ => panic!("expected numeric"),
        }
    }

    #[test]
    fn parse_csv_line_to_record_empty_cell_undefined() {
        let scalar = Unit::scalar();
        let headers = vec!["a".to_string(), "b".to_string()];
        let record = parse_csv_line_to_record("1,", &headers, ',', &scalar).unwrap();
        assert_eq!(record.len(), 2);
        assert!(matches!(record[1].1, Value::Undefined));
    }

    #[test]
    fn parse_csv_line_to_record_invalid_number_err() {
        let scalar = Unit::scalar();
        let headers = vec!["col".to_string()];
        let err = parse_csv_line_to_record("not a number", &headers, ',', &scalar).unwrap_err();
        assert!(format!("{}", err).contains("invalid number"));
        assert!(format!("{}", err).contains("col"));
    }

    #[test]
    fn parse_csv_line_to_record_trimmed_cells() {
        let scalar = Unit::scalar();
        let headers = vec!["v".to_string()];
        let record = parse_csv_line_to_record("  42  ", &headers, ',', &scalar).unwrap();
        match &record[0].1 {
            Value::Numeric(q) => assert_eq!(q.value(), 42.0),
            _ => panic!("expected numeric"),
        }
    }

    #[test]
    fn parse_csv_line_to_record_semicolon_delimiter() {
        let scalar = Unit::scalar();
        let headers = vec!["a".to_string(), "b".to_string()];
        let record = parse_csv_line_to_record("10;20", &headers, ';', &scalar).unwrap();
        match &record[0].1 {
            Value::Numeric(q) => assert_eq!(q.value(), 10.0),
            _ => panic!("expected numeric"),
        }
        match &record[1].1 {
            Value::Numeric(q) => assert_eq!(q.value(), 20.0),
            _ => panic!("expected numeric"),
        }
    }

    #[test]
    fn parse_csv_line_to_record_rejects_nan_and_infinity() {
        let scalar = Unit::scalar();
        let headers = vec!["v".to_string()];
        let err_nan = parse_csv_line_to_record("NaN", &headers, ',', &scalar).unwrap_err();
        assert!(format!("{}", err_nan).contains("invalid number"));
        let err_inf = parse_csv_line_to_record("inf", &headers, ',', &scalar).unwrap_err();
        assert!(format!("{}", err_inf).contains("invalid number"));
    }

    #[test]
    fn parse_csv_line_to_record_extra_columns_ignored() {
        let scalar = Unit::scalar();
        let headers = vec!["a".to_string(), "b".to_string()];
        let record = parse_csv_line_to_record("1,2,3,4", &headers, ',', &scalar).unwrap();
        assert_eq!(record.len(), 2);
        match &record[0].1 {
            Value::Numeric(q) => assert_eq!(q.value(), 1.0),
            _ => panic!("expected numeric"),
        }
        match &record[1].1 {
            Value::Numeric(q) => assert_eq!(q.value(), 2.0),
            _ => panic!("expected numeric"),
        }
    }

    #[test]
    fn strip_bom_removes_utf8_bom() {
        let with_bom = [0xEFu8, 0xBB, 0xBF, b'a', b'b'];
        let out = strip_bom(&with_bom);
        assert_eq!(out, b"ab");
    }

    #[test]
    fn strip_bom_no_bom_unchanged() {
        let no_bom = b"hello";
        assert_eq!(strip_bom(no_bom), no_bom);
    }

    #[test]
    fn strip_bom_short_buffer_unchanged() {
        let short = [0xEFu8, 0xBB];
        assert_eq!(strip_bom(&short), &short[..]);
    }
}
