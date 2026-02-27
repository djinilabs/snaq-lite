//! Convert Arrow [RecordBatch] to snaq [Record]s (one row at a time).
//! Used by Parquet and Arrow IPC parsers. Feature-gated.

use super::ParseError;
use arrow::array::Array;
use arrow::array::*;
use arrow::datatypes::DataType;
use arrow::record_batch::RecordBatch;
use snaq_lite_lang::{Quantity, Record, SnaqNumber, Unit, Value};

/// Convert one row of a RecordBatch into a [Record] (column name → value).
/// Numeric types become [Value::Numeric]; null or unsupported types become [Value::Undefined].
pub fn row_to_record(batch: &RecordBatch, row_index: usize) -> Result<Record, ParseError> {
    let schema = batch.schema();
    let mut record = Record::with_capacity(batch.num_columns());
    let scalar = Unit::scalar();

    for (col_idx, field) in schema.fields().iter().enumerate() {
        let name = field.name().clone();
        let array = batch.column(col_idx);

        let value = if array.is_null(row_index) {
            Value::Undefined
        } else {
            arrow_scalar_to_value(array, row_index, &scalar).unwrap_or(Value::Undefined)
        };
        record.push((name, value));
    }
    Ok(record)
}

/// Extract a numeric or undefined value from an Arrow array at the given row index.
/// Returns None for unsupported types (we map to Value::Undefined at the caller).
fn arrow_scalar_to_value(
    array: &dyn arrow::array::Array,
    row_index: usize,
    scalar: &Unit,
) -> Option<Value> {
    let n = SnaqNumber::new;
    let q = |v: f64| Value::Numeric(Quantity::with_number(n(v, 0.0), scalar.clone()));

    match array.data_type() {
        DataType::Int8 => {
            let a = array.as_any().downcast_ref::<Int8Array>()?;
            Some(q(f64::from(a.value(row_index))))
        }
        DataType::Int16 => {
            let a = array.as_any().downcast_ref::<Int16Array>()?;
            Some(q(f64::from(a.value(row_index))))
        }
        DataType::Int32 => {
            let a = array.as_any().downcast_ref::<Int32Array>()?;
            Some(q(f64::from(a.value(row_index))))
        }
        DataType::Int64 => {
            let a = array.as_any().downcast_ref::<Int64Array>()?;
            Some(q(a.value(row_index) as f64))
        }
        DataType::UInt8 => {
            let a = array.as_any().downcast_ref::<UInt8Array>()?;
            Some(q(f64::from(a.value(row_index))))
        }
        DataType::UInt16 => {
            let a = array.as_any().downcast_ref::<UInt16Array>()?;
            Some(q(f64::from(a.value(row_index))))
        }
        DataType::UInt32 => {
            let a = array.as_any().downcast_ref::<UInt32Array>()?;
            Some(q(f64::from(a.value(row_index))))
        }
        DataType::UInt64 => {
            let a = array.as_any().downcast_ref::<UInt64Array>()?;
            Some(q(a.value(row_index) as f64))
        }
        DataType::Float32 => {
            let a = array.as_any().downcast_ref::<Float32Array>()?;
            Some(q(f64::from(a.value(row_index))))
        }
        DataType::Float64 => {
            let a = array.as_any().downcast_ref::<Float64Array>()?;
            Some(q(a.value(row_index)))
        }
        _ => None,
    }
}

#[cfg(all(test, feature = "parquet"))]
mod tests {
    use super::*;
    use arrow::array::{Float32Array, Float64Array, Int64Array, StringArray};
    use arrow::datatypes::{DataType, Field, Schema};
    use arrow::record_batch::RecordBatch;
    use snaq_lite_lang::Value;
    use std::sync::Arc;

    fn numeric_value(v: &Value) -> Option<f64> {
        match v {
            Value::Numeric(q) => Some(q.value()),
            _ => None,
        }
    }

    #[test]
    fn row_to_record_numeric_columns() {
        let schema = Schema::new(vec![
            Field::new("x", DataType::Int64, false),
            Field::new("y", DataType::Float64, false),
        ]);
        let batch = RecordBatch::try_new(
            Arc::new(schema),
            vec![
                Arc::new(Int64Array::from(vec![10_i64])),
                Arc::new(Float64Array::from(vec![2.5])),
            ],
        )
        .expect("batch");
        let record = row_to_record(&batch, 0).expect("row");
        assert_eq!(record.len(), 2);
        assert_eq!(record[0].0, "x");
        assert_eq!(numeric_value(&record[0].1), Some(10.0));
        assert_eq!(record[1].0, "y");
        assert_eq!(numeric_value(&record[1].1), Some(2.5));
    }

    #[test]
    fn row_to_record_null_becomes_undefined() {
        let schema = Schema::new(vec![Field::new("a", DataType::Int64, true)]);
        let batch = RecordBatch::try_new(
            Arc::new(schema),
            vec![Arc::new(Int64Array::from(vec![Some(1), None, Some(3)]))],
        )
        .expect("batch");
        let r0 = row_to_record(&batch, 0).expect("row");
        assert_eq!(numeric_value(&r0[0].1), Some(1.0));
        let r1 = row_to_record(&batch, 1).expect("row");
        assert!(matches!(r1[0].1, Value::Undefined));
        let r2 = row_to_record(&batch, 2).expect("row");
        assert_eq!(numeric_value(&r2[0].1), Some(3.0));
    }

    #[test]
    fn row_to_record_unsupported_type_becomes_undefined() {
        let schema = Schema::new(vec![Field::new("label", DataType::Utf8, false)]);
        let batch = RecordBatch::try_new(
            Arc::new(schema),
            vec![Arc::new(StringArray::from(vec!["hello"]))],
        )
        .expect("batch");
        let record = row_to_record(&batch, 0).expect("row");
        assert_eq!(record.len(), 1);
        assert!(matches!(record[0].1, Value::Undefined));
    }

    #[test]
    fn row_to_record_mixed_numeric_and_unsupported() {
        let schema = Schema::new(vec![
            Field::new("n", DataType::Int64, false),
            Field::new("s", DataType::Utf8, false),
            Field::new("f", DataType::Float64, false),
        ]);
        let batch = RecordBatch::try_new(
            Arc::new(schema),
            vec![
                Arc::new(Int64Array::from(vec![42_i64])),
                Arc::new(StringArray::from(vec!["ignored"])),
                Arc::new(Float64Array::from(vec![3.14])),
            ],
        )
        .expect("batch");
        let record = row_to_record(&batch, 0).expect("row");
        assert_eq!(numeric_value(&record[0].1), Some(42.0));
        assert!(matches!(record[1].1, Value::Undefined));
        assert_eq!(numeric_value(&record[2].1), Some(3.14));
    }

    #[test]
    fn row_to_record_float32_becomes_numeric() {
        let schema = Schema::new(vec![Field::new("f32", DataType::Float32, false)]);
        let batch = RecordBatch::try_new(
            Arc::new(schema),
            vec![Arc::new(Float32Array::from(vec![1.5_f32]))],
        )
        .expect("batch");
        let record = row_to_record(&batch, 0).expect("row");
        assert_eq!(record.len(), 1);
        assert_eq!(record[0].0, "f32");
        assert_eq!(numeric_value(&record[0].1), Some(1.5));
    }
}
