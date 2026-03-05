//! Dispatch stream feeding by file format: tabular (CSV, etc.) vs newline-delimited numbers.
//! Uses [snaq_lite_ingest] for format detection and tabular parsing.
//! Uses bounded send so the feeder is back-pressured by the consumer.

use crate::stream_feeder;
use snaq_lite_ingest::{detect_format, parse_tabular, ReadSeek};
use snaq_lite_lang::{
    record_to_chunk_element, RunError, RunErrorKind, StreamChunkSender, StreamVarianceMode,
};
use std::path::Path;

/// Maximum rows per chunk (tabular) to avoid huge allocations.
const CHUNK_SIZE: usize = 8192;

/// Feed the file at `path` into the stream sender. Format is detected from the path (extension).
/// Tabular formats (e.g. CSV) yield one map (row) per record; otherwise newline-delimited numbers.
/// If `on_ready` is provided, it is called once after the file is successfully opened (so the consumer can start).
/// Returns `Ok(())` on success, or `Err(std::io::Error)` if the file could not be opened.
pub fn feed_stream_file_to_sender(
    path: &Path,
    sender: StreamChunkSender,
    variance_mode: StreamVarianceMode,
    on_ready: Option<Box<dyn FnOnce() + Send>>,
) -> Result<(), std::io::Error> {
    let format = detect_format(path, None);

    if format.is_tabular() && format.is_supported() {
        feed_tabular_to_sender(path, sender, variance_mode, on_ready)
    } else {
        stream_feeder::feed_file_to_sender(path, sender, variance_mode, on_ready)
    }
}

/// Open file, parse as tabular (e.g. CSV), push records as chunk elements (await send for back-pressure), then drop sender.
fn feed_tabular_to_sender(
    path: &Path,
    mut sender: StreamChunkSender,
    variance_mode: StreamVarianceMode,
    on_ready: Option<Box<dyn FnOnce() + Send>>,
) -> Result<(), std::io::Error> {
    use futures::sink::SinkExt;

    let file = std::fs::File::open(path)?;
    if let Some(f) = on_ready {
        f();
    }
    let format = detect_format(path, None);
    let reader: Box<dyn ReadSeek> = Box::new(file);

    let iter = match parse_tabular(format, reader, variance_mode) {
        Ok(it) => it,
        Err(e) => {
            let run_err = RunError::new(RunErrorKind::InvalidArgument(e.to_string()));
            let _ = futures::executor::block_on(sender.send(vec![Err(run_err)]));
            drop(sender);
            return Ok(());
        }
    };

    let mut chunk = Vec::with_capacity(CHUNK_SIZE);
    for result in iter {
        let elem = match result {
            Ok(record) => record_to_chunk_element(record),
            Err(parse_err) => Err(RunError::new(RunErrorKind::InvalidArgument(
                parse_err.to_string(),
            ))),
        };
        chunk.push(elem);
        if chunk.len() >= CHUNK_SIZE {
            if futures::executor::block_on(sender.send(std::mem::take(&mut chunk))).is_err() {
                drop(sender);
                return Ok(());
            }
            chunk = Vec::with_capacity(CHUNK_SIZE);
        }
    }
    if !chunk.is_empty() {
        let _ = futures::executor::block_on(sender.send(chunk));
    }
    drop(sender);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use futures::stream::StreamExt;
    use snaq_lite_lang::{RunError, RunErrorKind, Value};

    fn numeric_value(v: &Value) -> Option<f64> {
        match v {
            Value::Numeric(q) => Some(q.value()),
            _ => None,
        }
    }

    /// Write contents to a temp file with the given extension, feed it through dispatch, collect all chunk elements, remove the file. `unique` should differ per test so parallel runs do not clash.
    fn feed_temp_file_and_collect(
        extension: &str,
        contents: &str,
        unique: &str,
    ) -> Vec<Result<Option<Value>, RunError>> {
        feed_temp_file_and_collect_with_mode(extension, contents, unique, StreamVarianceMode::Zero)
    }

    fn feed_temp_file_and_collect_with_mode(
        extension: &str,
        contents: &str,
        unique: &str,
        variance_mode: StreamVarianceMode,
    ) -> Vec<Result<Option<Value>, RunError>> {
        let tmp = std::env::temp_dir().join(format!(
            "snaq_dispatch_{}_{}.{}",
            std::process::id(),
            unique,
            extension
        ));
        std::fs::write(&tmp, contents).expect("write");
        let (tx, mut rx) =
            futures::channel::mpsc::channel(snaq_lite_lang::STREAM_CHANNEL_CAPACITY);
        feed_stream_file_to_sender(&tmp, tx, variance_mode, None).expect("feed");
        let _ = std::fs::remove_file(&tmp);
        let mut chunks = Vec::new();
        while let Some(chunk) = futures::executor::block_on(rx.next()) {
            chunks.push(chunk);
        }
        chunks.into_iter().flatten().collect()
    }

    fn numeric_variance(v: &Value) -> Option<f64> {
        match v {
            Value::Numeric(q) => Some(q.variance()),
            _ => None,
        }
    }

    #[test]
    fn feed_tabular_csv_to_sender_yields_map_elements() {
        let flat = feed_temp_file_and_collect("csv", "a,b\n1,2\n3,4", "maps");
        assert_eq!(flat.len(), 2, "two rows");
        for (i, r) in flat.iter().enumerate() {
            let val = r.as_ref().expect("no error").as_ref().expect("some value");
            let id = match val {
                Value::Map(id) => *id,
                _ => panic!("expected Map"),
            };
            let a = snaq_lite_lang::map_registry::get_key(id, "a").and_then(|v| numeric_value(&v));
            let b = snaq_lite_lang::map_registry::get_key(id, "b").and_then(|v| numeric_value(&v));
            if i == 0 {
                assert_eq!(a, Some(1.0));
                assert_eq!(b, Some(2.0));
            } else {
                assert_eq!(a, Some(3.0));
                assert_eq!(b, Some(4.0));
            }
        }
    }

    #[test]
    fn feed_stream_file_to_sender_txt_uses_numeric_feeder() {
        let flat = feed_temp_file_and_collect("txt", "1\n2\n3\n", "numeric");
        assert_eq!(flat.len(), 3, "three numeric elements");
        for r in &flat {
            let val = r.as_ref().expect("no error").as_ref().expect("some value");
            assert!(matches!(val, Value::Numeric(_)), "expected numeric, got {val:?}");
        }
        assert_eq!(numeric_value(flat[0].as_ref().unwrap().as_ref().unwrap()), Some(1.0));
        assert_eq!(numeric_value(flat[1].as_ref().unwrap().as_ref().unwrap()), Some(2.0));
        assert_eq!(numeric_value(flat[2].as_ref().unwrap().as_ref().unwrap()), Some(3.0));
    }

    #[test]
    fn feed_tabular_csv_headers_only_yields_empty_stream() {
        let flat = feed_temp_file_and_collect("csv", "a,b\n", "empty");
        assert!(flat.is_empty(), "headers-only CSV should yield no elements");
    }

    #[test]
    fn feed_tabular_csv_invalid_number_yields_error_in_stream() {
        let flat = feed_temp_file_and_collect("csv", "a,b\n1,not_a_number\n", "badcell");
        assert_eq!(flat.len(), 1, "one element (the error)");
        assert!(flat[0].is_err());
        let run_err = flat[0].as_ref().unwrap_err();
        assert!(matches!(run_err.kind, RunErrorKind::InvalidArgument(_)));
        assert!(run_err.to_string().contains("invalid number"));
    }

    #[test]
    fn feed_tabular_csv_with_infer_variance_yields_different_variances() {
        let flat = feed_temp_file_and_collect_with_mode(
            "csv",
            "a,b\n10.5,10.50",
            "infer_var",
            StreamVarianceMode::InferFromDecimalPlaces,
        );
        assert_eq!(flat.len(), 1, "one row");
        let val = flat[0].as_ref().expect("no error").as_ref().expect("some value");
        let id = match val {
            Value::Map(id) => *id,
            _ => panic!("expected Map"),
        };
        let va = snaq_lite_lang::map_registry::get_key(id, "a");
        let vb = snaq_lite_lang::map_registry::get_key(id, "b");
        let var_a = va.and_then(|v| numeric_variance(&v));
        let var_b = vb.and_then(|v| numeric_variance(&v));
        assert!(var_a.is_some() && var_b.is_some(), "both columns numeric");
        assert!(var_b.unwrap() < var_a.unwrap(), "10.50 should have smaller variance than 10.5");
    }
}
