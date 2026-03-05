//! Read a file and push newline-delimited numbers as [Chunk]s to a stream sender.
//! Used by the CLI when running with `--stream name=path`.
//! Uses bounded send so the feeder is back-pressured by the consumer.

use snaq_lite_lang::{
    decimal_string_to_quantity, Quantity, RunError, RunErrorKind, SnaqNumber, StreamChunkSender,
    StreamVarianceMode, Unit, Value,
};
use std::io::{BufRead, BufReader, Read};
use std::path::Path;

/// Maximum lines per chunk to avoid huge allocations.
const CHUNK_SIZE: usize = 8192;

/// Read the file at `path`, parse newline-delimited numbers, push chunks to `sender` (awaiting send for back-pressure), then drop the sender (EOF).
/// Empty lines are skipped. Invalid lines (non-numeric) yield a stream error: `Err(InvalidArgument(...))`.
/// If `on_ready` is provided, it is called once after the file is successfully opened.
/// Returns `Ok(())` on success, or `Err(std::io::Error)` if the file could not be opened or read.
pub fn feed_file_to_sender(
    path: &Path,
    sender: StreamChunkSender,
    variance_mode: StreamVarianceMode,
    on_ready: Option<Box<dyn FnOnce() + Send>>,
) -> Result<(), std::io::Error> {
    let file = std::fs::File::open(path)?;
    if let Some(f) = on_ready {
        f();
    }
    let reader = BufReader::new(file);
    feed_read_to_sender(reader, sender, variance_mode);
    Ok(())
}

/// Read from `reader` line by line, parse newline-delimited numbers, push chunks to `sender` (block_on send for back-pressure), then drop the sender.
/// Used by tests with in-memory readers. Invalid lines yield `Err(InvalidArgument(...))`.
pub fn feed_read_to_sender<R: Read>(
    reader: R,
    mut sender: StreamChunkSender,
    variance_mode: StreamVarianceMode,
) {
    use futures::sink::SinkExt;

    let scalar = Unit::scalar();
    let mut chunk = Vec::with_capacity(CHUNK_SIZE);
    let mut lines = BufReader::new(reader).lines();

    while let Some(Ok(line)) = lines.next() {
        let s = line.trim();
        if s.is_empty() {
            continue;
        }
        let (n, variance) = match variance_mode {
            StreamVarianceMode::Zero => match s.parse::<f64>() {
                Ok(v) => (v, 0.0),
                Err(_) => {
                    chunk.push(Err(RunError::new(RunErrorKind::InvalidArgument(format!(
                        "stream feeder: invalid number: {s:?}"
                    )))));
                    if chunk.len() >= CHUNK_SIZE {
                        if futures::executor::block_on(sender.send(std::mem::take(&mut chunk)))
                            .is_err()
                        {
                            return;
                        }
                        chunk = Vec::with_capacity(CHUNK_SIZE);
                    }
                    continue;
                }
            },
            StreamVarianceMode::InferFromDecimalPlaces => match decimal_string_to_quantity(s) {
                Some((v, var)) => (v, var),
                None => {
                    chunk.push(Err(RunError::new(RunErrorKind::InvalidArgument(format!(
                        "stream feeder: invalid number: {s:?}"
                    )))));
                    if chunk.len() >= CHUNK_SIZE {
                        if futures::executor::block_on(sender.send(std::mem::take(&mut chunk)))
                            .is_err()
                        {
                            return;
                        }
                        chunk = Vec::with_capacity(CHUNK_SIZE);
                    }
                    continue;
                }
            },
        };
        let q = Quantity::with_number(SnaqNumber::new(n, variance), scalar.clone());
        chunk.push(Ok(Some(Value::Numeric(q))));
        if chunk.len() >= CHUNK_SIZE {
            if futures::executor::block_on(sender.send(std::mem::take(&mut chunk))).is_err() {
                return;
            }
            chunk = Vec::with_capacity(CHUNK_SIZE);
        }
    }

    if !chunk.is_empty() {
        let _ = futures::executor::block_on(sender.send(chunk));
    }
    drop(sender);
}

#[cfg(test)]
mod tests {
    use super::*;
    use futures::stream::StreamExt;
    use snaq_lite_lang::Chunk;

    #[test]
    fn feed_read_to_sender_yields_chunks_and_eof() {
        let (tx, mut rx) = futures::channel::mpsc::channel(snaq_lite_lang::STREAM_CHANNEL_CAPACITY);
        feed_read_to_sender(
            "1\n2\n3\n".as_bytes(),
            tx,
            StreamVarianceMode::Zero,
        );

        let mut collected: Chunk = Vec::new();
        while let Some(c) = futures::executor::block_on(rx.next()) {
            collected.extend(c);
        }

        assert_eq!(collected.len(), 3);
        for (i, r) in collected.iter().enumerate() {
            let val = r.as_ref().unwrap().as_ref().unwrap();
            if let Value::Numeric(q) = val {
                assert!((q.value() - (i + 1) as f64).abs() < 1e-10);
                assert_eq!(q.variance(), 0.0, "Zero mode must yield variance 0");
            } else {
                panic!("expected numeric");
            }
        }
    }

    #[test]
    fn feed_read_to_sender_skips_empty_lines() {
        let (tx, mut rx) = futures::channel::mpsc::channel(snaq_lite_lang::STREAM_CHANNEL_CAPACITY);
        feed_read_to_sender(
            "1\n\n2\n\n\n3".as_bytes(),
            tx,
            StreamVarianceMode::Zero,
        );

        let mut collected: Chunk = Vec::new();
        while let Some(c) = futures::executor::block_on(rx.next()) {
            collected.extend(c);
        }

        assert_eq!(collected.len(), 3);
    }

    #[test]
    fn feed_read_to_sender_invalid_line_yields_error() {
        let (tx, mut rx) = futures::channel::mpsc::channel(snaq_lite_lang::STREAM_CHANNEL_CAPACITY);
        feed_read_to_sender(
            "1\nfoo\n3".as_bytes(),
            tx,
            StreamVarianceMode::Zero,
        );

        let mut collected: Chunk = Vec::new();
        while let Some(c) = futures::executor::block_on(rx.next()) {
            collected.extend(c);
        }

        assert_eq!(collected.len(), 3);
        assert!(collected[0].as_ref().unwrap().as_ref().is_some());
        assert!(collected[1].as_ref().is_err());
        assert!(collected[2].as_ref().unwrap().as_ref().is_some());
    }

    #[test]
    fn feed_read_to_sender_infer_variance_from_decimal_places() {
        let (tx, mut rx) = futures::channel::mpsc::channel(snaq_lite_lang::STREAM_CHANNEL_CAPACITY);
        feed_read_to_sender(
            "10.5\n10.50\n".as_bytes(),
            tx,
            StreamVarianceMode::InferFromDecimalPlaces,
        );

        let mut collected: Chunk = Vec::new();
        while let Some(c) = futures::executor::block_on(rx.next()) {
            collected.extend(c);
        }
        assert_eq!(collected.len(), 2);
        let v0 = match &collected[0] {
            Ok(Some(Value::Numeric(q))) => q,
            _ => panic!("expected numeric"),
        };
        let v1 = match &collected[1] {
            Ok(Some(Value::Numeric(q))) => q,
            _ => panic!("expected numeric"),
        };
        assert_eq!(v0.value(), 10.5);
        assert_eq!(v1.value(), 10.5);
        assert!(v1.variance() < v0.variance(), "10.50 should have smaller variance than 10.5");
    }

    #[test]
    fn feed_read_to_sender_infer_invalid_line_yields_error() {
        let (tx, mut rx) = futures::channel::mpsc::channel(snaq_lite_lang::STREAM_CHANNEL_CAPACITY);
        feed_read_to_sender(
            "10.5\nnot_a_number\n10.50".as_bytes(),
            tx,
            StreamVarianceMode::InferFromDecimalPlaces,
        );

        let mut collected: Chunk = Vec::new();
        while let Some(c) = futures::executor::block_on(rx.next()) {
            collected.extend(c);
        }
        assert_eq!(collected.len(), 3);
        assert!(collected[0].as_ref().unwrap().as_ref().is_some());
        assert!(collected[1].as_ref().is_err());
        assert!(collected[2].as_ref().unwrap().as_ref().is_some());
    }
}
