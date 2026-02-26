//! Read a file and push newline-delimited numbers as [Chunk]s to a stream sender.
//! Used by the CLI when running with `--stream name=path`.

use snaq_lite_lang::{
    Chunk, Quantity, RunError, RunErrorKind, SnaqNumber, Unit, Value,
};
use std::io::{BufRead, BufReader, Read};
use std::path::Path;

/// Maximum lines per chunk to avoid huge allocations.
const CHUNK_SIZE: usize = 8192;

/// Read the file at `path`, parse newline-delimited numbers, push chunks to `sender`, then drop the sender (EOF).
/// Empty lines are skipped. Invalid lines (non-numeric) yield a stream error: `Err(InvalidArgument(...))`.
/// Returns `Ok(())` on success, or `Err(std::io::Error)` if the file could not be opened or read.
pub fn feed_file_to_sender(
    path: &Path,
    sender: futures::channel::mpsc::UnboundedSender<Chunk>,
) -> Result<(), std::io::Error> {
    let file = std::fs::File::open(path)?;
    let reader = BufReader::new(file);
    feed_read_to_sender(reader, sender);
    Ok(())
}

/// Read from `reader` line by line, parse newline-delimited numbers, push chunks to `sender`, then drop the sender.
/// Used by tests with in-memory readers. Invalid lines yield `Err(InvalidArgument(...))`.
pub fn feed_read_to_sender<R: Read>(
    reader: R,
    sender: futures::channel::mpsc::UnboundedSender<Chunk>,
) {
    let scalar = Unit::scalar();
    let mut chunk = Vec::with_capacity(CHUNK_SIZE);
    let mut lines = BufReader::new(reader).lines();

    while let Some(Ok(line)) = lines.next() {
        let s = line.trim();
        if s.is_empty() {
            continue;
        }
        match s.parse::<f64>() {
            Ok(n) => {
                let q = Quantity::with_number(SnaqNumber::new(n, 0.0), scalar.clone());
                chunk.push(Ok(Some(Value::Numeric(q))));
            }
            Err(_) => {
                chunk.push(Err(RunError::new(RunErrorKind::InvalidArgument(format!(
                    "stream feeder: invalid number: {s:?}"
                )))));
            }
        }
        if chunk.len() >= CHUNK_SIZE {
            if sender.unbounded_send(std::mem::take(&mut chunk)).is_err() {
                return;
            }
            chunk = Vec::with_capacity(CHUNK_SIZE);
        }
    }

    if !chunk.is_empty() {
        let _ = sender.unbounded_send(chunk);
    }
    sender.close_channel();
}

#[cfg(test)]
mod tests {
    use super::*;
    use futures::stream::StreamExt;

    #[test]
    fn feed_read_to_sender_yields_chunks_and_eof() {
        let (tx, mut rx) = futures::channel::mpsc::unbounded();
        feed_read_to_sender("1\n2\n3\n".as_bytes(), tx);

        let mut collected: Chunk = Vec::new();
        while let Some(c) = futures::executor::block_on(rx.next()) {
            collected.extend(c);
        }

        assert_eq!(collected.len(), 3);
        for (i, r) in collected.iter().enumerate() {
            let val = r.as_ref().unwrap().as_ref().unwrap();
            if let Value::Numeric(q) = val {
                assert!((q.value() - (i + 1) as f64).abs() < 1e-10);
            } else {
                panic!("expected numeric");
            }
        }
    }

    #[test]
    fn feed_read_to_sender_skips_empty_lines() {
        let (tx, mut rx) = futures::channel::mpsc::unbounded();
        feed_read_to_sender("1\n\n2\n\n\n3".as_bytes(), tx);

        let mut collected: Chunk = Vec::new();
        while let Some(c) = futures::executor::block_on(rx.next()) {
            collected.extend(c);
        }

        assert_eq!(collected.len(), 3);
    }

    #[test]
    fn feed_read_to_sender_invalid_line_yields_error() {
        let (tx, mut rx) = futures::channel::mpsc::unbounded();
        feed_read_to_sender("1\nfoo\n3".as_bytes(), tx);

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
