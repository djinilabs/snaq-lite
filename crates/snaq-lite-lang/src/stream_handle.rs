//! Stream handle abstraction for external data as asynchronous streams.
//!
//! The Host creates a channel (sender/receiver), registers the receiver under a [StreamHandleId],
//! and injects that id into the Salsa stream input registry under a name used in `$name` in the program. The runtime never holds raw data in the DB; it only
//! holds the handle id. The actual receiver lives in this thread-local registry until
//! [vector_into_stream](crate::queries::vector_into_stream) consumes it.

use crate::error::RunError;
use crate::symbolic::Value;
use futures::stream::Stream;
use std::cell::RefCell;
use std::collections::HashMap;
use std::pin::Pin;
use std::sync::atomic::{AtomicU64, Ordering};
use std::task::{Context, Poll};

/// A batch of values pushed by the Host. Each element is one stream item (or an error).
/// The Host sends chunks of this shape; the runtime flattens them to element-by-element
/// when building the stream for [LazyVector::FromInput](crate::vector::LazyVector::FromInput).
pub type Chunk = Vec<Result<Option<Value>, RunError>>;

/// Opaque id for a registered stream (receiver). Obtained only from [register]; Clone + Eq + Hash so it can live in Salsa inputs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct StreamHandleId(u64);

static NEXT_STREAM_HANDLE_ID: AtomicU64 = AtomicU64::new(0);

fn next_stream_handle_id() -> StreamHandleId {
    StreamHandleId(NEXT_STREAM_HANDLE_ID.fetch_add(1, Ordering::Relaxed))
}

thread_local! {
    static STREAM_REGISTRY: RefCell<HashMap<StreamHandleId, futures::channel::mpsc::UnboundedReceiver<Chunk>>> =
        RefCell::new(HashMap::new());
}

/// Register the receiving end of an unbounded channel. The Host holds the sender and pushes
/// [Chunk]s; dropping the sender signals EOF. Returns the handle id to use in
/// the stream input registry.
///
/// The receiver is single-consumer: the first call to [take_receiver] that uses this id will take the receiver out; subsequent use of the same id will get None.
pub fn register(
    receiver: futures::channel::mpsc::UnboundedReceiver<Chunk>,
) -> StreamHandleId {
    let id = next_stream_handle_id();
    STREAM_REGISTRY.with(|r| r.borrow_mut().insert(id, receiver));
    id
}

/// Take the receiver for this handle, if any. Removes it from the registry so the caller
/// can own it (e.g. wrap it in [ChunkFlattenStream]). Returns None if the handle was already
/// consumed or is unknown.
pub fn take_receiver(
    id: StreamHandleId,
) -> Option<futures::channel::mpsc::UnboundedReceiver<Chunk>> {
    STREAM_REGISTRY.with(|r| r.borrow_mut().remove(&id))
}

/// Stream that flattens chunks to elements. Used when we own the receiver.
/// Empty chunks (zero elements) are skipped and the next chunk is requested; they produce no items.
pub struct ChunkFlattenStream {
    receiver: Option<futures::channel::mpsc::UnboundedReceiver<Chunk>>,
    buffer: Vec<Result<Option<Value>, RunError>>,
    index: usize,
}

impl ChunkFlattenStream {
    pub fn new(receiver: futures::channel::mpsc::UnboundedReceiver<Chunk>) -> Self {
        Self {
            receiver: Some(receiver),
            buffer: Vec::new(),
            index: 0,
        }
    }
}

impl Stream for ChunkFlattenStream {
    type Item = Result<Option<Value>, RunError>;

    fn poll_next(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Option<Self::Item>> {
        let this = self.get_mut();
        if this.index < this.buffer.len() {
            let item = this.buffer[this.index].clone();
            this.index += 1;
            return Poll::Ready(Some(item));
        }
        this.buffer.clear();
        this.index = 0;
        let rx = match &mut this.receiver {
            Some(rx) => rx,
            None => return Poll::Ready(None),
        };
        match Pin::new(rx).poll_next(cx) {
            Poll::Ready(Some(chunk)) => {
                this.buffer = chunk;
                if this.buffer.is_empty() {
                    // Empty chunk: poll again for more
                    return Self::poll_next(Pin::new(this), cx);
                }
                let item = this.buffer[0].clone();
                this.index = 1;
                Poll::Ready(Some(item))
            }
            Poll::Ready(None) => {
                this.receiver = None;
                Poll::Ready(None)
            }
            Poll::Pending => Poll::Pending,
        }
    }
}

impl Unpin for ChunkFlattenStream {}
