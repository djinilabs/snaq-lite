//! Stream handle abstraction for external data as asynchronous streams.
//!
//! The Host creates a channel (sender/receiver), registers the receiver under a [StreamHandleId],
//! and injects that id into the Salsa stream input registry under a name used in `$name` in the program. The runtime never holds raw data in the DB; it only
//! holds the handle id. The actual receiver lives in this thread-local registry until
//! [vector_into_stream](crate::queries::vector_into_stream) consumes it.
//!
//! The channel is **bounded** so that feeders apply back-pressure: when the consumer is slow,
//! [Sender::send] will yield until there is capacity.

use crate::error::RunError;
use crate::symbolic::Value;
use futures::stream::Stream;
use std::cell::RefCell;
use std::collections::HashMap;
use std::pin::Pin;
use std::sync::atomic::{AtomicU64, Ordering};
use std::task::{Context, Poll};

/// Capacity of the stream channel. When full, the feeder blocks on send (back-pressure).
pub const STREAM_CHANNEL_CAPACITY: usize = 4;

/// A batch of values pushed by the Host. Each element is one stream item (or an error).
/// The Host sends chunks of this shape; the runtime flattens them to element-by-element
/// when building the stream for [LazyVector::FromInput](crate::vector::LazyVector::FromInput).
pub type Chunk = Vec<Result<Option<Value>, RunError>>;

/// Bounded sender for stream chunks. Use [futures::SinkExt::send] (or [Sender::send]) in async context for back-pressure.
pub type StreamChunkSender = futures::channel::mpsc::Sender<Chunk>;

/// Bounded receiver for stream chunks.
pub type StreamChunkReceiver = futures::channel::mpsc::Receiver<Chunk>;

/// Opaque id for a registered stream (receiver). Obtained only from [register]; Clone + Eq + Hash so it can live in Salsa inputs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct StreamHandleId(u64);

static NEXT_STREAM_HANDLE_ID: AtomicU64 = AtomicU64::new(0);

fn next_stream_handle_id() -> StreamHandleId {
    StreamHandleId(NEXT_STREAM_HANDLE_ID.fetch_add(1, Ordering::Relaxed))
}

thread_local! {
    static STREAM_REGISTRY: RefCell<HashMap<StreamHandleId, StreamChunkReceiver>> =
        RefCell::new(HashMap::new());
}

/// Create a new stream input: allocates a **bounded** channel, registers the receiver, and returns
/// the handle id and the sender. The Host uses the sender to push [Chunk]s; use `send(chunk).await`
/// so that when the channel is full the feeder yields (back-pressure). Dropping the sender signals EOF.
///
/// The receiver is single-consumer: the first call to [take_receiver] that uses this id
/// will take the receiver out; subsequent use of the same id will get None.
pub fn create_stream_input() -> (StreamHandleId, StreamChunkSender) {
    let (tx, rx) = futures::channel::mpsc::channel(STREAM_CHANNEL_CAPACITY);
    let id = register(rx);
    (id, tx)
}

/// Register the receiving end of the bounded channel. The Host holds the sender and pushes
/// [Chunk]s; dropping the sender signals EOF. Returns the handle id to use in
/// the stream input registry.
///
/// The receiver is single-consumer: the first call to [take_receiver] that uses this id will take the receiver out; subsequent use of the same id will get None.
pub fn register(receiver: StreamChunkReceiver) -> StreamHandleId {
    let id = next_stream_handle_id();
    STREAM_REGISTRY.with(|r| r.borrow_mut().insert(id, receiver));
    id
}

/// Take the receiver for this handle, if any. Removes it from the registry so the caller
/// can own it (e.g. wrap it in [ChunkFlattenStream]). Returns None if the handle was already
/// consumed or is unknown.
pub fn take_receiver(id: StreamHandleId) -> Option<StreamChunkReceiver> {
    STREAM_REGISTRY.with(|r| r.borrow_mut().remove(&id))
}

/// Stream that flattens chunks to elements. Used when we own the receiver.
/// Empty chunks (zero elements) are skipped and the next chunk is requested; they produce no items.
pub struct ChunkFlattenStream {
    receiver: Option<StreamChunkReceiver>,
    buffer: Vec<Result<Option<Value>, RunError>>,
    index: usize,
}

impl ChunkFlattenStream {
    pub fn new(receiver: StreamChunkReceiver) -> Self {
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
