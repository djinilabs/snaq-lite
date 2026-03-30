//! Streaming evaluation boundary for the LSP (slice/path/fanout).
//!
//! - **Native:** same-thread work. Handlers call [`resolve_path_blocking`] / [`collect_slice_window_blocking`]
//!   so tower-lsp futures stay `Send`. Graph fanout uses [`feed_fanout_batch_blocking`].
//! - **WASM:** `fetch_result_slice` sends slice/path work to a `spawn_local` worker via [`RuntimeHandle`];
//!   graph fanout still uses [`feed_fanout_batch_blocking`] on the LSP task (lang sync helper).

use crate::pubsub::PathSegment;
use snaq_lite_lang::{LazyVector, RunError, StreamChunkSender, UnitRegistry, Value};
use std::collections::HashMap;
use tower_lsp::lsp_types::Url;

#[cfg(target_arch = "wasm32")]
use futures::channel::{mpsc, oneshot};
#[cfg(target_arch = "wasm32")]
use futures::StreamExt;

#[cfg(target_arch = "wasm32")]
/// Requests processed sequentially on the WASM runtime worker.
pub enum RuntimeRequest {
    Ping {
        reply: oneshot::Sender<()>,
    },
    ResolvePath {
        value: Value,
        path: Vec<PathSegment>,
        db: salsa::DatabaseImpl,
        unit_registry: UnitRegistry,
        reply: oneshot::Sender<Option<Value>>,
    },
    CollectSliceWindow {
        db: salsa::DatabaseImpl,
        inner: LazyVector,
        offset: usize,
        limit: usize,
        unit_registry: UnitRegistry,
        reply: oneshot::Sender<(u64, Vec<Result<Option<Value>, RunError>>)>,
    },
    FeedFanout {
        value: Value,
        db: salsa::DatabaseImpl,
        senders: Vec<StreamChunkSender>,
        unit_registry: UnitRegistry,
        reply: oneshot::Sender<()>,
    },
}

pub(crate) async fn resolve_path_async(
    value: &Value,
    path: &[PathSegment],
    db: &salsa::DatabaseImpl,
) -> Option<Value> {
    use snaq_lite_lang::map_registry;
    let mut current = value.clone();
    for segment in path {
        current = match (&current, segment) {
            (Value::Vector(v), PathSegment::Index(i)) => {
                let idx = *i as usize;
                let slice = LazyVector::Take {
                    source: Box::new(v.inner.clone()),
                    start: idx,
                    length: 1,
                };
                match snaq_lite_lang::next_vector_item_streaming_async(db, slice).await {
                    Some(Ok(Some(val))) => val,
                    _ => return None,
                }
            }
            (Value::Map(id), PathSegment::Key(k)) => map_registry::get_key(*id, k)?.clone(),
            _ => return None,
        };
    }
    Some(current)
}

fn known_total_for_slice(inner: &LazyVector) -> Option<u64> {
    crate::vector_slice::known_lazy_vector_len(inner).map(|n| n as u64)
}

/// Native: path resolution without storing a `!Send` future in tower-lsp handler state machines.
#[cfg(not(target_arch = "wasm32"))]
pub(crate) fn resolve_path_blocking(
    value: &Value,
    path: &[PathSegment],
    db: &salsa::DatabaseImpl,
    unit_registry: UnitRegistry,
) -> Option<Value> {
    snaq_lite_lang::set_eval_registry(unit_registry);
    futures::executor::block_on(resolve_path_async(value, path, db))
}

/// Native: slice window collection for the same reason as [`resolve_path_blocking`].
#[cfg(not(target_arch = "wasm32"))]
pub(crate) fn collect_slice_window_blocking(
    db: salsa::DatabaseImpl,
    inner: LazyVector,
    offset: usize,
    limit: usize,
    unit_registry: UnitRegistry,
) -> (u64, Vec<Result<Option<Value>, RunError>>) {
    snaq_lite_lang::set_eval_registry(unit_registry);
    let known_total = known_total_for_slice(&inner);
    futures::executor::block_on(snaq_lite_lang::collect_vector_slice_window_streaming_async(
        &db, inner, offset, limit, known_total,
    ))
}

/// Graph edge fan-out: feed each upstream value to its downstream chunk senders.
///
/// Centralizes fanout so `lib.rs` does not call `feed_value_to_senders_streaming` directly (plan
/// Phase 3 guard). Uses the lang sync helper (inner `block_on` of async streaming).
pub(crate) fn feed_fanout_batch_blocking(
    unit_registry: UnitRegistry,
    senders_by_source: HashMap<Url, Vec<StreamChunkSender>>,
    output_values: &HashMap<Url, (Value, salsa::DatabaseImpl)>,
) {
    snaq_lite_lang::set_eval_registry(unit_registry);
    for (source_uri, senders) in senders_by_source {
        let Some((value, db)) = output_values.get(&source_uri) else {
            continue;
        };
        snaq_lite_lang::feed_value_to_senders_streaming(value, db, senders);
    }
}

#[cfg(target_arch = "wasm32")]
async fn runtime_loop(mut rx: mpsc::UnboundedReceiver<RuntimeRequest>) {
    while let Some(req) = rx.next().await {
        match req {
            RuntimeRequest::Ping { reply } => {
                let _ = reply.send(());
            }
            RuntimeRequest::ResolvePath {
                value,
                path,
                db,
                unit_registry,
                reply,
            } => {
                snaq_lite_lang::set_eval_registry(unit_registry);
                let out = resolve_path_async(&value, &path, &db).await;
                let _ = reply.send(out);
            }
            RuntimeRequest::CollectSliceWindow {
                db,
                inner,
                offset,
                limit,
                unit_registry,
                reply,
            } => {
                snaq_lite_lang::set_eval_registry(unit_registry);
                let known_total = known_total_for_slice(&inner);
                let out = snaq_lite_lang::collect_vector_slice_window_streaming_async(
                    &db, inner, offset, limit, known_total,
                )
                .await;
                let _ = reply.send(out);
            }
            RuntimeRequest::FeedFanout {
                value,
                db,
                senders,
                unit_registry,
                reply,
            } => {
                snaq_lite_lang::set_eval_registry(unit_registry);
                snaq_lite_lang::feed_value_to_senders_streaming_async(&value, &db, senders).await;
                let _ = reply.send(());
            }
        }
    }
}

/// Cloneable handle: native is a zero-sized inline executor; WASM holds a channel to `spawn_local` worker.
#[derive(Clone)]
pub struct RuntimeHandle {
    #[cfg(target_arch = "wasm32")]
    tx: mpsc::UnboundedSender<RuntimeRequest>,
}

impl RuntimeHandle {
    pub async fn ping(&self) {
        #[cfg(not(target_arch = "wasm32"))]
        {}
        #[cfg(target_arch = "wasm32")]
        {
            let (reply_tx, reply_rx) = oneshot::channel();
            if self
                .tx
                .unbounded_send(RuntimeRequest::Ping { reply: reply_tx })
                .is_err()
            {
                return;
            }
            let _ = reply_rx.await;
        }
    }

    pub async fn resolve_path(
        &self,
        value: Value,
        path: Vec<PathSegment>,
        db: salsa::DatabaseImpl,
        unit_registry: UnitRegistry,
    ) -> Option<Value> {
        #[cfg(not(target_arch = "wasm32"))]
        {
            resolve_path_blocking(&value, &path, &db, unit_registry)
        }
        #[cfg(target_arch = "wasm32")]
        {
            let (reply_tx, reply_rx) = oneshot::channel();
            if self
                .tx
                .unbounded_send(RuntimeRequest::ResolvePath {
                    value,
                    path,
                    db,
                    unit_registry,
                    reply: reply_tx,
                })
                .is_err()
            {
                return None;
            }
            reply_rx.await.ok().flatten()
        }
    }

    pub async fn collect_slice_window(
        &self,
        db: salsa::DatabaseImpl,
        inner: LazyVector,
        offset: usize,
        limit: usize,
        unit_registry: UnitRegistry,
    ) -> (u64, Vec<Result<Option<Value>, RunError>>) {
        #[cfg(not(target_arch = "wasm32"))]
        {
            collect_slice_window_blocking(db, inner, offset, limit, unit_registry)
        }
        #[cfg(target_arch = "wasm32")]
        {
            let (reply_tx, reply_rx) = oneshot::channel();
            if self
                .tx
                .unbounded_send(RuntimeRequest::CollectSliceWindow {
                    db,
                    inner,
                    offset,
                    limit,
                    unit_registry,
                    reply: reply_tx,
                })
                .is_err()
            {
                return (0, Vec::new());
            }
            reply_rx.await.unwrap_or((0, Vec::new()))
        }
    }

    /// Optional single-source fanout (e.g. future worker routing). Graph run uses
    /// [`feed_fanout_batch_blocking`] instead.
    #[cfg_attr(not(target_arch = "wasm32"), allow(dead_code))]
    pub async fn feed_fanout(
        &self,
        value: Value,
        db: salsa::DatabaseImpl,
        senders: Vec<StreamChunkSender>,
        unit_registry: UnitRegistry,
    ) {
        #[cfg(not(target_arch = "wasm32"))]
        {
            snaq_lite_lang::set_eval_registry(unit_registry);
            snaq_lite_lang::feed_value_to_senders_streaming(&value, &db, senders);
        }
        #[cfg(target_arch = "wasm32")]
        {
            let (reply_tx, reply_rx) = oneshot::channel();
            if self
                .tx
                .unbounded_send(RuntimeRequest::FeedFanout {
                    value,
                    db,
                    senders,
                    unit_registry,
                    reply: reply_tx,
                })
                .is_err()
            {
                return;
            }
            let _ = reply_rx.await;
        }
    }
}

pub struct RuntimeEngine;

impl RuntimeEngine {
    /// Native: inline streaming on the current task (no extra thread).
    #[cfg(not(target_arch = "wasm32"))]
    pub fn spawn() -> RuntimeHandle {
        RuntimeHandle {}
    }

    /// WASM: `spawn_local` worker loop (same JS thread; non-blocking).
    #[cfg(target_arch = "wasm32")]
    pub fn spawn() -> RuntimeHandle {
        let (tx, rx) = mpsc::unbounded();
        wasm_bindgen_futures::spawn_local(runtime_loop(rx));
        RuntimeHandle { tx }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(not(target_arch = "wasm32"))]
    #[tokio::test]
    async fn native_runtime_ping_round_trip() {
        let rt = RuntimeEngine::spawn();
        rt.ping().await;
    }

    #[cfg(target_arch = "wasm32")]
    #[test]
    fn wasm_runtime_request_is_send() {
        fn assert_send<T: Send>() {}
        assert_send::<RuntimeRequest>();
    }
}
