//! Subscription registry for live result pub-sub. Tracks active subscriptions by id and uri
//! for cancellation and mutation-driven invalidation.

use std::collections::HashMap;
use tower_lsp::lsp_types::Url;

/// Opaque subscription id (UUID string) returned to the client.
pub type SubscriptionId = String;

/// Per-subscription entry: uri and version for invalidation; cancel sender to stop the consumer task.
pub struct SubscriptionEntry {
    pub uri: Url,
    pub version: Option<i32>,
    pub cancel_tx: Option<futures::channel::oneshot::Sender<()>>,
}

/// Registry of active subscriptions. Cancel senders are used to stop background consumer tasks.
pub struct SubscriptionRegistry {
    by_id: HashMap<SubscriptionId, SubscriptionEntry>,
}

impl SubscriptionRegistry {
    pub fn new() -> Self {
        Self {
            by_id: HashMap::new(),
        }
    }

    /// Register a new subscription. Returns true if id was inserted (no previous entry).
    pub fn insert(
        &mut self,
        id: SubscriptionId,
        uri: Url,
        version: Option<i32>,
        cancel_tx: futures::channel::oneshot::Sender<()>,
    ) {
        self.by_id.insert(
            id,
            SubscriptionEntry {
                uri,
                version,
                cancel_tx: Some(cancel_tx),
            },
        );
    }

    /// Remove subscription by id. Returns the cancel sender if present (caller may send to cancel).
    pub fn remove(&mut self, id: &str) -> Option<futures::channel::oneshot::Sender<()>> {
        self.by_id.remove(id).and_then(|e| e.cancel_tx)
    }

    /// Invalidate all subscriptions for the given uri. Returns list of (id, cancel_tx) for each
    /// so the caller can send cancel and then send a final publishResult(Cancelled) per id.
    pub fn invalidate_uri(&mut self, uri: &Url) -> Vec<(SubscriptionId, futures::channel::oneshot::Sender<()>)> {
        let mut out = Vec::new();
        self.by_id.retain(|id, entry| {
            if entry.uri == *uri {
                if let Some(tx) = entry.cancel_tx.take() {
                    out.push((id.clone(), tx));
                }
                false
            } else {
                true
            }
        });
        out
    }

    /// Invalidate all subscriptions (e.g. on LSP shutdown). Returns list of (id, cancel_tx).
    pub fn invalidate_all(&mut self) -> Vec<(SubscriptionId, futures::channel::oneshot::Sender<()>)> {
        let mut out = Vec::new();
        for (id, entry) in self.by_id.drain() {
            if let Some(tx) = entry.cancel_tx {
                out.push((id, tx));
            }
        }
        out
    }
}

impl Default for SubscriptionRegistry {
    fn default() -> Self {
        Self::new()
    }
}
