//! Registry of active widget subscriptions for snaqlite/graph/subscribeWidget.

use std::collections::HashMap;
use tower_lsp::lsp_types::Url;

/// Per-widget entry: source URI for invalidation; cancel sender to stop the consumer task.
pub struct WidgetEntry {
    pub source_uri: Url,
    pub cancel_tx: Option<futures::channel::oneshot::Sender<()>>,
}

/// Registry of active widget subscriptions by widget_id.
pub struct WidgetRegistry {
    by_id: HashMap<String, WidgetEntry>,
}

impl WidgetRegistry {
    pub fn new() -> Self {
        Self {
            by_id: HashMap::new(),
        }
    }

    pub fn insert(
        &mut self,
        widget_id: String,
        source_uri: Url,
        cancel_tx: futures::channel::oneshot::Sender<()>,
    ) {
        self.by_id.insert(
            widget_id,
            WidgetEntry {
                source_uri,
                cancel_tx: Some(cancel_tx),
            },
        );
    }

    pub fn remove(&mut self, widget_id: &str) -> Option<futures::channel::oneshot::Sender<()>> {
        self.by_id.remove(widget_id).and_then(|e| e.cancel_tx)
    }

    /// Invalidate all widgets that listen to this URI. Returns (widget_id, cancel_tx) for each.
    pub fn invalidate_uri(&mut self, uri: &Url) -> Vec<(String, futures::channel::oneshot::Sender<()>)> {
        let mut out = Vec::new();
        self.by_id.retain(|id, entry| {
            if entry.source_uri == *uri {
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

    pub fn invalidate_all(&mut self) -> Vec<(String, futures::channel::oneshot::Sender<()>)> {
        let mut out = Vec::new();
        for (id, entry) in self.by_id.drain() {
            if let Some(tx) = entry.cancel_tx {
                out.push((id, tx));
            }
        }
        out
    }
}

impl Default for WidgetRegistry {
    fn default() -> Self {
        Self::new()
    }
}
