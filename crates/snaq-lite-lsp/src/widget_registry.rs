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

    /// Insert a widget with no background consumer (e.g. scalar result). Used so we can push
    /// updates when the source document changes without the client re-subscribing.
    pub fn insert_scalar(&mut self, widget_id: String, source_uri: Url) {
        self.by_id.insert(
            widget_id,
            WidgetEntry {
                source_uri,
                cancel_tx: None,
            },
        );
    }

    /// Remove widget by id. Returns Some(Some(cancel_tx)) if had a consumer, Some(None) for scalar, None if not found.
    pub fn remove(&mut self, widget_id: &str) -> Option<Option<futures::channel::oneshot::Sender<()>>> {
        self.by_id.remove(widget_id).map(|e| e.cancel_tx)
    }

    /// Take all widgets that listen to this URI (remove from registry). Returns (widget_id, cancel_tx) for each.
    /// cancel_tx is None for scalar subscriptions. Caller can refresh and re-insert.
    pub fn take_entries_for_uri(
        &mut self,
        uri: &Url,
    ) -> Vec<(String, Option<futures::channel::oneshot::Sender<()>>)> {
        let mut out = Vec::new();
        self.by_id.retain(|id, entry| {
            if entry.source_uri == *uri {
                out.push((id.clone(), entry.cancel_tx.take()));
                false
            } else {
                true
            }
        });
        out
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
