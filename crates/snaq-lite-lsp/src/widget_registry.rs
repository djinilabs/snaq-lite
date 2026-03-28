//! Registry of active widget subscriptions for snaqlite/graph/subscribeWidget.

use std::collections::HashMap;
use tower_lsp::lsp_types::Url;

/// Per-widget entry: source URI for invalidation; optional cancel sender (legacy stream consumer); cached result for fetchResultSlice.
pub struct WidgetEntry {
    pub source_uri: Url,
    pub cancel_tx: Option<futures::channel::oneshot::Sender<()>>,
    /// Cached result value so fetchResultSlice can serve slices without re-running. Cleared when widget is removed/invalidated.
    pub cached_value: Option<snaq_lite_lang::Value>,
}

/// Registry of active widget subscriptions by widget_id.
pub struct WidgetRegistry {
    by_id: HashMap<String, WidgetEntry>,
}

impl WidgetRegistry {
    fn uri_matches_prefix(uri: &str, prefix: &str) -> bool {
        if !uri.starts_with(prefix) {
            return false;
        }
        if uri.len() == prefix.len() || prefix.ends_with('/') {
            return true;
        }
        matches!(
            uri.as_bytes().get(prefix.len()).copied(),
            Some(b'/') | Some(b'?') | Some(b'#')
        )
    }

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
                cached_value: None,
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
                cached_value: None,
            },
        );
    }

    /// Insert a widget with a cached result value (for fetchResultSlice). No background consumer.
    pub fn insert_with_cached_value(
        &mut self,
        widget_id: String,
        source_uri: Url,
        value: snaq_lite_lang::Value,
    ) {
        self.by_id.insert(
            widget_id,
            WidgetEntry {
                source_uri,
                cancel_tx: None,
                cached_value: Some(value),
            },
        );
    }

    /// Get a clone of the cached value for this widget, if any.
    pub fn get_cached_value(&self, widget_id: &str) -> Option<snaq_lite_lang::Value> {
        self.by_id.get(widget_id).and_then(|e| e.cached_value.clone())
    }

    /// Source URI for this widget, if registered.
    pub fn source_uri(&self, widget_id: &str) -> Option<Url> {
        self.by_id.get(widget_id).map(|e| e.source_uri.clone())
    }

    /// Replace the cached value for an existing widget (e.g. after materializing a stream). No-op if widget not found.
    pub fn update_cached_value(&mut self, widget_id: &str, value: snaq_lite_lang::Value) {
        if let Some(entry) = self.by_id.get_mut(widget_id) {
            entry.cached_value = Some(value);
        }
    }

    /// List widget ids bound to a source URI.
    pub fn ids_for_uri(&self, uri: &Url) -> Vec<String> {
        self.by_id
            .iter()
            .filter(|(_, e)| e.source_uri == *uri)
            .map(|(id, _)| id.clone())
            .collect()
    }

    /// Update cached value by widget id if present.
    pub fn set_cached_value(&mut self, widget_id: &str, value: Option<snaq_lite_lang::Value>) {
        if let Some(entry) = self.by_id.get_mut(widget_id) {
            entry.cached_value = value;
        }
    }

    /// Remove widget by id. Returns Some(Some(cancel_tx)) if had a consumer, Some(None) for scalar, None if not found.
    pub fn remove(&mut self, widget_id: &str) -> Option<Option<futures::channel::oneshot::Sender<()>>> {
        self.by_id.remove(widget_id).map(|e| e.cancel_tx)
    }

    /// Take all widgets that listen to this URI (remove from registry). Returns (widget_id, cancel_tx) for each.
    /// cancel_tx is None for scalar / cached-value subscriptions. Caller can refresh and re-insert.
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

    /// Invalidate all widgets that listen to this URI. Returns (widget_id, optional cancel_tx) for each so caller can send Cancelled to all.
    pub fn invalidate_uri(
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

    /// Remove all widgets whose source URI starts with `uri_prefix`.
    /// Returns (widget_id, optional cancel_tx) for each removed widget.
    pub fn remove_prefix(
        &mut self,
        uri_prefix: &str,
    ) -> Vec<(String, Option<futures::channel::oneshot::Sender<()>>)> {
        let mut out = Vec::new();
        self.by_id.retain(|id, entry| {
            if Self::uri_matches_prefix(entry.source_uri.as_str(), uri_prefix) {
                out.push((id.clone(), entry.cancel_tx.take()));
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

    /// Drain all widgets, returning ids with optional cancel senders.
    /// Useful when callers must emit a terminal notification for every removed widget.
    pub fn drain_all_entries(
        &mut self,
    ) -> Vec<(String, Option<futures::channel::oneshot::Sender<()>>)> {
        self.by_id
            .drain()
            .map(|(id, mut entry)| (id, entry.cancel_tx.take()))
            .collect()
    }
}

impl Default for WidgetRegistry {
    fn default() -> Self {
        Self::new()
    }
}
