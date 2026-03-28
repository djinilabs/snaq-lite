//! URI-keyed node result cache for graph-runtime recomputation.

use std::collections::HashMap;
use tower_lsp::lsp_types::Url;

#[derive(Clone)]
pub struct NodeResultEntry {
    pub value: Option<snaq_lite_lang::Value>,
    pub error: Option<String>,
    pub revision: u64,
}

pub struct NodeResultRegistry {
    by_uri: HashMap<Url, NodeResultEntry>,
}

impl NodeResultRegistry {
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
            by_uri: HashMap::new(),
        }
    }

    pub fn upsert_value(&mut self, uri: Url, value: snaq_lite_lang::Value) -> u64 {
        let revision = self
            .by_uri
            .get(&uri)
            .map(|e| e.revision.saturating_add(1))
            .unwrap_or(1);
        self.by_uri.insert(
            uri,
            NodeResultEntry {
                value: Some(value),
                error: None,
                revision,
            },
        );
        revision
    }

    pub fn upsert_error(&mut self, uri: Url, error: String) -> u64 {
        let revision = self
            .by_uri
            .get(&uri)
            .map(|e| e.revision.saturating_add(1))
            .unwrap_or(1);
        self.by_uri.insert(
            uri,
            NodeResultEntry {
                value: None,
                error: Some(error),
                revision,
            },
        );
        revision
    }

    pub fn get(&self, uri: &Url) -> Option<&NodeResultEntry> {
        self.by_uri.get(uri)
    }

    pub fn remove(&mut self, uri: &Url) -> bool {
        self.by_uri.remove(uri).is_some()
    }

    pub fn remove_with_prefix(&mut self, uri_prefix: &str) -> usize {
        let before = self.by_uri.len();
        self.by_uri
            .retain(|uri, _| !Self::uri_matches_prefix(uri.as_str(), uri_prefix));
        before.saturating_sub(self.by_uri.len())
    }

    pub fn clear(&mut self) {
        self.by_uri.clear();
    }
}

impl Default for NodeResultRegistry {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snaq_lite_lang::{Quantity, Value};

    #[test]
    fn upsert_and_read_latest_result_by_uri() {
        let mut store = NodeResultRegistry::new();
        let uri = Url::parse("snaq://graph/node.sl").unwrap();
        let rev1 = store.upsert_value(uri.clone(), Value::Numeric(Quantity::from_scalar(1.0)));
        let rev2 = store.upsert_value(uri.clone(), Value::Numeric(Quantity::from_scalar(2.0)));
        assert_eq!(rev1, 1);
        assert_eq!(rev2, 2);
        let entry = store.get(&uri).expect("entry");
        assert_eq!(entry.revision, 2);
        let Value::Numeric(q) = entry.value.clone().expect("value") else {
            panic!("expected numeric value");
        };
        assert!((q.value() - 2.0).abs() < 1e-10);
    }

    #[test]
    fn upsert_error_updates_revision() {
        let mut store = NodeResultRegistry::new();
        let uri = Url::parse("snaq://graph/node.sl").unwrap();
        let rev1 = store.upsert_error(uri.clone(), "boom".to_string());
        let rev2 = store.upsert_error(uri.clone(), "boom2".to_string());
        assert_eq!(rev1, 1);
        assert_eq!(rev2, 2);
        let entry = store.get(&uri).expect("entry");
        assert_eq!(entry.error.as_deref(), Some("boom2"));
        assert!(entry.value.is_none());
    }

    #[test]
    fn multiple_subscribers_receive_same_versioned_update() {
        let mut store = NodeResultRegistry::new();
        let uri = Url::parse("snaq://graph/node.sl").unwrap();
        let rev = store.upsert_value(uri.clone(), Value::Numeric(Quantity::from_scalar(9.0)));
        let left = store.get(&uri).expect("left read").revision;
        let right = store.get(&uri).expect("right read").revision;
        assert_eq!(rev, left);
        assert_eq!(left, right);
    }
}
