//! Registry for node result handles and pagination cursors.

use crate::pubsub::PathSegment;
use std::collections::HashMap;
use std::time::{Duration, Instant};
use tower_lsp::lsp_types::Url;

const CURSOR_TTL: Duration = Duration::from_secs(300);
const MAX_CURSORS: usize = 1024;

#[derive(Clone)]
pub struct ResultHandleEntry {
    pub handle: String,
    pub source_uri: Url,
    pub revision: u64,
    pub value: snaq_lite_lang::Value,
}

#[derive(Clone)]
struct CursorEntry {
    handle: String,
    path: Vec<PathSegment>,
    expected_offset: u64,
    created_at: Instant,
}

pub struct ResultHandleRegistry {
    by_handle: HashMap<String, ResultHandleEntry>,
    by_uri: HashMap<Url, String>,
    cursors: HashMap<String, CursorEntry>,
}

impl ResultHandleRegistry {
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
            by_handle: HashMap::new(),
            by_uri: HashMap::new(),
            cursors: HashMap::new(),
        }
    }

    pub fn upsert_result(
        &mut self,
        source_uri: Url,
        revision: u64,
        value: snaq_lite_lang::Value,
    ) -> String {
        let handle = self.by_uri.get(&source_uri).cloned().unwrap_or_else(|| {
            let id = uuid::Uuid::new_v4().to_string();
            self.by_uri.insert(source_uri.clone(), id.clone());
            id
        });
        if let Some(existing) = self.by_handle.get(&handle) {
            if existing.revision == revision && existing.value == value {
                return handle;
            }
        }
        self.by_handle.insert(
            handle.clone(),
            ResultHandleEntry {
                handle: handle.clone(),
                source_uri,
                revision,
                value,
            },
        );
        self.invalidate_cursors_for_handle(&handle);
        handle
    }

    pub fn get(&self, handle: &str) -> Option<&ResultHandleEntry> {
        self.by_handle.get(handle)
    }

    pub fn update_handle_value(
        &mut self,
        handle: &str,
        revision: u64,
        value: snaq_lite_lang::Value,
    ) -> bool {
        let Some(entry) = self.by_handle.get_mut(handle) else {
            return false;
        };
        entry.revision = revision;
        entry.value = value;
        self.invalidate_cursors_for_handle(handle);
        true
    }

    pub fn issue_cursor(
        &mut self,
        handle: &str,
        path: &[PathSegment],
        expected_offset: u64,
    ) -> String {
        self.purge_expired_cursors();
        if self.cursors.len() >= MAX_CURSORS {
            self.evict_oldest_cursor();
        }
        let token = uuid::Uuid::new_v4().to_string();
        self.cursors.insert(
            token.clone(),
            CursorEntry {
                handle: handle.to_string(),
                path: path.to_vec(),
                expected_offset,
                created_at: Instant::now(),
            },
        );
        token
    }

    pub fn validate_and_consume_cursor(
        &mut self,
        cursor: &str,
        handle: &str,
        path: &[PathSegment],
        offset: u64,
    ) -> bool {
        self.purge_expired_cursors();
        let Some(entry) = self.cursors.remove(cursor) else {
            return false;
        };
        entry.handle == handle && entry.path == path && entry.expected_offset == offset
    }

    pub fn remove_for_uri(&mut self, uri: &Url) -> usize {
        let Some(handle) = self.by_uri.remove(uri) else {
            return 0;
        };
        self.by_handle.remove(&handle);
        self.invalidate_cursors_for_handle(&handle);
        1
    }

    pub fn remove_with_prefix(&mut self, uri_prefix: &str) -> usize {
        let uris: Vec<Url> = self
            .by_uri
            .keys()
            .filter(|uri| Self::uri_matches_prefix(uri.as_str(), uri_prefix))
            .cloned()
            .collect();
        let mut removed = 0usize;
        for uri in uris {
            removed += self.remove_for_uri(&uri);
        }
        removed
    }

    pub fn clear(&mut self) {
        self.by_handle.clear();
        self.by_uri.clear();
        self.cursors.clear();
    }

    pub fn is_empty(&self) -> bool {
        self.by_handle.is_empty() && self.by_uri.is_empty() && self.cursors.is_empty()
    }

    fn invalidate_cursors_for_handle(&mut self, handle: &str) {
        self.cursors.retain(|_, entry| entry.handle != handle);
    }

    fn purge_expired_cursors(&mut self) {
        let now = Instant::now();
        self.cursors
            .retain(|_, entry| now.duration_since(entry.created_at) <= CURSOR_TTL);
    }

    fn evict_oldest_cursor(&mut self) {
        let oldest = self
            .cursors
            .iter()
            .min_by_key(|(_, entry)| entry.created_at)
            .map(|(token, _)| token.clone());
        if let Some(token) = oldest {
            self.cursors.remove(&token);
        }
    }
}

impl Default for ResultHandleRegistry {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snaq_lite_lang::Quantity;

    #[test]
    fn upsert_reuses_handle_for_uri() {
        let mut reg = ResultHandleRegistry::new();
        let uri = Url::parse("snaq://canvas/n1.sl").unwrap();
        let h1 = reg.upsert_result(uri.clone(), 1, snaq_lite_lang::Value::Numeric(Quantity::from_scalar(1.0)));
        let h2 = reg.upsert_result(uri.clone(), 2, snaq_lite_lang::Value::Numeric(Quantity::from_scalar(2.0)));
        assert_eq!(h1, h2);
        let entry = reg.get(&h1).expect("entry");
        assert_eq!(entry.revision, 2);
    }

    #[test]
    fn cursor_is_one_time_and_matches_offset() {
        let mut reg = ResultHandleRegistry::new();
        let uri = Url::parse("snaq://canvas/n1.sl").unwrap();
        let handle = reg.upsert_result(uri, 1, snaq_lite_lang::Value::Undefined);
        let token = reg.issue_cursor(&handle, &[], 10);
        assert!(reg.validate_and_consume_cursor(&token, &handle, &[], 10));
        assert!(!reg.validate_and_consume_cursor(&token, &handle, &[], 10));
    }
}
