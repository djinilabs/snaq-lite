//! Registry for node result handles and pagination cursors.

use crate::pubsub::PathSegment;
use futures::stream::StreamExt;
use snaq_lite_lang::stream_handle::ChunkFlattenStream;
use std::collections::HashMap;
use std::time::{Duration, Instant};
use tower_lsp::lsp_types::Url;

const CURSOR_TTL: Duration = Duration::from_secs(300);
const MAX_CURSORS: usize = 1024;
const FORWARD_ONLY_PREFETCH_LIMIT: usize = 128;

#[derive(Clone)]
pub struct ResultHandleEntry {
    pub handle: String,
    pub source_uri: Url,
    pub revision: u64,
    pub value: snaq_lite_lang::Value,
    /// True when this handle originated from a non-replayable stream-backed vector.
    /// Forward-only paging rules should continue to apply even after server-side cache upgrades.
    pub forward_only: bool,
}

#[derive(Clone)]
struct CursorEntry {
    handle: String,
    path: Vec<PathSegment>,
    expected_offset: u64,
    created_at: Instant,
}

#[derive(Debug)]
pub struct ForwardOnlyPage {
    pub items: Vec<Result<Option<snaq_lite_lang::Value>, snaq_lite_lang::RunError>>,
    pub has_more: bool,
    pub total_count: u64,
}

struct ForwardOnlyState {
    stream: ChunkFlattenStream,
    next_offset: u64,
    prefetched: std::collections::VecDeque<
        Result<Option<snaq_lite_lang::Value>, snaq_lite_lang::RunError>,
    >,
    exhausted: bool,
}

pub struct ResultHandleRegistry {
    by_handle: HashMap<String, ResultHandleEntry>,
    by_uri: HashMap<Url, String>,
    cursors: HashMap<String, CursorEntry>,
    forward_only: HashMap<String, ForwardOnlyState>,
}

impl ResultHandleRegistry {
    fn is_forward_only_value(value: &snaq_lite_lang::Value) -> bool {
        matches!(
            value,
            snaq_lite_lang::Value::Vector(snaq_lite_lang::VectorValue {
                inner: snaq_lite_lang::LazyVector::FromInput(_),
                ..
            })
        )
    }

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
            forward_only: HashMap::new(),
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
                forward_only: Self::is_forward_only_value(&value),
                value,
            },
        );
        self.invalidate_cursors_for_handle(&handle);
        self.forward_only.remove(&handle);
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
        // Preserve forward-only contract once established for this handle lineage.
        self.invalidate_cursors_for_handle(handle);
        self.forward_only.remove(handle);
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
        self.forward_only.remove(&handle);
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
        self.forward_only.clear();
    }

    pub fn is_empty(&self) -> bool {
        self.by_handle.is_empty()
            && self.by_uri.is_empty()
            && self.cursors.is_empty()
            && self.forward_only.is_empty()
    }

    pub fn len_handles(&self) -> usize {
        self.by_handle.len()
    }

    fn invalidate_cursors_for_handle(&mut self, handle: &str) {
        self.cursors.retain(|_, entry| entry.handle != handle);
    }

    fn run_local_future<F>(future: F) -> F::Output
    where
        F: futures::Future,
    {
        let mut pool = futures::executor::LocalPool::new();
        pool.run_until(future)
    }

    fn ensure_forward_only_state(
        &mut self,
        handle: &str,
    ) -> Result<&mut ForwardOnlyState, &'static str> {
        if !self.forward_only.contains_key(handle) {
            let Some(entry) = self.by_handle.get(handle) else {
                return Err("result handle not found");
            };
            let handle_id = match &entry.value {
                snaq_lite_lang::Value::Vector(snaq_lite_lang::VectorValue {
                    inner: snaq_lite_lang::LazyVector::FromInput(id),
                    ..
                }) => *id,
                _ => return Err("result handle is not forward-only"),
            };
            let receiver =
                snaq_lite_lang::take_receiver(handle_id).ok_or("stream input not available")?;
            self.forward_only.insert(
                handle.to_string(),
                ForwardOnlyState {
                    stream: ChunkFlattenStream::new(receiver),
                    next_offset: 0,
                    prefetched: std::collections::VecDeque::new(),
                    exhausted: false,
                },
            );
        }
        // safe: inserted above when missing
        Ok(self
            .forward_only
            .get_mut(handle)
            .expect("forward-only state exists"))
    }

    pub fn read_forward_only_page(
        &mut self,
        handle: &str,
        offset: u64,
        limit: usize,
    ) -> Result<ForwardOnlyPage, &'static str> {
        let state = self.ensure_forward_only_state(handle)?;
        if offset != state.next_offset {
            return Err("forward-only handle offset does not match continuation state");
        }
        let mut items: Vec<Result<Option<snaq_lite_lang::Value>, snaq_lite_lang::RunError>> =
            Vec::with_capacity(limit);
        while items.len() < limit {
            if let Some(item) = state.prefetched.pop_front() {
                items.push(item);
                state.next_offset = state.next_offset.saturating_add(1);
                continue;
            }
            if state.exhausted {
                break;
            }
            let next = Self::run_local_future(async { state.stream.next().await });
            match next {
                Some(item) => {
                    items.push(item);
                    state.next_offset = state.next_offset.saturating_add(1);
                }
                None => {
                    state.exhausted = true;
                    break;
                }
            }
        }
        if !state.exhausted && state.prefetched.is_empty() {
            let next = Self::run_local_future(async { state.stream.next().await });
            match next {
                Some(item) => {
                    if state.prefetched.len() >= FORWARD_ONLY_PREFETCH_LIMIT {
                        state.prefetched.pop_front();
                    }
                    state.prefetched.push_back(item);
                }
                None => {
                    state.exhausted = true;
                }
            }
        }
        let has_more = !state.prefetched.is_empty() || !state.exhausted;
        // For forward-only streams, total count is exact only once exhausted.
        // Until then, return a lower bound (already consumed + prefetched + at least one more if has_more).
        let total_count = if state.exhausted {
            state.next_offset.saturating_add(state.prefetched.len() as u64)
        } else {
            state
                .next_offset
                .saturating_add(state.prefetched.len() as u64)
                .saturating_add(u64::from(has_more))
        };
        Ok(ForwardOnlyPage {
            items,
            has_more,
            total_count,
        })
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
    use futures::SinkExt;
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

    #[test]
    fn forward_only_paging_is_sequential_without_materialization_upgrade() {
        let mut reg = ResultHandleRegistry::new();
        let uri = Url::parse("snaq://canvas/stream.sl").unwrap();
        let (stream_id, mut sender) = snaq_lite_lang::create_stream_input();
        futures::executor::block_on(async {
            sender
                .send(vec![
                    Ok(Some(snaq_lite_lang::Value::Numeric(Quantity::from_scalar(1.0)))),
                    Ok(Some(snaq_lite_lang::Value::Numeric(Quantity::from_scalar(2.0)))),
                    Ok(Some(snaq_lite_lang::Value::Numeric(Quantity::from_scalar(3.0)))),
                ])
                .await
                .expect("send stream chunk");
        });
        drop(sender);
        let handle = reg.upsert_result(
            uri,
            1,
            snaq_lite_lang::Value::Vector(snaq_lite_lang::VectorValue::column(
                snaq_lite_lang::LazyVector::FromInput(stream_id),
            )),
        );

        let page1 = reg
            .read_forward_only_page(&handle, 0, 2)
            .expect("first page");
        assert_eq!(page1.items.len(), 2);
        assert!(page1.has_more);
        let page2 = reg
            .read_forward_only_page(&handle, 2, 2)
            .expect("second page");
        assert_eq!(page2.items.len(), 1);
        assert!(!page2.has_more);
        let err = match reg.read_forward_only_page(&handle, 2, 1) {
            Ok(_) => panic!("expected offset mismatch error"),
            Err(e) => e,
        };
        assert!(err.contains("offset does not match"));
    }
}
