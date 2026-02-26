//! Heap for map values referenced from scope bindings.
//! Maps are stored by id (like vectors) because [Value](crate::symbolic::Value) is not Hash,
//! and [Scope](crate::scope::Scope) is Salsa-interned so [Env] must be hashable.

use crate::symbolic::Value;
use std::cell::RefCell;
use std::sync::atomic::{AtomicU64, Ordering};

/// Unique id for a stored map (used in StoredValue::Map).
pub type MapId = u64;

static NEXT_ID: AtomicU64 = AtomicU64::new(0);

fn next_id() -> MapId {
    NEXT_ID.fetch_add(1, Ordering::Relaxed)
}

thread_local! {
    static REGISTRY: RefCell<std::collections::HashMap<MapId, Vec<(String, Value)>>> =
        RefCell::new(std::collections::HashMap::new());
}

/// Store a map (ordered key-value pairs) and return its id.
pub fn register(entries: Vec<(String, Value)>) -> MapId {
    let id = next_id();
    REGISTRY.with(|r| r.borrow_mut().insert(id, entries));
    id
}

/// Look up a map by id. Returns None if not found (e.g. id from another thread).
pub fn get(id: MapId) -> Option<Vec<(String, Value)>> {
    REGISTRY.with(|r| r.borrow().get(&id).cloned())
}

/// Look up a key in a map by id. Returns None if map not found or key not present.
pub fn get_key(id: MapId, key: &str) -> Option<Value> {
    REGISTRY.with(|r| {
        r.borrow()
            .get(&id)
            .and_then(|entries| entries.iter().find(|(k, _)| k == key).map(|(_, v)| v.clone()))
    })
}
