//! Heap for map values referenced from scope bindings and stream inputs.
//! Maps are stored by id (like vectors) because [Value](crate::symbolic::Value) is not Hash,
//! and [Scope](crate::scope::Scope) is Salsa-interned so [Env] must be hashable.
//!
//! The registry is **shared across threads** so that stream feeders (running in worker threads)
//! can register row-as-map values and the main thread can resolve them when evaluating e.g. `row.col`.

use crate::error::RunError;
use crate::symbolic::Value;
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, OnceLock};

/// Unique id for a stored map (used in StoredValue::Map).
pub type MapId = u64;

/// One tabular row: column name → value. Used by stream ingest (CSV, Parquet, Arrow) and hosts.
pub type Record = Vec<(String, Value)>;

type RegistryStore = HashMap<MapId, Vec<(String, Value)>>;

static NEXT_ID: AtomicU64 = AtomicU64::new(0);

fn next_id() -> MapId {
    NEXT_ID.fetch_add(1, Ordering::Relaxed)
}

static REGISTRY: OnceLock<Arc<Mutex<RegistryStore>>> = OnceLock::new();

fn registry() -> &'static Arc<Mutex<RegistryStore>> {
    REGISTRY.get_or_init(|| Arc::new(Mutex::new(HashMap::new())))
}

/// Store a map (ordered key-value pairs) and return its id.
/// Safe to call from any thread (used by stream feeders and evaluation).
pub fn register(entries: Vec<(String, Value)>) -> MapId {
    let id = next_id();
    registry()
        .lock()
        .expect("map_registry lock")
        .insert(id, entries);
    id
}

/// Look up a map by id. Returns None if not found.
pub fn get(id: MapId) -> Option<Vec<(String, Value)>> {
    registry().lock().expect("map_registry lock").get(&id).cloned()
}

/// Look up a key in a map by id. Returns None if map not found or key not present.
pub fn get_key(id: MapId, key: &str) -> Option<Value> {
    registry()
        .lock()
        .expect("map_registry lock")
        .get(&id)
        .and_then(|entries| entries.iter().find(|(k, _)| k == key).map(|(_, v)| v.clone()))
}

/// Build a [Value::Map](crate::symbolic::Value::Map) from a record (e.g. one tabular row).
/// Intended for hosts building stream chunk elements: register the entries and return the map value.
/// Safe to call from any thread.
pub fn record_to_value(entries: Vec<(String, Value)>) -> Value {
    Value::Map(register(entries))
}

/// Turn a record (e.g. one tabular row) into a single chunk element for stream input.
/// Returns `Ok(Some(Value::Map(id)))` so hosts (CLI or WASM) can push it into a [Chunk](crate::stream_handle::Chunk).
pub fn record_to_chunk_element(entries: Vec<(String, Value)>) -> Result<Option<Value>, RunError> {
    Ok(Some(record_to_value(entries)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::quantity::{Quantity, SnaqNumber};
    use crate::unit::Unit;

    fn numeric_value(v: &Value) -> Option<f64> {
        match v {
            Value::Numeric(q) => Some(q.value()),
            _ => None,
        }
    }

    #[test]
    fn shared_registry_register_from_one_thread_get_from_another() {
        let entries = vec![
            ("a".to_string(), Value::Numeric(Quantity::with_number(
                SnaqNumber::new(1.0, 0.0),
                Unit::scalar(),
            ))),
            ("b".to_string(), Value::Numeric(Quantity::with_number(
                SnaqNumber::new(2.0, 0.0),
                Unit::scalar(),
            ))),
        ];
        let id = std::thread::spawn(move || register(entries))
            .join()
            .expect("thread");
        assert_eq!(get_key(id, "a").as_ref().and_then(numeric_value), Some(1.0));
        assert_eq!(get_key(id, "b").as_ref().and_then(numeric_value), Some(2.0));
        assert!(get_key(id, "c").is_none());
    }

    #[test]
    fn record_to_value_returns_map_with_registered_entries() {
        let entries = vec![
            ("x".to_string(), Value::Numeric(Quantity::with_number(
                SnaqNumber::new(10.0, 0.0),
                Unit::scalar(),
            ))),
        ];
        let v = record_to_value(entries);
        let id = match &v {
            Value::Map(id) => *id,
            _ => panic!("expected Value::Map"),
        };
        assert_eq!(get_key(id, "x").as_ref().and_then(numeric_value), Some(10.0));
    }

    #[test]
    fn record_to_chunk_element_returns_ok_some_map() {
        let entries = vec![
            ("col".to_string(), Value::Numeric(Quantity::with_number(
                SnaqNumber::new(42.0, 0.0),
                Unit::scalar(),
            ))),
        ];
        let r = record_to_chunk_element(entries).expect("ok");
        assert!(r.is_some());
        let v = r.unwrap();
        let id = match &v {
            Value::Map(id) => *id,
            _ => panic!("expected Value::Map"),
        };
        assert_eq!(get_key(id, "col").as_ref().and_then(numeric_value), Some(42.0));
    }
}
