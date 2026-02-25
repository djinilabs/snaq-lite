//! Heap for vector values referenced from scope bindings.
//! Variable bindings are unified in [Env](crate::scope::Env): each name maps to one [StoredValue](crate::scope::StoredValue).
//! For vectors we store only an id in the scope because [VectorValue](crate::vector::VectorValue) cannot implement Eq + Hash
//! (it contains [Value](crate::symbolic::Value), [ExprDef](crate::ir::ExprDef), etc.), and [Scope](crate::scope::Scope) is Salsa-interned so [Env] must be hashable.
//! This module is just the backing store for those ids, not a second set of bindings.

use crate::vector::VectorValue;
use std::cell::RefCell;
use std::sync::atomic::{AtomicU64, Ordering};

/// Unique id for a stored vector (used in StoredValue::Vector).
pub type VectorId = u64;

static NEXT_ID: AtomicU64 = AtomicU64::new(0);

fn next_id() -> VectorId {
    NEXT_ID.fetch_add(1, Ordering::Relaxed)
}

thread_local! {
    static REGISTRY: RefCell<std::collections::HashMap<VectorId, VectorValue>> =
        RefCell::new(std::collections::HashMap::new());
}

/// Store a vector and return its id. The vector can be retrieved later with [get].
pub fn register(v: VectorValue) -> VectorId {
    let id = next_id();
    REGISTRY.with(|r| r.borrow_mut().insert(id, v));
    id
}

/// Look up a vector by id. Returns None if not found (e.g. id from another thread).
pub fn get(id: VectorId) -> Option<VectorValue> {
    REGISTRY.with(|r| r.borrow().get(&id).cloned())
}
