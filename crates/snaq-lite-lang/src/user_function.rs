//! User-defined functions: closure representation and registry.
//! Functions are stored by id so Value and StoredValue can hold a u64 without circular deps.

use crate::ir::ExprDef;
use crate::scope::Env;
use std::sync::atomic::{AtomicU64, Ordering};

/// Unique id for a user function (used in Value::Function and StoredValue::Function).
pub type UserFunctionId = u64;

static NEXT_ID: AtomicU64 = AtomicU64::new(0);

fn next_id() -> UserFunctionId {
    NEXT_ID.fetch_add(1, Ordering::Relaxed)
}

/// A user-defined function: params (with optional defaults), body, and captured env.
#[derive(Clone, Debug)]
pub struct UserFunction {
    pub id: UserFunctionId,
    /// (param name, optional default expression).
    pub params: Vec<(String, Option<Box<ExprDef>>)>,
    pub body: Box<ExprDef>,
    /// Environment at definition time (captured closure).
    pub closure_env: Env,
}

impl UserFunction {
    pub fn new(
        params: Vec<(String, Option<Box<ExprDef>>)>,
        body: Box<ExprDef>,
        closure_env: Env,
    ) -> Self {
        Self {
            id: next_id(),
            params,
            body,
            closure_env,
        }
    }
}

/// Registry: map from id to UserFunction. Used to resolve Value::Function(id) when calling.
/// We use a simple thread-local map so we don't need Mutex in the main path.
use std::cell::RefCell;
thread_local! {
    static REGISTRY: RefCell<std::collections::HashMap<UserFunctionId, UserFunction>> =
        RefCell::new(std::collections::HashMap::new());
}

/// Insert a user function and return its id. The id is also stored inside the struct.
pub fn register(uf: UserFunction) -> UserFunctionId {
    let id = uf.id;
    REGISTRY.with(|r| r.borrow_mut().insert(id, uf));
    id
}

/// Look up a user function by id. Returns None if not found (e.g. id from another thread).
pub fn get(id: UserFunctionId) -> Option<UserFunction> {
    REGISTRY.with(|r| r.borrow().get(&id).cloned())
}
