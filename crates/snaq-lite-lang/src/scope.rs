//! Lexical scope (environment) for variable bindings.
//!
//! Environments are immutable and implemented with a persistent map so that
//! extending the scope returns a new map that shares structure with the old one.
//! Scope is Salsa-interned so that (scope, expr) is the memoization key for evaluation.
//!
//! Closure envs (captured by user functions) are stored in a thread-local registry
//! so UserFunction can hold only an id and remain hashable (breaking the type cycle).

use crate::fuzzy::FuzzyBool;
use crate::quantity::Quantity;
use crate::symbolic::Value;
use crate::user_function::UserFunction;
use crate::vector_registry;
use im::OrdMap;
use std::cell::RefCell;
use std::hash::{Hash, Hasher};
use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};

/// Value that can be stored in the scope map. Must be Eq + Hash (Scope is Salsa-interned by Env).
/// Bindings are unified here: each variable name maps to exactly one StoredValue.
/// For vectors we store an id; the actual payload lives in [vector_registry](crate::vector_registry) (VectorValue is not Hash).
/// User functions are stored inline (hashable); only their captured env lives in [closure_env_register]/[closure_env_get].
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum StoredValue {
    Numeric(Quantity),
    FuzzyBool(FuzzyBool),
    Undefined,
    /// User-defined function (inline; closure env in closure-env registry).
    Function(Box<UserFunction>),
    /// Vector (id into vector_registry; payload stored there because VectorValue is not Eq+Hash).
    Vector(vector_registry::VectorId),
}

impl StoredValue {
    /// Convert from runtime Value. Returns Err for Vector or Symbolic (cannot store in scope in v1).
    pub fn from_value(v: &Value) -> Result<Self, crate::error::RunError> {
        match v {
            Value::Numeric(q) => Ok(StoredValue::Numeric(q.clone())),
            Value::Symbolic(_) => Err(crate::error::RunError::BindingValueNotSupported(
                "symbolic value not yet supported".to_string(),
            )),
            Value::FuzzyBool(fb) => Ok(StoredValue::FuzzyBool(fb.clone())),
            Value::Undefined => Ok(StoredValue::Undefined),
            Value::Vector(v) => {
                let id = vector_registry::register(v.clone());
                Ok(StoredValue::Vector(id))
            }
            Value::Function(uf) => Ok(StoredValue::Function(uf.clone())),
        }
    }

    /// Convert to runtime Value.
    pub fn to_value(&self) -> Value {
        match self {
            StoredValue::Numeric(q) => Value::Numeric(q.clone()),
            StoredValue::FuzzyBool(fb) => Value::FuzzyBool(fb.clone()),
            StoredValue::Undefined => Value::Undefined,
            StoredValue::Function(uf) => Value::Function(uf.clone()),
            StoredValue::Vector(id) => vector_registry::get(*id)
                .map(Value::Vector)
                .unwrap_or(Value::Undefined),
        }
    }
}

impl fmt::Display for StoredValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_value().fmt(f)
    }
}

/// Immutable environment: map from variable names to stored values.
/// Uses a persistent map so extension does not mutate.
/// Wrapped in a newtype so we can implement Hash for Salsa interning.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Env(OrdMap<String, StoredValue>);

impl Hash for Env {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for (k, v) in self.0.iter() {
            k.hash(state);
            v.hash(state);
        }
    }
}

impl Env {
    pub fn empty() -> Self {
        Self(OrdMap::new())
    }

    pub fn get(&self, name: &str) -> Option<&StoredValue> {
        self.0.get(name)
    }

    /// Return a new env with the binding added (non-destructive).
    pub fn extend(&self, name: String, value: StoredValue) -> Self {
        Self(self.0.update(name, value))
    }
}

/// Empty environment (convenience).
pub fn empty_env() -> Env {
    Env::empty()
}

/// Extension: return a new env with the binding added (non-destructive).
pub fn env_extend(env: Env, name: String, value: StoredValue) -> Env {
    env.extend(name, value)
}

/// Salsa-interned scope. Used as parameter to evaluation so (scope, expr) is the memoization key.
#[salsa::interned]
pub struct Scope {
    #[returns(ref)]
    pub env: Env,
}

/// Canonical empty scope (all callers get the same interned id).
pub fn empty_scope(db: &dyn salsa::Database) -> Scope<'_> {
    Scope::new(db, Env::empty())
}

// --- Closure-env registry (breaks type cycle: UserFunction holds id, not Env) ---

pub type ClosureEnvId = u64;

static NEXT_CLOSURE_ENV_ID: AtomicU64 = AtomicU64::new(0);

fn next_closure_env_id() -> ClosureEnvId {
    NEXT_CLOSURE_ENV_ID.fetch_add(1, Ordering::Relaxed)
}

thread_local! {
    static CLOSURE_ENV_REGISTRY: RefCell<std::collections::HashMap<ClosureEnvId, Env>> =
        RefCell::new(std::collections::HashMap::new());
}

/// Store a closure environment and return its id. Used when creating a user function.
pub fn closure_env_register(env: Env) -> ClosureEnvId {
    let id = next_closure_env_id();
    CLOSURE_ENV_REGISTRY.with(|r| r.borrow_mut().insert(id, env));
    id
}

/// Look up a closure environment by id. Returns None if not found (e.g. id from another thread).
pub fn closure_env_get(id: ClosureEnvId) -> Option<Env> {
    CLOSURE_ENV_REGISTRY.with(|r| r.borrow().get(&id).cloned())
}
