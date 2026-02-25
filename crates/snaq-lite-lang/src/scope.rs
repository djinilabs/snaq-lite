//! Lexical scope (environment) for variable bindings.
//!
//! Environments are immutable and implemented with a persistent map so that
//! extending the scope returns a new map that shares structure with the old one.
//! Scope is Salsa-interned so that (scope, expr) is the memoization key for evaluation.

use crate::fuzzy::FuzzyBool;
use crate::quantity::Quantity;
use crate::symbolic::Value;
use crate::vector_registry;
use im::OrdMap;
use std::hash::{Hash, Hasher};
use std::fmt;

/// Value that can be stored in the scope map. Must be Eq + Hash (Scope is Salsa-interned by Env).
/// Bindings are unified here: each variable name maps to exactly one StoredValue.
/// For vectors we store an id; the actual payload lives in [vector_registry](crate::vector_registry) (VectorValue is not Hash).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum StoredValue {
    Numeric(Quantity),
    FuzzyBool(FuzzyBool),
    Undefined,
    /// User-defined function (id into user_function registry).
    Function(crate::user_function::UserFunctionId),
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
            Value::Function(id) => Ok(StoredValue::Function(*id)),
        }
    }

    /// Convert to runtime Value.
    pub fn to_value(&self) -> Value {
        match self {
            StoredValue::Numeric(q) => Value::Numeric(q.clone()),
            StoredValue::FuzzyBool(fb) => Value::FuzzyBool(fb.clone()),
            StoredValue::Undefined => Value::Undefined,
            StoredValue::Function(id) => Value::Function(*id),
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
