//! User-defined functions: closure representation (hashable, no registry).
//! The function (params, body, closure_env_id) is stored inline in Value/StoredValue.
//! Captured environment is stored in scope's closure-env registry to break the type cycle.

use crate::ir::ExprDef;

/// A user-defined function: params (with optional defaults), body, and id of captured env.
/// Stored directly in scope/Value; closure env is looked up by closure_env_id when calling.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct UserFunction {
    /// (param name, optional default expression).
    pub params: Vec<(String, Option<Box<ExprDef>>)>,
    pub body: Box<ExprDef>,
    /// Id into scope's closure-env registry (actual Env stored there to avoid type cycle).
    pub closure_env_id: u64,
}

impl UserFunction {
    pub fn new(
        params: Vec<(String, Option<Box<ExprDef>>)>,
        body: Box<ExprDef>,
        closure_env_id: u64,
    ) -> Self {
        Self {
            params,
            body,
            closure_env_id,
        }
    }
}
