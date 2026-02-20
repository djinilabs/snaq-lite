//! Symbol registry: named constants (e.g. pi, π, e) with optional numeric values.
//! Used to disambiguate identifiers (unit vs symbol) in resolve and to substitute symbols in numeric mode.

use std::collections::HashMap;

/// Registry mapping symbol names to numeric values for substitution.
///
/// Built-in constants: "pi", "π" → π; "e" → e. Any identifier not in the unit registry
/// is treated as a symbol; symbols not present in this registry have no numeric value
/// (e.g. user-defined names like `x`). Use [SymbolRegistry::get] to substitute; missing
/// symbols return `None` and cause [crate::RunError::SymbolHasNoValue] when using [crate::Value::to_quantity].
#[derive(Clone, Default)]
pub struct SymbolRegistry {
    values: HashMap<String, f64>,
}

impl SymbolRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create the default registry with built-in constants: pi, π, e.
    pub fn default_registry() -> Self {
        let mut r = Self::new();
        r.insert("pi", std::f64::consts::PI);
        r.insert("π", std::f64::consts::PI);
        r.insert("e", std::f64::consts::E);
        r
    }

    /// Register a symbol with a numeric value (for substitution in [crate::run_numeric]).
    pub fn insert(&mut self, name: impl Into<String>, value: f64) {
        self.values.insert(name.into(), value);
    }

    /// Return the numeric value for a symbol, if defined.
    pub fn get(&self, name: &str) -> Option<f64> {
        self.values.get(name).copied()
    }

}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_has_pi_and_e() {
        let r = SymbolRegistry::default_registry();
        assert!((r.get("pi").unwrap() - std::f64::consts::PI).abs() < 1e-15);
        assert!((r.get("π").unwrap() - std::f64::consts::PI).abs() < 1e-15);
        assert!((r.get("e").unwrap() - std::f64::consts::E).abs() < 1e-15);
    }

    #[test]
    fn unknown_symbol_has_no_value() {
        let r = SymbolRegistry::default_registry();
        assert_eq!(r.get("foo"), None);
    }
}
