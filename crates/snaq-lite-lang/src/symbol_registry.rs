//! Symbol registry: named constants (e.g. pi, π, e) with optional numeric values.
//! Used to disambiguate identifiers (unit vs symbol) in resolve and to substitute symbols in numeric mode.

use std::collections::HashMap;

/// Registry mapping symbol names to numeric values for substitution.
///
/// Built-in constants: "pi", "π" → π; "e" → e; "sqrt_2" → √2; "sqrt_3" → √3; "phi" → φ.
/// Physical constants (dimensionless numeric values; combine with units for dimensional expressions):
/// "c" → speed of light (299792458 m/s in SI); "h" → Planck constant; "hbar" → ℏ = h/(2π); "R" → gas constant.
/// These are used for exact trig display (symbolic) and for numeric substitution.
/// Any identifier not in the unit registry is treated as a symbol; symbols not
/// present in this registry have no numeric value (e.g. user-defined names like `x`).
/// Use [SymbolRegistry::get] to substitute; missing symbols return `None` and
/// cause [crate::RunError::SymbolHasNoValue] when using [crate::Value::to_quantity].
#[derive(Clone, Default)]
pub struct SymbolRegistry {
    values: HashMap<String, f64>,
}

impl SymbolRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create the default registry with built-in constants: pi, π, e, sqrt_2, sqrt_3, phi, and physical constants c, h, hbar, R.
    pub fn default_registry() -> Self {
        let mut r = Self::new();
        r.insert("pi", std::f64::consts::PI);
        r.insert("π", std::f64::consts::PI);
        r.insert("e", std::f64::consts::E);
        r.insert("sqrt_2", 2_f64.sqrt());
        r.insert("sqrt_3", 3_f64.sqrt());
        r.insert("phi", (1.0 + 5_f64.sqrt()) / 2.0);
        // Physical constants (numeric values; use with units e.g. c * m / s for speed of light)
        r.insert("c", 299_792_458.0);                    // speed of light in m/s (exact)
        r.insert("h", 6.626_070_15e-34);                  // Planck constant (exact)
        r.insert("hbar", 6.626_070_15e-34 / (2.0 * std::f64::consts::PI)); // ℏ = h/(2π)
        r.insert("R", 8.314_462_618);                     // gas constant J/(mol·K)
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

    #[test]
    fn default_has_sqrt_2_and_sqrt_3() {
        let r = SymbolRegistry::default_registry();
        assert!((r.get("sqrt_2").unwrap() - 2_f64.sqrt()).abs() < 1e-15);
        assert!((r.get("sqrt_3").unwrap() - 3_f64.sqrt()).abs() < 1e-15);
    }

    #[test]
    fn default_has_physical_constants() {
        let r = SymbolRegistry::default_registry();
        assert!((r.get("c").unwrap() - 299_792_458.0).abs() < 1e-6);
        assert!((r.get("h").unwrap() - 6.626_070_15e-34).abs() < 1e-42);
        assert!((r.get("hbar").unwrap() - (6.626_070_15e-34 / (2.0 * std::f64::consts::PI))).abs() < 1e-42);
        assert!((r.get("R").unwrap() - 8.314_462_618).abs() < 1e-9);
    }
}
