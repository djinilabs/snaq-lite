//! Variance mode and helpers for stream import (CSV, newline-delimited).
//! Used when parsing numbers from external files: zero variance (exact) or infer from decimal places.
//! The **infer** rule matches [crate::ir::NumLiteral] (decimal places in the text → implicit variance).

/// How to assign variance to numbers read from a stream (e.g. CSV or newline-delimited file).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum StreamVarianceMode {
    /// Treat all numbers as exact (variance 0).
    #[default]
    Zero,
    /// Infer variance from the number of decimal places in the text (same rule as language literals).
    InferFromDecimalPlaces,
}

impl StreamVarianceMode {
    /// Whether variance is inferred from decimal places in the text (CSV cells or newline-delimited lines).
    pub fn is_infer(self) -> bool {
        matches!(self, StreamVarianceMode::InferFromDecimalPlaces)
    }
}

/// Compute (value, variance) from a numeric string using the same rule as [crate::ir::NumLiteral]:
/// no decimal point → abs_err 0.5, N decimal places → abs_err = 5×10^−(N+1), variance = abs_err².
/// Returns `None` if the string does not parse as a finite f64.
pub fn decimal_string_to_quantity(s: &str) -> Option<(f64, f64)> {
    let value: f64 = s.trim().parse().ok()?;
    if !value.is_finite() {
        return None;
    }
    let variance = implicit_variance_from_string(s.trim());
    Some((value, variance))
}

/// Decimal places in the mantissa (digits after '.' before any 'e'/'E').
fn decimal_places_after(s: &str) -> Option<usize> {
    let mantissa = s
        .split_once(|c| ['e', 'E'].contains(&c))
        .map(|(m, _)| m)
        .unwrap_or(s);
    let dot = mantissa.find('.')?;
    Some(
        mantissa[dot + 1..]
            .chars()
            .filter(|c| c.is_ascii_digit())
            .count(),
    )
}

/// Implicit absolute error: no decimal point → 0.5; N decimal places → 5×10^−(N+1).
fn implicit_absolute_error_from_string(s: &str) -> f64 {
    match decimal_places_after(s) {
        None => 0.5,
        Some(n) => 5.0 * 10.0_f64.powi(-(n as i32 + 1)),
    }
}

/// Variance = (implicit absolute error)².
fn implicit_variance_from_string(s: &str) -> f64 {
    let err = implicit_absolute_error_from_string(s);
    err * err
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decimal_string_to_quantity_integer_no_decimal() {
        let (v, var) = decimal_string_to_quantity("10").expect("parse");
        assert_eq!(v, 10.0);
        assert_eq!(var, 0.25); // 0.5^2
    }

    #[test]
    fn decimal_string_to_quantity_one_decimal_place() {
        let (v, var) = decimal_string_to_quantity("10.5").expect("parse");
        assert_eq!(v, 10.5);
        // 1 decimal → abs_err = 5e-2, var = 2.5e-3
        assert!((var - 0.0025).abs() < 1e-10);
    }

    #[test]
    fn decimal_string_to_quantity_two_decimal_places() {
        let (v, var) = decimal_string_to_quantity("10.50").expect("parse");
        assert_eq!(v, 10.5);
        // 2 decimals → abs_err = 5e-3, var = 2.5e-5
        assert!(var < 0.0025, "10.50 should have smaller variance than 10.5");
        assert!((var - 2.5e-5).abs() < 1e-12);
    }

    #[test]
    fn decimal_string_to_quantity_whitespace_trimmed() {
        let (v, var) = decimal_string_to_quantity("  3.14  ").expect("parse");
        assert_eq!(v, 3.14);
        assert!(var > 0.0);
    }

    #[test]
    fn decimal_string_to_quantity_invalid_returns_none() {
        assert!(decimal_string_to_quantity("not a number").is_none());
        assert!(decimal_string_to_quantity("").is_none());
    }

    #[test]
    fn decimal_string_to_quantity_scientific_notation_uses_mantissa_decimal_places() {
        // 1.50e2 → value 150, variance from 2 decimal places in mantissa "1.50"
        let (v, var) = decimal_string_to_quantity("1.50e2").expect("parse");
        assert_eq!(v, 150.0);
        assert!((var - 2.5e-5).abs() < 1e-12, "2 decimals → var = 2.5e-5, got {var}");
    }

    #[test]
    fn decimal_string_to_quantity_non_finite_returns_none() {
        assert!(decimal_string_to_quantity("inf").is_none());
        assert!(decimal_string_to_quantity("-inf").is_none());
        assert!(decimal_string_to_quantity("nan").is_none());
    }

    #[test]
    fn stream_variance_mode_default_is_zero() {
        assert_eq!(StreamVarianceMode::default(), StreamVarianceMode::Zero);
    }

    #[test]
    fn stream_variance_mode_is_infer() {
        assert!(!StreamVarianceMode::Zero.is_infer());
        assert!(StreamVarianceMode::InferFromDecimalPlaces.is_infer());
    }
}
