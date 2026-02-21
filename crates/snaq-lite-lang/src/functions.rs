//! Built-in functions: sin, cos, tan (trig, one arg radians), max, min (two args, same dimension).

use crate::error::RunError;
use crate::quantity::{Quantity, SnaqNumber};
use crate::symbolic::{SymbolicExpr, SymbolicQuantity, Value};
use crate::unit::Unit;
use crate::unit_registry::UnitRegistry;

/// Parameter names for each built-in (order matters for positional binding).
pub fn param_names(name: &str) -> Option<&'static [&'static str]> {
    match name {
        "sin" | "cos" | "tan" => Some(&["x"]),
        "max" | "min" => Some(&["a", "b"]),
        _ => None,
    }
}

/// Evaluate a built-in function with resolved argument values.
/// All args must be numeric (Quantity) for trig and max/min; returns error on unknown function or bad arity/dimension.
/// Trig functions propagate variance via first-order propagation: Var(f(x)) ≈ (f'(x))² Var(x).
pub fn call_builtin(
    name: &str,
    param_values: &[Quantity],
    registry: &UnitRegistry,
) -> Result<Value, RunError> {
    match name {
        "sin" => {
            let x = exactly_one(param_values, "sin")?;
            let (v, u) = require_dimensionless(x.clone(), "sin")?;
            let var_x = x.variance();
            let result_value = v.sin();
            let result_variance = v.cos().powi(2) * var_x;
            Ok(Value::Numeric(Quantity::with_number(
                SnaqNumber::new(result_value, result_variance),
                u,
            )))
        }
        "cos" => {
            let x = exactly_one(param_values, "cos")?;
            let (v, u) = require_dimensionless(x.clone(), "cos")?;
            let var_x = x.variance();
            let result_value = v.cos();
            let result_variance = v.sin().powi(2) * var_x;
            Ok(Value::Numeric(Quantity::with_number(
                SnaqNumber::new(result_value, result_variance),
                u,
            )))
        }
        "tan" => {
            let x = exactly_one(param_values, "tan")?;
            let (v, u) = require_dimensionless(x.clone(), "tan")?;
            let var_x = x.variance();
            let result_value = v.tan();
            let result_variance = if result_value.is_finite() {
                let cos_v = v.cos();
                if cos_v != 0.0 {
                    var_x / cos_v.powi(4)
                } else {
                    0.0
                }
            } else {
                0.0
            };
            Ok(Value::Numeric(Quantity::with_number(
                SnaqNumber::new(result_value, result_variance),
                u,
            )))
        }
        "max" => {
            let (a, b) = exactly_two(param_values, "max")?;
            same_dimension_max_min(a, b, registry, |x, y| x.max(y))
        }
        "min" => {
            let (a, b) = exactly_two(param_values, "min")?;
            same_dimension_max_min(a, b, registry, |x, y| x.min(y))
        }
        _ => Err(RunError::UnknownFunction(name.to_string())),
    }
}

fn exactly_one(qs: &[Quantity], name: &str) -> Result<Quantity, RunError> {
    match qs {
        [q] => Ok(q.clone()),
        _ => Err(RunError::UnknownFunction(format!(
            "{name}: expected 1 argument, got {}",
            qs.len()
        ))),
    }
}

fn exactly_two(qs: &[Quantity], name: &str) -> Result<(Quantity, Quantity), RunError> {
    match qs {
        [a, b] => Ok((a.clone(), b.clone())),
        _ => Err(RunError::UnknownFunction(format!(
            "{name}: expected 2 arguments, got {}",
            qs.len()
        ))),
    }
}

fn require_dimensionless(q: Quantity, _name: &str) -> Result<(f64, Unit), RunError> {
    if !q.unit().is_scalar() {
        return Err(RunError::DimensionMismatch {
            left: q.unit().clone(),
            right: Unit::scalar(),
        });
    }
    Ok((q.value(), q.unit().clone()))
}

fn same_dimension_max_min<F>(
    a: Quantity,
    b: Quantity,
    registry: &UnitRegistry,
    op: F,
) -> Result<Value, RunError>
where
    F: FnOnce(f64, f64) -> f64,
{
    if !registry.same_dimension(a.unit(), b.unit()).unwrap_or(false) {
        return Err(RunError::DimensionMismatch {
            left: a.unit().clone(),
            right: b.unit().clone(),
        });
    }
    let result_unit = Quantity::smaller_unit(registry, a.unit(), b.unit())
        .cloned()
        .unwrap_or_else(|| a.unit().clone());
    let a_val = a.convert_to(registry, &result_unit).map_err(|e| match e {
        crate::quantity::QuantityError::DimensionMismatch { left, right } => {
            RunError::DimensionMismatch { left, right }
        }
        _ => RunError::DivisionByZero,
    })?.value();
    let b_val = b.convert_to(registry, &result_unit).map_err(|e| match e {
        crate::quantity::QuantityError::DimensionMismatch { left, right } => {
            RunError::DimensionMismatch { left, right }
        }
        _ => RunError::DivisionByZero,
    })?.value();
    let result = op(a_val, b_val);
    Ok(Value::Numeric(Quantity::new(result, result_unit)))
}

/// Build symbolic result for a call when any argument is symbolic (e.g. sin(pi) as expression).
pub fn symbolic_call(name: &str, args: &[SymbolicExpr], unit: Unit) -> Value {
    Value::Symbolic(SymbolicQuantity::new(
        SymbolicExpr::Call(name.to_string(), args.to_vec()),
        unit,
    ))
}

/// Try to evaluate a built-in when the call is represented as symbolic args (e.g. sin(pi) -> 0).
/// Substitute each arg with the symbol registry; if all substitute to numbers, call the built-in and return the result.
/// Used when folding symbolic calls during substitution (e.g. in [SymbolicExpr::substitute] for `Call` once unit registry is available).
pub fn try_eval_symbolic_call(
    name: &str,
    args: &[SymbolicExpr],
    unit_registry: &UnitRegistry,
    symbol_registry: &crate::symbol_registry::SymbolRegistry,
) -> Option<Value> {
    let mut qs = Vec::with_capacity(args.len());
    for e in args {
        let v = e.substitute(symbol_registry)?;
        qs.push(Quantity::from_scalar(v));
    }
    call_builtin(name, &qs, unit_registry).ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::unit_registry::default_si_registry;

    #[test]
    fn trig_sin_propagates_variance() {
        let x = 0.5_f64;
        let var_x = 0.01;
        let q = Quantity::with_number(
            SnaqNumber::new(x, var_x),
            Unit::scalar(),
        );
        let registry = default_si_registry();
        let v = call_builtin("sin", &[q], &registry).unwrap();
        let result = match &v {
            Value::Numeric(q) => q,
            _ => panic!("expected Numeric"),
        };
        let expected_var = x.cos().powi(2) * var_x;
        assert!(
            (result.variance() - expected_var).abs() < 1e-15,
            "sin: variance {} expected {}",
            result.variance(),
            expected_var
        );
    }

    #[test]
    fn trig_cos_propagates_variance() {
        let x = 0.5_f64;
        let var_x = 0.01;
        let q = Quantity::with_number(
            SnaqNumber::new(x, var_x),
            Unit::scalar(),
        );
        let registry = default_si_registry();
        let v = call_builtin("cos", &[q], &registry).unwrap();
        let result = match &v {
            Value::Numeric(q) => q,
            _ => panic!("expected Numeric"),
        };
        let expected_var = x.sin().powi(2) * var_x;
        assert!(
            (result.variance() - expected_var).abs() < 1e-15,
            "cos: variance {} expected {}",
            result.variance(),
            expected_var
        );
    }

    #[test]
    fn trig_tan_propagates_variance() {
        let x = 0.3_f64;
        let var_x = 0.01;
        let q = Quantity::with_number(
            SnaqNumber::new(x, var_x),
            Unit::scalar(),
        );
        let registry = default_si_registry();
        let v = call_builtin("tan", &[q], &registry).unwrap();
        let result = match &v {
            Value::Numeric(q) => q,
            _ => panic!("expected Numeric"),
        };
        let expected_var = var_x / x.cos().powi(4);
        assert!(
            (result.variance() - expected_var).abs() < 1e-15,
            "tan: variance {} expected {}",
            result.variance(),
            expected_var
        );
    }

    #[test]
    fn trig_tan_near_pole_succeeds_and_variance_non_negative() {
        // tan(π/2) is not exactly ±∞ in f64 (cos(π/2) is small but non-zero), so result is finite but large.
        // This test ensures we don't panic and variance remains non-negative.
        let x = std::f64::consts::FRAC_PI_2;
        let q = Quantity::with_number(
            SnaqNumber::new(x, 1.0),
            Unit::scalar(),
        );
        let registry = default_si_registry();
        let v = call_builtin("tan", &[q], &registry).unwrap();
        let result = match &v {
            Value::Numeric(q) => q,
            _ => panic!("expected Numeric"),
        };
        assert!(result.variance() >= 0.0, "variance must be non-negative");
    }
}
