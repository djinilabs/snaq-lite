//! Built-in functions: trig (sin, cos, tan), inverse trig (asin, acos, atan, atan2), hyperbolic (sinh, cosh, tanh, asinh, acosh, atanh),
//! elementary (sqrt, cbrt, abs, sign, floor, ceil, round, trunc), exp/log (exp, ln, log10, log2), pow, mod,
//! probability (norm_cdf, norm_inv, factorial, binom, perm), number theory (gcd, lcm), max, min, take.
//! For well-known angles, exact symbolic results (0, 1, √2/2, etc.) are returned when possible.

use crate::error::{RunError, RunErrorKind};
use crate::quantity::{Quantity, SnaqNumber};
use crate::symbolic::{SymbolicExpr, SymbolicQuantity, Value};
use crate::unit::Unit;
use crate::unit_registry::UnitRegistry;
use statrs::distribution::{ContinuousCDF, Normal};

use std::f64::consts::FRAC_PI_2;

fn factorial_f64(n: u64) -> f64 {
    if n > 170 {
        f64::INFINITY
    } else {
        (1..=n).map(|i| i as f64).product()
    }
}

fn binom_f64(n: u64, k: u64) -> f64 {
    if k > n {
        0.0
    } else {
        factorial_f64(n) / (factorial_f64(k) * factorial_f64(n - k))
    }
}

fn perm_f64(n: u64, k: u64) -> f64 {
    if k > n {
        0.0
    } else {
        (n - k + 1..=n).map(|i| i as f64).product()
    }
}

fn gcd_u64(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

/// Well-known angle as a fraction of π (0, 1/6, 1/4, 1/3, 1/2, 1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KnownAngle {
    Zero,
    PiSixth,
    PiFourth,
    PiThird,
    PiHalf,
    Pi,
}

impl KnownAngle {
    pub fn rad_value(self) -> f64 {
        match self {
            KnownAngle::Zero => 0.0,
            KnownAngle::PiSixth => std::f64::consts::PI / 6.0,
            KnownAngle::PiFourth => std::f64::consts::PI / 4.0,
            KnownAngle::PiThird => std::f64::consts::PI / 3.0,
            KnownAngle::PiHalf => FRAC_PI_2,
            KnownAngle::Pi => std::f64::consts::PI,
        }
    }
}

const TWO_PI: f64 = std::f64::consts::TAU;
/// Epsilon for matching a radian value to a known angle. Must be large enough to absorb
/// rounding from unit conversion (e.g. 90 degree → π/2 rad via 90 * (π/180)).
const TRIG_EPS: f64 = 1e-8;

/// Result of matching an angle: the base known angle and whether sin/cos are negated (angle in (π, 2π)).
#[derive(Clone, Copy, Debug)]
pub struct KnownAngleMatch {
    pub angle: KnownAngle,
    /// When true, sin(π + x) = -sin(x), cos(π + x) = -cos(x), tan(π + x) = tan(x).
    pub negate_sin_cos: bool,
}

/// If `rad` (in radians) is close to a well-known angle a or a + π (normalized to [0, 2π)), return the match.
pub fn known_angle_from_rad(rad: f64) -> Option<KnownAngleMatch> {
    let r = rad.rem_euclid(TWO_PI);
    // Check [0, π] first
    for &angle in &[
        KnownAngle::Zero,
        KnownAngle::PiSixth,
        KnownAngle::PiFourth,
        KnownAngle::PiThird,
        KnownAngle::PiHalf,
        KnownAngle::Pi,
    ] {
        if (r - angle.rad_value()).abs() < TRIG_EPS {
            return Some(KnownAngleMatch {
                angle,
                negate_sin_cos: false,
            });
        }
    }
    // Check (π, 2π): r = π + base, so base = r - π
    let base = r - std::f64::consts::PI;
    for &angle in &[
        KnownAngle::Zero,
        KnownAngle::PiSixth,
        KnownAngle::PiFourth,
        KnownAngle::PiThird,
        KnownAngle::PiHalf,
    ] {
        if (base - angle.rad_value()).abs() < TRIG_EPS {
            return Some(KnownAngleMatch {
                angle,
                negate_sin_cos: true,
            });
        }
    }
    None
}

/// Try to interpret the scalar expression (angle in rad or degree) as a well-known angle.
/// For rad: expr = k*π for any k (e.g. pi, pi/4, pi + pi/4, 2*pi - pi/4); reduced modulo 2π.
/// For degree: expr should be a number 0, 30, 45, 60, 90, 180, 210, 225, 240, 270, 360, etc.
pub fn known_angle_from_symbolic(
    expr: &SymbolicExpr,
    unit: &Unit,
    registry: &UnitRegistry,
) -> Option<KnownAngleMatch> {
    let rad = Unit::from_base_unit("rad");
    let degree = Unit::from_base_unit("degree");
    if registry.same_dimension(unit, &rad).unwrap_or(false) {
        let k = expr_as_pi_multiple(expr)?;
        let r = k.rem_euclid(2.0);
        let frac_eps = 1e-9;
        let (base, negate) = if r > 1.0 {
            (r - 1.0, true)
        } else {
            (r, false)
        };
        let angle = if base.abs() < frac_eps {
            KnownAngle::Zero
        } else if (base - 1.0 / 6.0).abs() < frac_eps {
            KnownAngle::PiSixth
        } else if (base - 1.0 / 4.0).abs() < frac_eps {
            KnownAngle::PiFourth
        } else if (base - 1.0 / 3.0).abs() < frac_eps {
            KnownAngle::PiThird
        } else if (base - 1.0 / 2.0).abs() < frac_eps {
            KnownAngle::PiHalf
        } else if (base - 1.0).abs() < frac_eps {
            KnownAngle::Pi
        } else {
            return None;
        };
        return Some(KnownAngleMatch { angle, negate_sin_cos: negate });
    }
    if registry.same_dimension(unit, &degree).unwrap_or(false) {
        let d = expr_as_number(expr)?;
        let deg = d.rem_euclid(360.0);
        let (angle, negate) = match (deg.round() as i32 + 360) % 360 {
            0 => (KnownAngle::Zero, false),
            30 => (KnownAngle::PiSixth, false),
            45 => (KnownAngle::PiFourth, false),
            60 => (KnownAngle::PiThird, false),
            90 => (KnownAngle::PiHalf, false),
            180 => (KnownAngle::Pi, false),
            210 => (KnownAngle::PiSixth, true),
            225 => (KnownAngle::PiFourth, true),
            240 => (KnownAngle::PiThird, true),
            270 => (KnownAngle::PiHalf, true),
            _ => return None,
        };
        return Some(KnownAngleMatch { angle, negate_sin_cos: negate });
    }
    None
}

/// Extract numeric value if the expression is a constant number.
fn expr_as_number(expr: &SymbolicExpr) -> Option<f64> {
    match expr {
        SymbolicExpr::Number(x) => Some(*x),
        SymbolicExpr::Sum { constant, terms, rest } if terms.is_empty() && rest.is_empty() => {
            Some(*constant)
        }
        _ => None,
    }
}

/// If expr represents k*π for some k, return k. Handles 0, pi, pi/2, pi+pi/4, 2*pi, etc.
fn expr_as_pi_multiple(expr: &SymbolicExpr) -> Option<f64> {
    match expr {
        SymbolicExpr::Number(x) => {
            if x.abs() < TRIG_EPS {
                Some(0.0)
            } else {
                None
            }
        }
        SymbolicExpr::Symbol(s) if s == "pi" || s == "π" => Some(1.0),
        SymbolicExpr::Product { coef, symbols } => {
            if symbols.len() == 1 && (symbols[0] == "pi" || symbols[0] == "π") {
                Some(*coef)
            } else {
                None
            }
        }
        SymbolicExpr::Div(a, b) => {
            let num = a.as_ref();
            let den = b.as_ref();
            let den_val = expr_as_number(den)?;
            if den_val.abs() < 1e-15 {
                return None;
            }
            match num {
                SymbolicExpr::Symbol(s) if s == "pi" || s == "π" => Some(1.0 / den_val),
                SymbolicExpr::Product { coef, symbols } if symbols.len() == 1 && (symbols[0] == "pi" || symbols[0] == "π") => {
                    Some(*coef / den_val)
                }
                _ => None,
            }
        }
        SymbolicExpr::Sum {
            constant,
            terms,
            rest,
        } => {
            if constant.abs() >= 1e-15 {
                return None;
            }
            let mut k = 0.0_f64;
            for (coef, syms) in terms {
                if syms.len() == 1 && (syms[0] == "pi" || syms[0] == "π") {
                    k += coef;
                } else {
                    return None;
                }
            }
            for e in rest {
                k += expr_as_pi_multiple(e)?;
            }
            Some(k)
        }
        SymbolicExpr::Neg(inner) => expr_as_pi_multiple(inner).map(|x| -x),
        _ => None,
    }
}

/// Exact symbolic result for sin at a well-known angle. Variance is 0 (exact).
pub fn exact_sin(angle: KnownAngle) -> SymbolicExpr {
    match angle {
        KnownAngle::Zero => SymbolicExpr::Number(0.0),
        KnownAngle::PiSixth => SymbolicExpr::Number(0.5),
        KnownAngle::PiFourth => SymbolicExpr::div(
            &SymbolicExpr::symbol("sqrt_2"),
            &SymbolicExpr::Number(2.0),
        ),
        KnownAngle::PiThird => SymbolicExpr::div(
            &SymbolicExpr::symbol("sqrt_3"),
            &SymbolicExpr::Number(2.0),
        ),
        KnownAngle::PiHalf => SymbolicExpr::Number(1.0),
        KnownAngle::Pi => SymbolicExpr::Number(0.0),
    }
}

/// Exact symbolic result for cos at a well-known angle.
pub fn exact_cos(angle: KnownAngle) -> SymbolicExpr {
    match angle {
        KnownAngle::Zero => SymbolicExpr::Number(1.0),
        KnownAngle::PiSixth => SymbolicExpr::div(
            &SymbolicExpr::symbol("sqrt_3"),
            &SymbolicExpr::Number(2.0),
        ),
        KnownAngle::PiFourth => SymbolicExpr::div(
            &SymbolicExpr::symbol("sqrt_2"),
            &SymbolicExpr::Number(2.0),
        ),
        KnownAngle::PiThird => SymbolicExpr::Number(0.5),
        KnownAngle::PiHalf => SymbolicExpr::Number(0.0),
        KnownAngle::Pi => SymbolicExpr::Number(-1.0),
    }
}

/// Exact symbolic result for tan at a well-known angle. Returns None for π/2 (undefined).
/// tan(π + x) = tan(x), so no negate flag.
pub fn exact_tan(angle: KnownAngle) -> Option<SymbolicExpr> {
    match angle {
        KnownAngle::Zero => Some(SymbolicExpr::Number(0.0)),
        KnownAngle::PiSixth => Some(SymbolicExpr::div(
            &SymbolicExpr::Number(1.0),
            &SymbolicExpr::symbol("sqrt_3"),
        )),
        KnownAngle::PiFourth => Some(SymbolicExpr::Number(1.0)),
        KnownAngle::PiThird => Some(SymbolicExpr::symbol("sqrt_3")),
        KnownAngle::PiHalf => None, // pole
        KnownAngle::Pi => Some(SymbolicExpr::Number(0.0)),
    }
}

/// Exact sin for a known-angle match (handles a + n*π via negate_sin_cos).
pub fn exact_sin_match(m: KnownAngleMatch) -> SymbolicExpr {
    let e = exact_sin(m.angle);
    if m.negate_sin_cos {
        SymbolicExpr::neg(&e)
    } else {
        e
    }
}

/// Exact cos for a known-angle match (handles a + n*π via negate_sin_cos).
pub fn exact_cos_match(m: KnownAngleMatch) -> SymbolicExpr {
    let e = exact_cos(m.angle);
    if m.negate_sin_cos {
        SymbolicExpr::neg(&e)
    } else {
        e
    }
}

/// Exact tan for a known-angle match. tan(π + x) = tan(x), so no negate.
pub fn exact_tan_match(m: KnownAngleMatch) -> Option<SymbolicExpr> {
    exact_tan(m.angle)
}

/// Parameter names for each built-in (order matters for positional binding).
pub fn param_names(name: &str) -> Option<&'static [&'static str]> {
    match name {
        "sin" | "cos" | "tan" | "sqrt" | "cbrt" | "abs" | "sign" | "floor" | "ceil" | "round" | "trunc"
        | "exp" | "ln" | "log" | "log10" | "log2" | "asin" | "acos" | "atan"
        | "sinh" | "cosh" | "tanh" | "asinh" | "acosh" | "atanh"
        | "norm_cdf" | "norm_inv" | "factorial" => Some(&["x"]),
        "max" | "min" | "mod" | "gcd" | "lcm" | "corr" => Some(&["a", "b"]),
        "pow" => Some(&["x", "n"]),
        "binom" | "perm" => Some(&["n", "k"]),
        "atan2" => Some(&["y", "x"]),
        "take" => Some(&["vector", "start", "length"]),
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
        "sin" => eval_trig(param_values, registry, "sin", |v, var_x| {
            (v.sin(), v.cos().powi(2) * var_x)
        }),
        "cos" => eval_trig(param_values, registry, "cos", |v, var_x| {
            (v.cos(), v.sin().powi(2) * var_x)
        }),
        "tan" => eval_trig(param_values, registry, "tan", |v, var_x| {
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
            (result_value, result_variance)
        }),
        "max" => {
            let (a, b) = exactly_two(param_values, "max")?;
            same_dimension_max_min(a, b, registry, |x, y| x.max(y))
        }
        "min" => {
            let (a, b) = exactly_two(param_values, "min")?;
            same_dimension_max_min(a, b, registry, |x, y| x.min(y))
        }
        "sqrt" => {
            let x = exactly_one(param_values, "sqrt")?;
            let v = x.value();
            if v < 0.0 {
                return Err(RunError::new(RunErrorKind::InvalidArgument(
                    "sqrt: argument must be non-negative".to_string(),
                )));
            }
            let result_value = v.sqrt();
            let var_x = x.variance();
            // Var(sqrt(x)) ≈ (1/(2*sqrt(x)))^2 * Var(x) = Var(x)/(4*x); for x <= 0 use 0
            let result_variance = if v > 0.0 && result_value > 0.0 {
                var_x / (4.0 * v)
            } else {
                0.0
            };
            let half = crate::dimension::Exponent::new(1, 2);
            Ok(Value::Numeric(Quantity::with_number(
                SnaqNumber::new(result_value, result_variance),
                x.unit().clone().power(half),
            )))
        }
        "abs" => {
            let x = exactly_one(param_values, "abs")?;
            let v = x.value();
            let result_value = v.abs();
            let result_variance = x.variance(); // variance unchanged for abs
            Ok(Value::Numeric(Quantity::with_number(
                SnaqNumber::new(result_value, result_variance),
                x.unit().clone(),
            )))
        }
        "sign" => {
            let x = exactly_one(param_values, "sign")?;
            let (v, _) = require_dimensionless(&x, registry, "sign")?;
            let result_value = if v > 0.0 { 1.0 } else if v < 0.0 { -1.0 } else { 0.0 };
            Ok(Value::Numeric(Quantity::new(result_value, Unit::scalar())))
        }
        "floor" | "ceil" | "round" | "trunc" => {
            let x = exactly_one(param_values, name)?;
            let v = x.value();
            let result_value = match name {
                "floor" => v.floor(),
                "ceil" => v.ceil(),
                "round" => v.round(),
                "trunc" => v.trunc(),
                _ => unreachable!(),
            };
            Ok(Value::Numeric(Quantity::with_number(
                SnaqNumber::new(result_value, 0.0),
                x.unit().clone(),
            )))
        }
        "mod" => {
            let (a, b) = exactly_two(param_values, "mod")?;
            if !registry.same_dimension(a.unit(), b.unit()).unwrap_or(false) {
                return Err(RunError::new(RunErrorKind::DimensionMismatch {
                    left: a.unit().clone(),
                    right: b.unit().clone(),
                }));
            }
            let b_val = b.value();
            if b_val == 0.0 {
                return Err(RunError::new(RunErrorKind::DivisionByZero));
            }
            let a_val = a.value();
            let result_value = a_val.rem_euclid(b_val);
            let result_unit = a.unit().clone();
            Ok(Value::Numeric(Quantity::new(result_value, result_unit)))
        }
        "exp" => {
            let x = exactly_one(param_values, "exp")?;
            let (v, var_x) = require_dimensionless(&x, registry, "exp")?;
            let result_value = v.exp();
            let result_variance = result_value * result_value * var_x;
            Ok(Value::Numeric(Quantity::with_number(
                SnaqNumber::new(result_value, result_variance),
                Unit::scalar(),
            )))
        }
        "ln" | "log" => {
            let x = exactly_one(param_values, name)?;
            let (v, var_x) = require_dimensionless(&x, registry, name)?;
            if v <= 0.0 {
                return Err(RunError::new(RunErrorKind::InvalidArgument(
                    format!("{name}: argument must be positive"),
                )));
            }
            let result_value = v.ln();
            let result_variance = var_x / (v * v);
            Ok(Value::Numeric(Quantity::with_number(
                SnaqNumber::new(result_value, result_variance),
                Unit::scalar(),
            )))
        }
        "log10" => {
            let x = exactly_one(param_values, "log10")?;
            let (v, var_x) = require_dimensionless(&x, registry, "log10")?;
            if v <= 0.0 {
                return Err(RunError::new(RunErrorKind::InvalidArgument(
                    "log10: argument must be positive".to_string(),
                )));
            }
            let result_value = v.log10();
            let ln10 = 10.0_f64.ln();
            let result_variance = var_x / (v * v * ln10 * ln10);
            Ok(Value::Numeric(Quantity::with_number(
                SnaqNumber::new(result_value, result_variance),
                Unit::scalar(),
            )))
        }
        "log2" => {
            let x = exactly_one(param_values, "log2")?;
            let (v, var_x) = require_dimensionless(&x, registry, "log2")?;
            if v <= 0.0 {
                return Err(RunError::new(RunErrorKind::InvalidArgument(
                    "log2: argument must be positive".to_string(),
                )));
            }
            let result_value = v.log2();
            let ln2 = 2.0_f64.ln();
            let result_variance = var_x / (v * v * ln2 * ln2);
            Ok(Value::Numeric(Quantity::with_number(
                SnaqNumber::new(result_value, result_variance),
                Unit::scalar(),
            )))
        }
        "asin" | "acos" => {
            let x = exactly_one(param_values, name)?;
            let (v, _) = require_dimensionless(&x, registry, name)?;
            if !(-1.0..=1.0).contains(&v) {
                return Err(RunError::new(RunErrorKind::InvalidArgument(
                    format!("{name}: argument must be in [-1, 1]"),
                )));
            }
            let result_value = match name {
                "asin" => v.asin(),
                "acos" => v.acos(),
                _ => unreachable!(),
            };
            let rad = Unit::from_base_unit("rad");
            Ok(Value::Numeric(Quantity::new(result_value, rad)))
        }
        "atan" => {
            let x = exactly_one(param_values, "atan")?;
            let (v, _) = require_dimensionless(&x, registry, "atan")?;
            let result_value = v.atan();
            let rad = Unit::from_base_unit("rad");
            Ok(Value::Numeric(Quantity::new(result_value, rad)))
        }
        "atan2" => {
            let (y, x) = exactly_two(param_values, "atan2")?;
            if !registry.same_dimension(y.unit(), x.unit()).unwrap_or(false) {
                return Err(RunError::new(RunErrorKind::DimensionMismatch {
                    left: y.unit().clone(),
                    right: x.unit().clone(),
                }));
            }
            let y_val = y.value();
            let x_val = x.value();
            let result_value = y_val.atan2(x_val);
            let rad = Unit::from_base_unit("rad");
            Ok(Value::Numeric(Quantity::new(result_value, rad)))
        }
        "sinh" | "cosh" | "tanh" | "asinh" | "acosh" | "atanh" => {
            let x = exactly_one(param_values, name)?;
            let (v, var_x) = require_dimensionless(&x, registry, name)?;
            let (result_value, result_variance) = match name {
                "sinh" => {
                    let r = v.sinh();
                    (r, v.cosh().powi(2) * var_x)
                }
                "cosh" => {
                    let r = v.cosh();
                    (r, v.sinh().powi(2) * var_x)
                }
                "tanh" => {
                    let r = v.tanh();
                    let sech2 = (1.0 - r * r).max(0.0);
                    (r, sech2 * sech2 * var_x)
                }
                "asinh" => (v.asinh(), var_x / (1.0 + v * v)),
                "acosh" => {
                    if v < 1.0 {
                        return Err(RunError::new(RunErrorKind::InvalidArgument(
                            "acosh: argument must be >= 1".to_string(),
                        )));
                    }
                    (v.acosh(), var_x / ((v * v - 1.0).max(0.0)))
                }
                "atanh" => {
                    if !(-1.0..1.0).contains(&v) {
                        return Err(RunError::new(RunErrorKind::InvalidArgument(
                            "atanh: argument must be in (-1, 1)".to_string(),
                        )));
                    }
                    (v.atanh(), var_x / (1.0 - v * v).powi(2))
                }
                _ => unreachable!(),
            };
            Ok(Value::Numeric(Quantity::with_number(
                SnaqNumber::new(result_value, result_variance),
                Unit::scalar(),
            )))
        }
        "pow" => {
            let (base, exp) = exactly_two(param_values, "pow")?;
            let (exp_val, _) = require_dimensionless(&exp, registry, "pow")?;
            let result_value = base.value().powf(exp_val);
            if !result_value.is_finite() {
                return Err(RunError::new(RunErrorKind::InvalidArgument(
                    "pow: result is not finite".to_string(),
                )));
            }
            let third = crate::dimension::Exponent::new(1, 3);
            let half = crate::dimension::Exponent::new(1, 2);
            let result_unit = if (exp_val - 0.5).abs() < 1e-10 {
                base.unit().clone().power(half)
            } else if (exp_val - 1.0 / 3.0).abs() < 1e-10 {
                base.unit().clone().power(third)
            } else if (exp_val - exp_val.round()).abs() < 1e-10 {
                base.unit().clone().power(crate::dimension::Exponent::from_integer(exp_val.round() as i64))
            } else if registry.same_dimension(base.unit(), &Unit::scalar()).unwrap_or(false) {
                Unit::scalar()
            } else {
                return Err(RunError::new(RunErrorKind::InvalidArgument(
                    "pow: non-integer exponent requires dimensionless base".to_string(),
                )));
            };
            Ok(Value::Numeric(Quantity::new(result_value, result_unit)))
        }
        "cbrt" => {
            let x = exactly_one(param_values, "cbrt")?;
            let result_value = x.value().cbrt();
            let var_x = x.variance();
            let v = x.value();
            let result_variance = if v != 0.0 {
                let cbrt_v = v.cbrt();
                var_x / (9.0 * cbrt_v.powi(4))
            } else {
                0.0
            };
            let third = crate::dimension::Exponent::new(1, 3);
            Ok(Value::Numeric(Quantity::with_number(
                SnaqNumber::new(result_value, result_variance),
                x.unit().clone().power(third),
            )))
        }
        "norm_cdf" => {
            let x = exactly_one(param_values, "norm_cdf")?;
            let (v, _) = require_dimensionless(&x, registry, "norm_cdf")?;
            let dist = Normal::new(0.0, 1.0).map_err(|_| RunError::new(RunErrorKind::InvalidArgument("norm_cdf".to_string())))?;
            let result_value = dist.cdf(v);
            Ok(Value::Numeric(Quantity::new(result_value, Unit::scalar())))
        }
        "norm_inv" => {
            let p = exactly_one(param_values, "norm_inv")?;
            let (v, _) = require_dimensionless(&p, registry, "norm_inv")?;
            if !(0.0..1.0).contains(&v) {
                return Err(RunError::new(RunErrorKind::InvalidArgument(
                    "norm_inv: argument must be in (0, 1)".to_string(),
                )));
            }
            let dist = Normal::new(0.0, 1.0).map_err(|_| RunError::new(RunErrorKind::InvalidArgument("norm_inv".to_string())))?;
            let result_value = dist.inverse_cdf(v);
            Ok(Value::Numeric(Quantity::new(result_value, Unit::scalar())))
        }
        "factorial" => {
            let x = exactly_one(param_values, "factorial")?;
            let (v, _) = require_dimensionless(&x, registry, "factorial")?;
            let n = v.round() as i64;
            if n < 0 || (v - n as f64).abs() > 1e-10 {
                return Err(RunError::new(RunErrorKind::InvalidArgument(
                    "factorial: argument must be non-negative integer".to_string(),
                )));
            }
            let result_value = factorial_f64(n as u64);
            Ok(Value::Numeric(Quantity::new(result_value, Unit::scalar())))
        }
        "binom" => {
            let (n, k) = exactly_two(param_values, "binom")?;
            let (n_val, _) = require_dimensionless(&n, registry, "binom")?;
            let (k_val, _) = require_dimensionless(&k, registry, "binom")?;
            let nn = n_val.round() as i64;
            let kk = k_val.round() as i64;
            if nn < 0 || kk < 0 || kk > nn {
                return Err(RunError::new(RunErrorKind::InvalidArgument(
                    "binom: require 0 <= k <= n (integers)".to_string(),
                )));
            }
            let result_value = binom_f64(nn as u64, kk as u64);
            Ok(Value::Numeric(Quantity::new(result_value, Unit::scalar())))
        }
        "perm" => {
            let (n, k) = exactly_two(param_values, "perm")?;
            let (n_val, _) = require_dimensionless(&n, registry, "perm")?;
            let (k_val, _) = require_dimensionless(&k, registry, "perm")?;
            let nn = n_val.round() as i64;
            let kk = k_val.round() as i64;
            if nn < 0 || kk < 0 || kk > nn {
                return Err(RunError::new(RunErrorKind::InvalidArgument(
                    "perm: require 0 <= k <= n (integers)".to_string(),
                )));
            }
            let result_value = perm_f64(nn as u64, kk as u64);
            Ok(Value::Numeric(Quantity::new(result_value, Unit::scalar())))
        }
        "gcd" => {
            let (a, b) = exactly_two(param_values, "gcd")?;
            let (a_val, _) = require_dimensionless(&a, registry, "gcd")?;
            let (b_val, _) = require_dimensionless(&b, registry, "gcd")?;
            let aa = a_val.round() as i64;
            let bb = b_val.round() as i64;
            if aa < 0 || bb < 0 {
                return Err(RunError::new(RunErrorKind::InvalidArgument(
                    "gcd: arguments must be non-negative integers".to_string(),
                )));
            }
            let result_value = gcd_u64(aa as u64, bb as u64) as f64;
            Ok(Value::Numeric(Quantity::new(result_value, Unit::scalar())))
        }
        "lcm" => {
            let (a, b) = exactly_two(param_values, "lcm")?;
            let (a_val, _) = require_dimensionless(&a, registry, "lcm")?;
            let (b_val, _) = require_dimensionless(&b, registry, "lcm")?;
            let aa = a_val.round() as i64;
            let bb = b_val.round() as i64;
            if aa < 0 || bb < 0 {
                return Err(RunError::new(RunErrorKind::InvalidArgument(
                    "lcm: arguments must be non-negative integers".to_string(),
                )));
            }
            let g = gcd_u64(aa as u64, bb as u64);
            let result_value = if g == 0 { 0.0 } else { (aa as u64 * bb as u64 / g) as f64 };
            Ok(Value::Numeric(Quantity::new(result_value, Unit::scalar())))
        }
        _ => Err(RunError::new(RunErrorKind::UnknownFunction(name.to_string()))),
    }
}

/// Shared path for sin, cos, tan: one angle arg, convert to rad, then apply op to get (value, variance).
fn eval_trig<F>(
    param_values: &[Quantity],
    registry: &UnitRegistry,
    name: &str,
    op: F,
) -> Result<Value, RunError>
where
    F: FnOnce(f64, f64) -> (f64, f64),
{
    let x = exactly_one(param_values, name)?;
    let in_rad = require_angle(x, registry, name)?;
    let v = in_rad.value();
    let var_x = in_rad.variance();
    let (result_value, result_variance) = op(v, var_x);
    Ok(Value::Numeric(Quantity::with_number(
        SnaqNumber::new(result_value, result_variance),
        Unit::scalar(),
    )))
}

fn exactly_one(qs: &[Quantity], name: &str) -> Result<Quantity, RunError> {
    match qs {
        [q] => Ok(q.clone()),
        _ => Err(RunError::new(RunErrorKind::UnknownFunction(format!(
            "{name}: expected 1 argument, got {}",
            qs.len()
        )))),
    }
}

fn exactly_two(qs: &[Quantity], name: &str) -> Result<(Quantity, Quantity), RunError> {
    match qs {
        [a, b] => Ok((a.clone(), b.clone())),
        _ => Err(RunError::new(RunErrorKind::UnknownFunction(format!(
            "{name}: expected 2 arguments, got {}",
            qs.len()
        )))),
    }
}

/// Require the quantity to have Angle dimension (rad or degree); convert to radians and return.
fn require_angle(
    q: Quantity,
    registry: &UnitRegistry,
    _name: &str,
) -> Result<Quantity, RunError> {
    let rad = Unit::from_base_unit("rad");
    if !registry.same_dimension(q.unit(), &rad).unwrap_or(false) {
        return Err(RunError::new(RunErrorKind::ExpectedAngle {
            actual: q.unit().clone(),
        }));
    }
    q.convert_to(registry, &rad).map_err(|_| RunError::new(RunErrorKind::ExpectedAngle {
        actual: q.unit().clone(),
    }))
}

/// Require the quantity to be dimensionless (scalar); return value and variance.
fn require_dimensionless(q: &Quantity, registry: &UnitRegistry, name: &str) -> Result<(f64, f64), RunError> {
    let scalar = Unit::scalar();
    if !registry.same_dimension(q.unit(), &scalar).unwrap_or(false) {
        return Err(RunError::new(RunErrorKind::InvalidArgument(format!(
            "{name}: argument must be dimensionless (got unit with dimension)"
        ))));
    }
    Ok((q.value(), q.variance()))
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
        return Err(RunError::new(RunErrorKind::DimensionMismatch {
            left: a.unit().clone(),
            right: b.unit().clone(),
        }));
    }
    let result_unit = Quantity::smaller_unit(registry, a.unit(), b.unit())
        .cloned()
        .unwrap_or_else(|| a.unit().clone());
    let a_val = a.convert_to(registry, &result_unit).map_err(|e| match e {
        crate::quantity::QuantityError::DimensionMismatch { left, right } => {
            RunError::new(RunErrorKind::DimensionMismatch { left, right })
        }
        _ => RunError::new(RunErrorKind::DivisionByZero),
    })?.value();
    let b_val = b.convert_to(registry, &result_unit).map_err(|e| match e {
        crate::quantity::QuantityError::DimensionMismatch { left, right } => {
            RunError::new(RunErrorKind::DimensionMismatch { left, right })
        }
        _ => RunError::new(RunErrorKind::DivisionByZero),
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

/// Try to evaluate a built-in when the call is represented as symbolic args (e.g. sin(pi * rad) -> 0).
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
            Unit::from_base_unit("rad"),
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
            Unit::from_base_unit("rad"),
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
            Unit::from_base_unit("rad"),
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
            Unit::from_base_unit("rad"),
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
