//! snaq-lite: reactive arithmetic language (Salsa-based).

pub mod cas;
pub mod dimension;
pub mod error;
pub mod fuzzy;
pub mod functions;
pub mod ir;
pub mod lexer;
pub mod parser;
pub mod prefix;
pub mod quantity;
pub mod queries;
pub mod resolve;
pub mod scope;
pub mod symbol_registry;
pub mod symbolic;
pub mod unit;
pub mod stat_compare;
pub mod user_function;
pub mod unit_registry;
pub mod vector;
pub mod vector_registry;

pub use error::{ParseError, RunError};
pub use quantity::{Quantity, QuantityError, SnaqNumber};
pub use unit::Unit;
pub use ir::{ExprDef, Expression, NumLiteral, ProgramDef};
pub use scope::{empty_scope, Env, Scope, StoredValue};
pub use parser::parse;
pub use queries::{program, set_eval_registry, value, vector_into_stream};
pub use symbol_registry::SymbolRegistry;
pub use fuzzy::FuzzyBool;
pub use symbolic::{SymbolicQuantity, SymbolicExpr, Value};
pub use vector::{LazyVector, VectorOrientation, VectorValue};
pub use unit_registry::{default_si_registry, UnitRegistry};

/// Parse and evaluate the expression, returning a Value (symbolic by default, e.g. "6 + π").
///
/// Input can be multiple expressions (newline- or `;`-separated) and blocks `{ ... }`; the result
/// is the last expression's value, or `Value::Undefined` if there are no expressions (e.g. empty
/// input or empty block).
///
/// Supports float literals, quantity literals (e.g. `100 m`), symbols (e.g. `pi`, `π`, `e`),
/// implicit multiplication, division as `/` or `per`, unit conversion with `as` (e.g. `10 km as m`),
/// vector literals `[ expr, ... ]`, and postfix transpose `'` on vectors (e.g. `[1,2,3]'`).
/// Numeric literals get implicit uncertainty from decimal places (e.g. `10.5` has variance 0.0025);
/// use the tilde operator for explicit error: `value ~ error` (e.g. `10 ~ 2` gives mean 10, variance 4).
/// Uses the default unit registry.
pub fn run(input: &str) -> Result<Value, RunError> {
    run_with_registry(input, &default_si_registry())
}

/// Like [run], but with a custom unit registry.
pub fn run_with_registry(input: &str, registry: &UnitRegistry) -> Result<Value, RunError> {
    let root_def = parse(input).map_err(RunError::from)?;
    let root_def = resolve::resolve(root_def, registry)?;
    let root_def = cas::simplify_symbolic(root_def, registry)?;
    set_eval_registry(registry.clone());
    let db = salsa::DatabaseImpl::new();
    let program_def = ProgramDef::new(&db, root_def);
    let root = program(&db, program_def);
    value(&db, empty_scope(&db), root)
}

/// Recursively format a value for display. Vectors are shown as `[e1, e2, ...]` with nested
/// vectors fully expanded. Sparse (undefined) elements are shown as `?`.
fn format_value_for_display(db: &dyn salsa::Database, value: &Value) -> Result<String, RunError> {
    match value {
        Value::Numeric(q) => Ok(format!("{q}")),
        Value::Symbolic(sq) => Ok(format!("{sq}")),
        Value::FuzzyBool(fb) => Ok(format!("{fb}")),
        Value::Undefined => Ok("undefined".to_string()),
        Value::Function(_) => Ok("<function>".to_string()),
        Value::Vector(v) => {
            let stream = vector_into_stream(db, v.inner.clone());
            let results: Vec<_> = futures::executor::block_on(async move {
                use futures::stream::StreamExt;
                stream.collect().await
            });
            let mut parts = Vec::with_capacity(results.len());
            for r in results {
                let opt = r?;
                // Sparse (undefined) elements display as "?"
                let s = match opt {
                    None => "?".to_string(),
                    Some(v) => format_value_for_display(db, &v)?,
                };
                parts.push(s);
            }
            Ok(format!("[{}]", parts.join(", ")))
        }
    }
}

/// Format the result of evaluating the expression for display. Vectors are shown as `[e1, e2, ...]`.
/// Uses the default unit registry.
pub fn run_format(input: &str) -> Result<String, RunError> {
    run_with_registry_format(input, &default_si_registry())
}

/// Like [run_format], but with a custom unit registry. Nested vectors are fully expanded
/// in the output (e.g. `[[1, 2], [3, 4]]`).
pub fn run_with_registry_format(input: &str, registry: &UnitRegistry) -> Result<String, RunError> {
    let root_def = parse(input).map_err(RunError::from)?;
    let root_def = resolve::resolve(root_def, registry)?;
    let root_def = cas::simplify_symbolic(root_def, registry)?;
    set_eval_registry(registry.clone());
    let db = salsa::DatabaseImpl::new();
    let program_def = ProgramDef::new(&db, root_def);
    let root = program(&db, program_def);
    let val = value(&db, empty_scope(&db), root)?;
    format_value_for_display(&db, &val)
}

/// Evaluate and substitute all symbols with their numeric values; returns a single Quantity.
/// Errors if any symbol has no value in the default symbol registry, or if the result is undefined
/// (e.g. empty input or empty block) with [RunError::UndefinedResult].
pub fn run_numeric(input: &str) -> Result<Quantity, RunError> {
    run_numeric_with_registry(input, &default_si_registry(), &SymbolRegistry::default_registry())
}

/// Like [run_numeric], but with custom unit and symbol registries.
pub fn run_numeric_with_registry(
    input: &str,
    unit_registry: &UnitRegistry,
    symbol_registry: &SymbolRegistry,
) -> Result<Quantity, RunError> {
    let root_def = parse(input).map_err(RunError::from)?;
    let root_def = resolve::resolve(root_def, unit_registry)?;
    let root_def = cas::simplify_numeric(root_def, unit_registry, symbol_registry)?;
    set_eval_registry(unit_registry.clone());
    let db = salsa::DatabaseImpl::new();
    let program_def = ProgramDef::new(&db, root_def);
    let root = program(&db, program_def);
    let v = value(&db, empty_scope(&db), root)?;
    v.to_quantity(symbol_registry)
}

/// Evaluate in numeric mode and return the scalar value only if dimensionless.
/// Errors with [RunError::UndefinedResult] when the result is undefined (e.g. empty input or empty block).
pub fn run_scalar(input: &str) -> Result<f64, RunError> {
    let q = run_numeric(input)?;
    q.as_scalar().map_err(|e| match e {
        QuantityError::IncompatibleUnits(..) => {
            RunError::DimensionMismatch {
                left: q.unit().clone(),
                right: Unit::scalar(),
            }
        }
        _ => RunError::DivisionByZero,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{CallArg, ExprDef, NumLiteral};

    fn lit_scalar(n: f64) -> ExprDef {
        ExprDef::LitScalar(NumLiteral::from_f64(n))
    }

    /// Top-level parse returns a Block; single expression is Block([expr]).
    fn block_one(expr: ExprDef) -> ExprDef {
        ExprDef::Block(vec![expr])
    }

    #[test]
    fn parse_lit() {
        // Cases where parser raw matches from_f64; top level is Block([expr])
        assert_eq!(parse("1").unwrap(), block_one(lit_scalar(1.0)));
        assert_eq!(parse("42").unwrap(), block_one(lit_scalar(42.0)));
        assert_eq!(parse("0").unwrap(), block_one(lit_scalar(0.0)));
        assert_eq!(parse("1.5").unwrap(), block_one(lit_scalar(1.5)));
        // Parser preserves source form (".5", "2e1") so compare value only
        match parse(".5").unwrap() {
            ExprDef::Block(ref v) if v.len() == 1 => match &v[0] {
                ExprDef::LitScalar(n) => assert_eq!(n.value_f64(), 0.5),
                _ => panic!("expected LitScalar"),
            },
            _ => panic!("expected Block([LitScalar])"),
        }
        match parse("2e1").unwrap() {
            ExprDef::Block(ref v) if v.len() == 1 => match &v[0] {
                ExprDef::LitScalar(n) => assert_eq!(n.value_f64(), 20.0),
                _ => panic!("expected LitScalar"),
            },
            _ => panic!("expected Block([LitScalar])"),
        }
        match parse("9223372036854775807").unwrap() {
            ExprDef::Block(ref v) if v.len() == 1 => match &v[0] {
                ExprDef::LitScalar(n) => assert_eq!(n.value_f64(), 9223372036854775807.0),
                _ => panic!("expected LitScalar"),
            },
            _ => panic!("expected Block([LitScalar])"),
        }
    }

    #[test]
    fn parse_add() {
        assert_eq!(
            parse("1 + 2").unwrap(),
            block_one(ExprDef::Add(Box::new(lit_scalar(1.0)), Box::new(lit_scalar(2.0))))
        );
    }

    #[test]
    fn parse_sub() {
        assert_eq!(
            parse("1 - 2").unwrap(),
            block_one(ExprDef::Sub(Box::new(lit_scalar(1.0)), Box::new(lit_scalar(2.0))))
        );
    }

    #[test]
    fn parse_unary_minus() {
        assert_eq!(
            parse("-1").unwrap(),
            block_one(ExprDef::Neg(Box::new(lit_scalar(1.0))))
        );
        assert_eq!(
            parse("-(2 * 3)").unwrap(),
            block_one(ExprDef::Neg(Box::new(ExprDef::Mul(
                Box::new(lit_scalar(2.0)),
                Box::new(lit_scalar(3.0))
            ))))
        );
    }

    #[test]
    fn parse_mul() {
        assert_eq!(
            parse("2 * 3").unwrap(),
            block_one(ExprDef::Mul(Box::new(lit_scalar(2.0)), Box::new(lit_scalar(3.0))))
        );
    }

    #[test]
    fn parse_implicit_mul() {
        assert_eq!(
            parse("10 20").unwrap(),
            block_one(ExprDef::Mul(Box::new(lit_scalar(10.0)), Box::new(lit_scalar(20.0))))
        );
    }

    #[test]
    fn parse_div() {
        assert_eq!(
            parse("6 / 2").unwrap(),
            block_one(ExprDef::Div(Box::new(lit_scalar(6.0)), Box::new(lit_scalar(2.0))))
        );
    }

    #[test]
    fn parse_per_same_as_div() {
        assert_eq!(
            parse("6 per 2").unwrap(),
            block_one(ExprDef::Div(Box::new(lit_scalar(6.0)), Box::new(lit_scalar(2.0))))
        );
    }

    #[test]
    fn parse_ident_containing_per_still_ident() {
        // "per" is reserved as operator; identifiers like "percent" are still parsed as Ident
        assert_eq!(
            parse("1 percent").unwrap(),
            block_one(ExprDef::Mul(
                Box::new(ExprDef::LitScalar(NumLiteral::from_f64(1.0))),
                Box::new(ExprDef::LitUnit("percent".to_string()))
            ))
        );
    }

    #[test]
    fn parse_with_parens() {
        assert_eq!(
            parse("(1 + 2) - 1").unwrap(),
            block_one(ExprDef::Sub(
                Box::new(ExprDef::Add(Box::new(lit_scalar(1.0)), Box::new(lit_scalar(2.0)))),
                Box::new(lit_scalar(1.0))
            ))
        );
    }

    #[test]
    fn parse_precedence_mul_tighter_than_add() {
        assert_eq!(
            parse("1 + 2 * 3").unwrap(),
            block_one(ExprDef::Add(
                Box::new(lit_scalar(1.0)),
                Box::new(ExprDef::Mul(Box::new(lit_scalar(2.0)), Box::new(lit_scalar(3.0))))
            ))
        );
    }

    #[test]
    fn parse_precedence_div_tighter_than_sub() {
        assert_eq!(
            parse("6 - 4 / 2").unwrap(),
            block_one(ExprDef::Sub(
                Box::new(lit_scalar(6.0)),
                Box::new(ExprDef::Div(Box::new(lit_scalar(4.0)), Box::new(lit_scalar(2.0))))
            ))
        );
    }

    #[test]
    fn parse_precedence_parens_override() {
        assert_eq!(
            parse("(1 + 2) * 3").unwrap(),
            block_one(ExprDef::Mul(
                Box::new(ExprDef::Add(Box::new(lit_scalar(1.0)), Box::new(lit_scalar(2.0)))),
                Box::new(lit_scalar(3.0))
            ))
        );
    }

    #[test]
    fn parse_quantity_literal() {
        // "100 m" and "10 m" parse as implicit mul (number * unit) and resolve to same quantity
        assert_eq!(
            parse("100 m").unwrap(),
            block_one(ExprDef::Mul(
                Box::new(ExprDef::LitScalar(NumLiteral::from_f64(100.0))),
                Box::new(ExprDef::LitUnit("m".to_string()))
            ))
        );
        assert_eq!(
            parse("10 m").unwrap(),
            block_one(ExprDef::Mul(
                Box::new(ExprDef::LitScalar(NumLiteral::from_f64(10.0))),
                Box::new(ExprDef::LitUnit("m".to_string()))
            ))
        );
        // "1.5 * km" parses as Mul(LitScalar(1.5), LitUnit("km")) and resolves to 1.5 km
        assert_eq!(
            parse("1.5 * km").unwrap(),
            block_one(ExprDef::Mul(
                Box::new(ExprDef::LitScalar(NumLiteral::from_f64(1.5))),
                Box::new(ExprDef::LitUnit("km".to_string()))
            ))
        );
        assert_eq!(parse("hour").unwrap(), block_one(ExprDef::LitUnit("hour".to_string())));
    }

    #[test]
    fn parse_2_pi_rad_implicit_mul() {
        // "2 pi rad" parses as implicit mul chain (2 * pi * rad); pi → symbol, rad → unit
        let parsed = parse("2 pi rad").unwrap();
        let expected = ExprDef::Mul(
            Box::new(ExprDef::Mul(
                Box::new(ExprDef::LitScalar(NumLiteral::from_f64(2.0))),
                Box::new(ExprDef::LitUnit("pi".to_string())),
            )),
            Box::new(ExprDef::LitUnit("rad".to_string())),
        );
        assert_eq!(parsed, block_one(expected));
        let q = run_numeric("2 pi rad").unwrap();
        assert!((q.value() - 2.0 * std::f64::consts::PI).abs() < 1e-10);
        assert_eq!(q.unit().iter().next().map(|f| f.unit_name.as_str()), Some("rad"));
    }

    #[test]
    fn eval_lit() {
        assert_eq!(run_scalar("1").unwrap(), 1.0);
        assert_eq!(run_scalar("42").unwrap(), 42.0);
        assert_eq!(run_scalar("1.5").unwrap(), 1.5);
    }

    #[test]
    fn num_literal_implicit_variance_from_decimal_places() {
        use crate::ir::NumLiteral;
        // No decimal point → abs_err 0.5, variance 0.25
        let n = NumLiteral { raw: "10".to_string(), value: ordered_float::OrderedFloat::from(10.0) };
        assert_eq!(n.implicit_absolute_error(), 0.5);
        assert_eq!(n.implicit_variance(), 0.25);
        // One decimal place → 5e-2, variance 0.0025
        let n = NumLiteral { raw: "10.5".to_string(), value: ordered_float::OrderedFloat::from(10.5) };
        assert!((n.implicit_absolute_error() - 0.05).abs() < 1e-15);
        assert!((n.implicit_variance() - 0.0025).abs() < 1e-15);
        // Two decimal places → 5e-3, variance 0.000025
        let n = NumLiteral { raw: "10.50".to_string(), value: ordered_float::OrderedFloat::from(10.5) };
        assert!((n.implicit_absolute_error() - 0.005).abs() < 1e-15);
        assert!((n.implicit_variance() - 0.000025).abs() < 1e-15);
        // Scientific notation: count decimals in mantissa only
        let n = NumLiteral { raw: "1.23e4".to_string(), value: ordered_float::OrderedFloat::from(12300.0) };
        assert_eq!(n.decimal_places_after(), Some(2));
        assert!((n.implicit_absolute_error() - 0.005).abs() < 1e-15);
    }

    #[test]
    fn run_literal_implicit_variance_preserved() {
        // "10" (no decimal) → variance 0.25
        let q = run_numeric("10").unwrap();
        assert!((q.value() - 10.0).abs() < 1e-10);
        assert!((q.variance() - 0.25).abs() < 1e-10);
        // "10.5" (1 decimal) → variance 0.0025
        let q = run_numeric("10.5").unwrap();
        assert!((q.variance() - 0.0025).abs() < 1e-10);
        // "10.50" (2 decimals) → variance 0.000025
        let q = run_numeric("10.50").unwrap();
        assert!((q.variance() - 0.000025).abs() < 1e-10);
    }

    #[test]
    fn parse_tilde_precedence() {
        // "5 + 10 ~ 2" => 5 + (10 ~ 2), not (5 + 10) ~ 2
        let def = parse("5 + 10 ~ 2").unwrap();
        let inner = match &def {
            ExprDef::Block(v) if v.len() == 1 => &v[0],
            _ => panic!("expected Block([Add(_, WithPrecision)]), got {:?}", def),
        };
        match inner {
            ExprDef::Add(l, r) => {
                assert!(matches!(l.as_ref(), ExprDef::LitScalar(_) | ExprDef::Lit(_)));
                assert!(matches!(r.as_ref(), ExprDef::WithPrecision(_, _)));
            }
            _ => panic!("expected Add(_, WithPrecision), got {:?}", inner),
        }
    }

    #[test]
    fn run_tilde_explicit_variance() {
        // 10 ~ 2 => mean 10, variance 4 (error 2)
        let q = run_numeric("10 ~ 2").unwrap();
        assert!((q.value() - 10.0).abs() < 1e-10);
        assert!((q.variance() - 4.0).abs() < 1e-10);
        // 5 + 10 ~ 2 => 15 with variance 0.25 + 4 = 4.25 (Add sums variances)
        let q = run_numeric("5 + 10 ~ 2").unwrap();
        assert!((q.value() - 15.0).abs() < 1e-10);
        assert!((q.variance() - 4.25).abs() < 1e-10);
    }

    #[test]
    fn run_tilde_negative_error_returns_err() {
        let e = run_numeric("10 ~ -1").unwrap_err();
        assert!(matches!(e, RunError::PrecisionMustBePositive));
    }

    #[test]
    fn run_tilde_zero_error_returns_err() {
        let e = run_numeric("10 ~ 0").unwrap_err();
        assert!(matches!(e, RunError::PrecisionMustBePositive));
    }

    #[test]
    fn run_tilde_rhs_variance_discarded() {
        // 10 ~ (2 ~ 0.5): RHS evaluates to value 2 (variance 0.25); we use only central value 2 => variance 4
        let q = run_numeric("10 ~ (2 ~ 0.5)").unwrap();
        assert!((q.value() - 10.0).abs() < 1e-10);
        assert!((q.variance() - 4.0).abs() < 1e-10);
    }

    #[test]
    fn run_tilde_requires_numeric_operands() {
        // Symbolic LHS: pi ~ 2 cannot be evaluated in numeric context; run() still evaluates and returns err
        let e = run_with_registry("pi ~ 2", &default_si_registry()).unwrap_err();
        assert!(matches!(e, RunError::TildeRequiresNumeric));
    }

    #[test]
    fn run_literal_decimal_places_affect_variance() {
        // "10.5" (1 decimal) vs "10.50" (2 decimals) => different variances
        let q5 = run_numeric("10.5").unwrap();
        let q50 = run_numeric("10.50").unwrap();
        assert_eq!(q5.value(), q50.value());
        assert!((q5.variance() - 0.0025).abs() < 1e-12);
        assert!((q50.variance() - 0.000025).abs() < 1e-12);
        assert!(q50.variance() < q5.variance());
    }

    #[test]
    fn eval_unary_minus() {
        assert_eq!(run_scalar("-1").unwrap(), -1.0);
        assert_eq!(run_scalar("-0").unwrap(), 0.0);
        assert_eq!(run_scalar("-(2 * 3)").unwrap(), -6.0);
    }

    #[test]
    fn eval_add() {
        assert_eq!(run_scalar("1 + 2").unwrap(), 3.0);
    }

    #[test]
    fn eval_sub() {
        assert_eq!(run_scalar("1 - 2").unwrap(), -1.0);
    }

    #[test]
    fn eval_mul() {
        assert_eq!(run_scalar("2 * 3").unwrap(), 6.0);
    }

    #[test]
    fn eval_implicit_mul() {
        assert_eq!(run_scalar("10 20").unwrap(), 200.0);
        assert_eq!(run_scalar("10 20 30").unwrap(), 6000.0);
        assert_eq!(run_scalar("2 (3 + 4)").unwrap(), 14.0);
        assert_eq!(run_scalar("10 20 + 5").unwrap(), 205.0); // (10*20)+5, implicit mul binds tighter than +
    }

    #[test]
    fn eval_div() {
        assert_eq!(run_scalar("6 / 2").unwrap(), 3.0);
        assert_eq!(run_scalar("6 per 2").unwrap(), 3.0);
    }

    #[test]
    fn eval_parens() {
        assert_eq!(run_scalar("(1 + 2) - 1").unwrap(), 2.0);
    }

    #[test]
    fn eval_precedence_mul_tighter_than_add() {
        assert_eq!(run_scalar("1 + 2 * 3").unwrap(), 7.0);
    }

    #[test]
    fn eval_precedence_div_tighter_than_sub() {
        assert_eq!(run_scalar("6 - 4 / 2").unwrap(), 4.0);
    }

    #[test]
    fn eval_precedence_mul_div_left_to_right() {
        assert_eq!(run_scalar("8 / 4 / 2").unwrap(), 1.0);
        assert_eq!(run_scalar("2 * 3 * 4").unwrap(), 24.0);
    }

    #[test]
    fn eval_precedence_parens_override() {
        assert_eq!(run_scalar("(1 + 2) * 3").unwrap(), 9.0);
        assert_eq!(run_scalar("6 / (1 + 1)").unwrap(), 3.0);
    }

    #[test]
    fn eval_quantity_with_units() {
        let q = run_numeric("1.5 km + 500 m").unwrap();
        assert!((q.value() - 2000.0).abs() < 1e-10);
        assert_eq!(q.unit().iter().next().unwrap().unit_name, "m");
    }

    #[test]
    fn eval_implicit_mul_with_units() {
        let q = run_numeric("10 m 2").unwrap();
        assert!((q.value() - 20.0).abs() < 1e-10);
        assert_eq!(q.unit().iter().next().unwrap().unit_name, "m");
    }

    #[test]
    fn eval_compound_unit() {
        let q = run_numeric("10 m / 2 s").unwrap();
        assert!((q.value() - 5.0).abs() < 1e-10);
        let factors: Vec<_> = q.unit().iter().collect();
        assert_eq!(factors.len(), 2);
    }

    #[test]
    fn parse_as_unit_conversion() {
        // "10 km as m" parses as Block([As(...)])
        let parsed = parse("10 km as m").unwrap();
        assert!(matches!(parsed, ExprDef::Block(ref v) if v.len() == 1 && matches!(&v[0], ExprDef::As(_, _))));
        let q = run_numeric("10 km as m").unwrap();
        assert!((q.value() - 10_000.0).abs() < 1e-10);
        assert_eq!(q.unit().iter().next().map(|f| f.unit_name.as_str()), Some("m"));
    }

    #[test]
    fn run_as_simple_and_compound_unit() {
        let q = run_numeric("10 km as m").unwrap();
        assert!((q.value() - 10_000.0).abs() < 1e-10);
        // 10 km/hour as m/s
        let q3 = run_numeric("10 km per hour as m / s").unwrap();
        assert!((q3.value() - 10.0 / 3.6).abs() < 1e-10);
        let factors: Vec<_> = q3.unit().iter().collect();
        assert_eq!(factors.len(), 2); // m and s in denominator
    }

    #[test]
    fn run_numeric_time_units_convert_and_add() {
        let q = run_numeric("10 hours as day").unwrap();
        assert!((q.value() - 10.0 / 24.0).abs() < 1e-10, "10 hours as day");
        assert_eq!(q.unit().iter().next().unwrap().unit_name, "day");
        let q2 = run_numeric("1 week + 2 days").unwrap();
        assert!((q2.value() - 9.0).abs() < 1e-10, "1 week + 2 days = 9 days");
        assert_eq!(q2.unit().iter().next().unwrap().unit_name, "day");
    }

    #[test]
    fn run_as_dimension_mismatch_errors() {
        let e = run_numeric("10 km as s").unwrap_err();
        assert!(matches!(e, RunError::DimensionMismatch { .. }));
    }

    #[test]
    fn run_as_precedence() {
        // "10 km + 5 m as m" => (10 km + 5 m) as m
        let q = run_numeric("10 km + 5 m as m").unwrap();
        assert!((q.value() - 10_005.0).abs() < 1e-10);
    }

    #[test]
    fn parse_if_then_else() {
        let parsed = parse("if 1 then 2 else 3").unwrap();
        assert!(matches!(parsed, ExprDef::Block(ref v) if v.len() == 1 && matches!(&v[0], ExprDef::If(_, _, _))));
        let parsed = parse("if 1 < 2 then 10 else 20").unwrap();
        assert!(matches!(parsed, ExprDef::Block(ref v) if v.len() == 1 && matches!(&v[0], ExprDef::If(_, _, _))));
        if let ExprDef::Block(ref v) = parsed {
            if let ExprDef::If(cond, then_b, else_b) = &v[0] {
                assert!(matches!(cond.as_ref(), ExprDef::Lt(_, _)));
                assert!(matches!(then_b.as_ref(), ExprDef::LitScalar(_) | ExprDef::Lit(_)));
                assert!(matches!(else_b.as_ref(), ExprDef::LitScalar(_) | ExprDef::Lit(_)));
            }
        }
    }

    #[test]
    fn run_if_crisp_then() {
        // Condition 1.0 < 2.0 constant-folds to True (decimal literals => low variance => crisp).
        let v = run_with_registry("if 1.0 < 2.0 then 10 else 20", &default_si_registry()).unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric") };
        assert!((q.value() - 10.0).abs() < 1e-10);
    }

    #[test]
    fn run_if_crisp_else() {
        // Condition 1.0 > 2.0 constant-folds to False (decimal literals => low variance => crisp).
        let v = run_with_registry("if 1.0 > 2.0 then 10 else 20", &default_si_registry()).unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric") };
        assert!((q.value() - 20.0).abs() < 1e-10);
    }

    #[test]
    fn run_if_superposition_numeric() {
        // 1 > 1 gives Uncertain(0.5); both branches numeric => blended mean 0.5*10 + 0.5*20 = 15.
        let v = run_with_registry("if 1 > 1 then 10 else 20", &default_si_registry()).unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric") };
        assert!((q.value() - 15.0).abs() < 1e-10, "blended mean should be 15");
    }

    #[test]
    fn run_if_superposition_symbolic() {
        // Uncertain condition with symbolic branches yields symbolic weighted sum (simplified).
        let v = run_with_registry("if 1 > 1 then pi else 2 * pi", &default_si_registry()).unwrap();
        let Value::Symbolic(sq) = v else { panic!("expected symbolic") };
        let s = format!("{}", sq);
        assert!(s.contains("π") || s.contains("pi"), "result should contain pi symbol");
    }

    #[test]
    fn run_if_branch_type_mismatch() {
        // Uncertain condition forces both branches evaluated; one numeric, one vector => IfBranchTypeMismatch.
        let e = run_with_registry("if 1 > 1 then 10 else [1, 2]", &default_si_registry()).unwrap_err();
        assert!(matches!(e, RunError::IfBranchTypeMismatch));
    }

    #[test]
    fn run_if_expected_condition() {
        // Condition must be boolean; a number is not valid.
        let e = run_with_registry("if 1 then 10 else 20", &default_si_registry()).unwrap_err();
        assert!(matches!(e, RunError::ExpectedCondition));
    }

    #[test]
    fn run_if_superposition_numeric_different_units() {
        // Same dimension, different units: blend after converting to common unit.
        let v = run_with_registry("if 1 > 1 then 10 m else 20 m", &default_si_registry()).unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric") };
        assert!((q.value() - 15.0).abs() < 1e-10, "blended mean 15 m");
        assert!(!q.unit().is_scalar(), "result should have length unit (m)");
        // 1 km and 1000 m: result in common unit (m), 0.5*1000 + 0.5*1000 = 1000 m
        let v2 = run_with_registry("if 1 > 1 then 1 km else 1000 m", &default_si_registry()).unwrap();
        let Value::Numeric(q2) = v2 else { panic!("expected numeric") };
        assert!((q2.value() - 1000.0).abs() < 1e-6, "1 km and 1000 m blend to 1000 m");
    }

    #[test]
    fn run_if_superposition_dimension_mismatch() {
        // Uncertain condition but branches have different dimensions => DimensionMismatch.
        let e = run_with_registry("if 1 > 1 then 10 m else 10 s", &default_si_registry()).unwrap_err();
        assert!(matches!(e, RunError::DimensionMismatch { .. }));
    }

    #[test]
    fn parse_comparison() {
        let parsed = parse("1 == 2").unwrap();
        assert!(matches!(parsed, ExprDef::Block(ref v) if v.len() == 1 && matches!(&v[0], ExprDef::Eq(_, _))));
        let parsed = parse("100 m < 1 kilometer").unwrap();
        assert!(matches!(parsed, ExprDef::Block(ref v) if v.len() == 1 && matches!(&v[0], ExprDef::Lt(_, _))));
        let parsed = parse("2 <= 3").unwrap();
        assert!(matches!(parsed, ExprDef::Block(ref v) if v.len() == 1 && matches!(&v[0], ExprDef::Le(_, _))));
        let parsed = parse("3 > 2").unwrap();
        assert!(matches!(parsed, ExprDef::Block(ref v) if v.len() == 1 && matches!(&v[0], ExprDef::Gt(_, _))));
        let parsed = parse("4 >= 4").unwrap();
        assert!(matches!(parsed, ExprDef::Block(ref v) if v.len() == 1 && matches!(&v[0], ExprDef::Ge(_, _))));
        let parsed = parse("1 != 1").unwrap();
        assert!(matches!(parsed, ExprDef::Block(ref v) if v.len() == 1 && matches!(&v[0], ExprDef::Ne(_, _))));
    }

    #[test]
    fn run_comparison_scalar_numeric() {
        // Result is Value::FuzzyBool (crisp when literals have low variance, e.g. decimals)
        let v = run_with_registry("1.0 == 2.0", &default_si_registry()).unwrap();
        assert!(matches!(v, Value::FuzzyBool(FuzzyBool::False)));
        let v = run_with_registry("1.0 == 1.0", &default_si_registry()).unwrap();
        assert!(matches!(v, Value::FuzzyBool(FuzzyBool::True)));
        let v = run_with_registry("100 m < 1 kilometer", &default_si_registry()).unwrap();
        assert!(matches!(v, Value::FuzzyBool(FuzzyBool::True))); // 100 < 1000
        let v = run_with_registry("2.0 <= 3.0", &default_si_registry()).unwrap();
        assert!(matches!(v, Value::FuzzyBool(FuzzyBool::True)));
        let v = run_with_registry("3.0 > 2.0", &default_si_registry()).unwrap();
        assert!(matches!(v, Value::FuzzyBool(FuzzyBool::True)));
        let v = run_with_registry("4.0 >= 4.0", &default_si_registry()).unwrap();
        assert!(matches!(v, Value::FuzzyBool(FuzzyBool::True)));
        let v = run_with_registry("1.0 != 2.0", &default_si_registry()).unwrap();
        assert!(matches!(v, Value::FuzzyBool(FuzzyBool::True)));
    }

    #[test]
    fn run_comparison_precedence() {
        // 1 + 2 < 3 + 4 => (1+2) < (3+4) => 3 < 7 => true
        let v = run_with_registry("1 + 2 < 3 + 4", &default_si_registry()).unwrap();
        assert!(matches!(v, Value::FuzzyBool(FuzzyBool::True)));
    }

    #[test]
    fn run_comparison_dimension_mismatch() {
        let e = run_with_registry("1 m < 1 s", &default_si_registry()).unwrap_err();
        assert!(matches!(e, RunError::DimensionMismatch { .. }));
    }

    #[test]
    fn run_comparison_vector_scalar() {
        use crate::queries::{program, set_eval_registry, value, vector_into_stream};
        use crate::resolve;
        use crate::cas;
        use futures::stream::StreamExt;
        use salsa::DatabaseImpl;

        let registry = default_si_registry();
        let root_def = parse("[1.0 m, 2.0 m] < 1.5 m").unwrap();
        let root_def = resolve::resolve(root_def, &registry).unwrap();
        let root_def = cas::simplify_symbolic(root_def, &registry).unwrap();
        set_eval_registry(registry.clone());
        let db = DatabaseImpl::new();
        let program_def = ProgramDef::new(&db, root_def);
        let root = program(&db, program_def);
        let v = value(&db, empty_scope(&db), root).unwrap();
        let Value::Vector(w) = v else { panic!("expected vector") };
        let stream = vector_into_stream(&db, w.inner.clone());
        let results: Vec<_> = futures::executor::block_on(async move {
            stream.collect().await
        });
        assert_eq!(results.len(), 2);
        let v0 = results[0].as_ref().unwrap().as_ref().unwrap();
        let v1 = results[1].as_ref().unwrap().as_ref().unwrap();
        // Use decimal literals so variance is small and comparisons are crisp
        assert!(matches!(v0, Value::FuzzyBool(FuzzyBool::True)), "1.0 m < 1.5 m => true");
        assert!(matches!(v1, Value::FuzzyBool(FuzzyBool::False)), "2.0 m < 1.5 m => false");
    }

    #[test]
    fn run_comparison_vector_vector_element_wise() {
        use crate::queries::{program, set_eval_registry, value, vector_into_stream};
        use crate::resolve;
        use crate::cas;
        use futures::stream::StreamExt;
        use salsa::DatabaseImpl;

        let registry = default_si_registry();
        let root_def = parse("[1, 2, 3] == [1, 0, 3]").unwrap();
        let root_def = resolve::resolve(root_def, &registry).unwrap();
        let root_def = cas::simplify_symbolic(root_def, &registry).unwrap();
        set_eval_registry(registry.clone());
        let db = DatabaseImpl::new();
        let program_def = ProgramDef::new(&db, root_def);
        let root = program(&db, program_def);
        let v = value(&db, empty_scope(&db), root).unwrap();
        let Value::Vector(w) = v else { panic!("expected vector") };
        let stream = vector_into_stream(&db, w.inner.clone());
        let results: Vec<_> = futures::executor::block_on(async move {
            stream.collect().await
        });
        assert_eq!(results.len(), 3);
        let v0 = results[0].as_ref().unwrap().as_ref().unwrap();
        let v1 = results[1].as_ref().unwrap().as_ref().unwrap();
        let v2 = results[2].as_ref().unwrap().as_ref().unwrap();
        assert!(matches!(v0, Value::FuzzyBool(FuzzyBool::True)));
        assert!(matches!(v1, Value::FuzzyBool(FuzzyBool::False)));
        assert!(matches!(v2, Value::FuzzyBool(FuzzyBool::True)));
    }

    #[test]
    fn run_comparison_cas_fold() {
        // 1 < 2 constant-folds to LitFuzzyBool(True); run_numeric returns BooleanResult
        let e = run_numeric("1 < 2").unwrap_err();
        assert!(matches!(e, RunError::BooleanResult));
    }

    #[test]
    fn run_comparison_format() {
        // Comparison results display as "true" or "false" (use decimal literals for crisp)
        assert_eq!(run_format("1.0 < 2.0").unwrap(), "true");
        assert_eq!(run_format("1.0 == 2.0").unwrap(), "false");
        assert_eq!(run_format("100 m < 1 kilometer").unwrap(), "true");
    }

    #[test]
    fn run_comparison_symbolic_display() {
        // Symbolic comparison displays as (expr) op (expr)
        let s = run_format("1 + pi < 3").unwrap();
        assert!(s.contains('<'), "symbolic comparison should contain <");
        assert!(s.contains('π') || s.contains("pi"), "should contain pi symbol");
    }

    #[test]
    fn run_comparison_row_column_reduce() {
        // row×column: compare(sum(left), sum(right)) → one Value::FuzzyBool
        // [1 m, 2 m]' < [2 m, 1 m] => sum 3 m < 3 m. With variance, can be False or Uncertain (not True).
        let v = run_with_registry("[1 m, 2 m]' < [2 m, 1 m]", &default_si_registry()).unwrap();
        match &v {
            Value::FuzzyBool(FuzzyBool::False) | Value::FuzzyBool(FuzzyBool::Uncertain(_)) => {}
            _ => panic!("3 m < 3 m should be False or Uncertain, got {:?}", v),
        }
        // [1.0, 2.0]' < [0.0, 4.0] => 3 < 4 => true (crisp: decimal literals => low variance)
        let v = run_with_registry("[1.0, 2.0]' < [0.0, 4.0]", &default_si_registry()).unwrap();
        assert!(matches!(v, Value::FuzzyBool(FuzzyBool::True)), "3 < 4 => true");
    }

    #[test]
    fn run_format_vector_of_booleans() {
        // Vector of comparison results displays as [true, false, ...] (decimal literals for crisp)
        assert_eq!(run_format("[1.0 < 2.0, 1.0 == 2.0]").unwrap(), "[true, false]");
        assert_eq!(run_format("[2.0 <= 3.0, 3.0 > 4.0]").unwrap(), "[true, false]");
    }

    #[test]
    fn run_format_fuzzy_bool_uncertain() {
        // FuzzyBool::Uncertain displays as "uncertain(prob)"
        use ordered_float::OrderedFloat;
        let v = Value::FuzzyBool(FuzzyBool::Uncertain(OrderedFloat::from(0.5)));
        let s = v.to_string();
        assert!(
            s.contains("uncertain"),
            "Uncertain should display as uncertain(...), got {}",
            s
        );
    }

    #[test]
    fn parse_implicit_mul_rhs_not_ident() {
        // Implicit mul RHS is only number or (expr). "2 3 m" has no op between 3 and m, so parse error.
        assert!(parse("2 3 m").is_err());
    }

    #[test]
    fn parse_pi_rad_implicit_mul() {
        // "pi rad" parses as implicit mul (no number); pi → symbol, rad → unit
        let parsed = parse("pi rad").unwrap();
        let expected = ExprDef::Mul(
            Box::new(ExprDef::LitUnit("pi".to_string())),
            Box::new(ExprDef::LitUnit("rad".to_string())),
        );
        assert_eq!(parsed, block_one(expected));
        let q = run_numeric("pi rad").unwrap();
        assert!((q.value() - std::f64::consts::PI).abs() < 1e-10);
        assert_eq!(q.unit().iter().next().map(|f| f.unit_name.as_str()), Some("rad"));
    }

    #[test]
    fn parse_unicode_pi_rad_implicit_mul() {
        // "π rad" (unicode) parses like "pi rad" via PiIdents
        let q = run_numeric("π rad").unwrap();
        assert!((q.value() - std::f64::consts::PI).abs() < 1e-10);
        assert_eq!(q.unit().iter().next().map(|f| f.unit_name.as_str()), Some("rad"));
        let q_sin = run_numeric("sin(π rad)").unwrap();
        assert!(q_sin.value().abs() < 1e-10, "sin(π rad) ≈ 0");
    }

    #[test]
    fn parse_empty_returns_empty_block() {
        // Empty input parses as Block([]); run returns Value::Undefined
        let parsed = parse("").unwrap();
        assert!(matches!(parsed, ExprDef::Block(ref v) if v.is_empty()));
        let parsed = parse("   ").unwrap();
        assert!(matches!(parsed, ExprDef::Block(ref v) if v.is_empty()));
    }

    #[test]
    fn parse_invalid_char_is_error() {
        assert!(parse("!").is_err());
        assert!(parse("1 + *").is_err());
    }

    #[test]
    fn parse_1_2_3_as_implicit_mul() {
        // With implicit multiplication, "1.2.3" parses as 1.2 * .3 (two Num tokens) = 0.36
        assert_eq!(run_scalar("1.2.3").unwrap(), 0.36);
    }

    #[test]
    fn run_parse_error_returns_err() {
        assert!(run("1 +").is_err());
    }

    #[test]
    fn run_empty_returns_undefined() {
        let v = run("").unwrap();
        assert!(matches!(v, Value::Undefined));
    }

    #[test]
    fn parse_binding() {
        let def = parse("x = 10").unwrap();
        let ExprDef::Block(items) = def else { panic!("expected block") };
        assert_eq!(items.len(), 1);
        let ExprDef::Binding(name, rhs) = &items[0] else { panic!("expected binding") };
        assert_eq!(name, "x");
        let ExprDef::LitScalar(_) = rhs.as_ref() else { panic!("expected lit in rhs") };
    }

    #[test]
    fn parse_chained_assignment() {
        let def = parse("A = B = 42").unwrap();
        let ExprDef::Block(items) = def else { panic!("expected block") };
        assert_eq!(items.len(), 1);
        let ExprDef::Binding(a, rhs) = &items[0] else { panic!("expected binding") };
        assert_eq!(a, "A");
        let ExprDef::Binding(b, inner) = rhs.as_ref() else { panic!("expected inner binding") };
        assert_eq!(b, "B");
        let ExprDef::LitScalar(_) = inner.as_ref() else { panic!("expected lit in innermost rhs") };
    }

    #[test]
    fn run_variable_shadows_unit_def() {
        // "DEF" would parse as unit (da+F = decafarad); with scope-first, variable DEF wins.
        let v = run("DEF=3;DEF + 2").unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric, got {:?}", v) };
        assert!((q.value() - 5.0).abs() < 1e-10, "DEF=3; DEF+2 => 5");
    }

    #[test]
    fn run_numeric_variable_shadowing_unit_uses_scope() {
        // substitute_symbols leaves names bound in the program as LitSymbol; value() resolves from scope.
        // So run_numeric("DEF=3; DEF+2") yields 5 (variable DEF takes precedence over unit decafarad).
        let q = run_numeric("DEF=3; DEF + 2").expect("run_numeric(DEF=3; DEF+2) should succeed");
        assert!((q.value() - 5.0).abs() < 1e-10, "DEF=3; DEF+2 => 5");
    }

    #[test]
    fn run_numeric_nested_block_shadowing() {
        // Bound names are collected from the whole tree; inner block binding shadows outer. value() resolves from scope.
        let q = run_numeric("m = 1; { m = 2; m }").expect("run_numeric(m=1; { m=2; m }) should succeed");
        assert!((q.value() - 2.0).abs() < 1e-10, "inner m shadows => 2");
    }

    #[test]
    fn run_numeric_unbound_unit_name_still_errors() {
        // Without a binding, DEF is substituted as unit (decafarad); 2 + 1 DEF => dimension mismatch.
        let e = run_numeric("DEF + 2");
        assert!(e.is_err(), "run_numeric(DEF+2) without binding should error: {:?}", e);
        let err = e.unwrap_err();
        assert!(
            matches!(err, RunError::DimensionMismatch { .. } | RunError::SymbolHasNoValue(_)),
            "expected DimensionMismatch or SymbolHasNoValue, got {:?}",
            err
        );
    }

    #[test]
    fn run_chained_assignment() {
        let v = run("x = y = 42").unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric, got {:?}", v) };
        assert!((q.value() - 42.0).abs() < 1e-10);
        let v = run("x = y = 42\nx + y").unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric, got {:?}", v) };
        assert!((q.value() - 84.0).abs() < 1e-10, "x and y both 42 => x + y = 84");
    }

    #[test]
    fn run_binding_simple() {
        // x = 10; x + 1 => 11
        let v = run("x = 10\nx + 1").unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric, got {:?}", v) };
        assert!((q.value() - 11.0).abs() < 1e-10);
    }

    #[test]
    fn run_binding_block() {
        // { a = 2; b = 3; a * b } => 6
        let v = run("{ a = 2; b = 3; a * b }").unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric, got {:?}", v) };
        assert!((q.value() - 6.0).abs() < 1e-10);
    }

    #[test]
    fn run_binding_shadowing() {
        // x = 1; { x = 2; x } => 2 (inner x shadows)
        let v = run("x = 1\n{ x = 2; x }").unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric, got {:?}", v) };
        assert!((q.value() - 2.0).abs() < 1e-10);
    }

    #[test]
    fn run_block_only_bindings_returns_last_rhs() {
        // Assignment is an expression: value is the RHS. Block of only bindings => last binding's value.
        let v = run("x = 1\ny = 2").unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric (last RHS), got {:?}", v) };
        assert!((q.value() - 2.0).abs() < 1e-10, "last binding y = 2 => 2");
    }

    #[test]
    fn run_binding_through_full_pipeline() {
        // Parse → resolve → simplify_symbolic → program → value: bindings preserved and evaluated
        let registry = default_si_registry();
        let root_def = parse("x = 10\nx + 1").unwrap();
        let root_def = resolve::resolve(root_def, &registry).unwrap();
        let root_def = cas::simplify_symbolic(root_def, &registry).unwrap();
        set_eval_registry(registry.clone());
        let db = salsa::DatabaseImpl::new();
        let program_def = ProgramDef::new(&db, root_def);
        let root = program(&db, program_def);
        let v = value(&db, empty_scope(&db), root).unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric, got {:?}", v) };
        assert!((q.value() - 11.0).abs() < 1e-10);
    }

    #[test]
    fn run_binding_symbolic_returns_binding_value_not_supported() {
        let err = run("x = 1 + pi").unwrap_err();
        assert!(
            matches!(err, RunError::BindingValueNotSupported(_)),
            "binding symbolic value should return BindingValueNotSupported, got {:?}",
            err
        );
    }

    #[test]
    fn run_binding_vector_succeeds() {
        let v = run("V = [1, 2, 3]").unwrap();
        assert!(
            matches!(v, Value::Vector(_)),
            "binding vector should succeed and yield vector, got {:?}",
            v
        );
        let v = run("V = [1, 2, 3]\nV").unwrap();
        assert!(
            matches!(v, Value::Vector(_)),
            "bound variable V should evaluate to vector, got {:?}",
            v
        );
    }

    #[test]
    fn run_multiple_expressions_newline_last_wins() {
        // Multiple expressions separated by newline; result is last expression
        let v = run("1 + 1\n2 + 2").unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric") };
        assert!((q.value() - 4.0).abs() < 1e-10);
        let v = run("1\n2\n3").unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric") };
        assert!((q.value() - 3.0).abs() < 1e-10);
    }

    #[test]
    fn run_multiple_expressions_semicolon_last_wins() {
        let v = run("1; 2; 3").unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric") };
        assert!((q.value() - 3.0).abs() < 1e-10);
        let v = run("1 + 1; 2 * 3").unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric") };
        assert!((q.value() - 6.0).abs() < 1e-10);
    }

    #[test]
    fn run_block_returns_last_expression() {
        let v = run("{ 1; 2 }").unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric") };
        assert!((q.value() - 2.0).abs() < 1e-10);
        let v = run("{ 10\n20 }").unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric") };
        assert!((q.value() - 20.0).abs() < 1e-10);
    }

    #[test]
    fn run_empty_block_returns_undefined() {
        let v = run("{}").unwrap();
        assert!(matches!(v, Value::Undefined));
    }

    #[test]
    fn run_numeric_and_run_scalar_empty_or_undefined_return_undefined_result() {
        let e = run_numeric("").unwrap_err();
        assert!(matches!(e, RunError::UndefinedResult));
        let e = run_scalar("").unwrap_err();
        assert!(matches!(e, RunError::UndefinedResult));
        let e = run_numeric("{}").unwrap_err();
        assert!(matches!(e, RunError::UndefinedResult));
        let e = run_scalar("{}").unwrap_err();
        assert!(matches!(e, RunError::UndefinedResult));
    }

    #[test]
    fn run_block_as_expression() {
        // Block is an expression; can be used in larger expressions
        let v = run("2 * { 3; 4 }").unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric") };
        assert!((q.value() - 8.0).abs() < 1e-10, "2 * 4 = 8");
    }

    #[test]
    fn run_nested_blocks() {
        let v = run("{ 1; { 2; 3 } }").unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric") };
        assert!((q.value() - 3.0).abs() < 1e-10);
    }

    #[test]
    fn run_blank_lines_allowed() {
        let v = run("1\n\n2\n\n3").unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric") };
        assert!((q.value() - 3.0).abs() < 1e-10);
    }

    #[test]
    fn run_unknown_identifier_treated_as_symbol() {
        // Identifiers that are not units are treated as symbols (e.g. "foo", "bar").
        let v = run("1 foo").unwrap();
        assert!(matches!(v, Value::Symbolic(_)));
        let v = run("bar").unwrap();
        assert!(matches!(v, Value::Symbolic(_)));
    }

    #[test]
    /// With CAS, division by zero in constant folding yields DivisionByZero (no ±∞).
    fn run_division_by_zero_nonzero_yields_infinity() {
        let e = run_numeric("1 / 0").unwrap_err();
        assert!(matches!(e, RunError::DivisionByZero));
        let e = run_numeric("0 - 1/0").unwrap_err();
        assert!(matches!(e, RunError::DivisionByZero));
        let e = run_numeric("3 m / 0 s").unwrap_err();
        assert!(matches!(e, RunError::DivisionByZero));
    }

    #[test]
    fn run_zero_over_zero_returns_err() {
        let e = run_numeric("0 / 0").unwrap_err();
        assert!(matches!(e, RunError::DivisionByZero));
    }

    #[test]
    fn run_numeric_symbolic_div_by_zero_returns_division_by_zero() {
        let e = run_numeric("(1 + pi) / 0").unwrap_err();
        assert!(matches!(e, RunError::DivisionByZero));
    }

    /// With CAS, expressions that would yield ±∞ (1/0) are caught as DivisionByZero in rewrite.
    #[test]
    fn run_arithmetic_with_infinity() {
        let e = run_numeric("1/0 + 1").unwrap_err();
        assert!(matches!(e, RunError::DivisionByZero));
        let e = run_numeric("2 * (1/0)").unwrap_err();
        assert!(matches!(e, RunError::DivisionByZero));
    }

    #[test]
    fn run_dimension_mismatch_returns_err() {
        let e = run("1 m + 1 s").unwrap_err();
        assert!(matches!(e, RunError::DimensionMismatch { .. }));
    }

    /// Adding or subtracting quantities with *different units* but the *same dimension* is supported.
    #[test]
    fn add_same_dimension_different_units_length() {
        let q = run_numeric("1 km + 500 m").unwrap();
        assert!((q.value() - 1500.0).abs() < 1e-6, "1 km + 500 m = 1500 m");
        assert_eq!(q.unit().iter().next().unwrap().unit_name, "m");

        let q2 = run_numeric("500 m + 1 km").unwrap();
        assert!((q2.value() - 1500.0).abs() < 1e-6, "commutativity");
        assert_eq!(q2.unit().iter().next().unwrap().unit_name, "m");

        let q3 = run_numeric("1 mile + 1 km").unwrap();
        assert!((q3.value() - 2.609_344).abs() < 1e-3);
        assert_eq!(q3.unit().iter().next().unwrap().unit_name, "km");
    }

    #[test]
    fn add_same_dimension_different_units_time() {
        let q = run_numeric("1 hour + 30 minute").unwrap();
        assert!((q.value() - 90.0).abs() < 1e-6);
        assert_eq!(q.unit().iter().next().unwrap().unit_name, "minute");

        let q2 = run_numeric("60 minute + 1 hour").unwrap();
        assert!((q2.value() - 120.0).abs() < 1e-6);
        assert_eq!(q2.unit().iter().next().unwrap().unit_name, "minute");
    }

    #[test]
    fn second_and_seconds_recognized_as_time_units() {
        let q = run_numeric("1 second").unwrap();
        assert!((q.value() - 1.0).abs() < 1e-10);
        assert_eq!(q.unit().iter().next().unwrap().unit_name, "second");

        let q2 = run_numeric("5 seconds").unwrap();
        assert!((q2.value() - 5.0).abs() < 1e-10);
        assert_eq!(q2.unit().iter().next().unwrap().unit_name, "second");

        let q3 = run_numeric("1 minute + 30 seconds").unwrap();
        assert!((q3.value() - 90.0).abs() < 1e-6);
        assert_eq!(q3.unit().iter().next().unwrap().unit_name, "second");
    }

    #[test]
    fn long_form_base_unit_aliases() {
        for (expr, unit_name) in [
            ("1 ampere", "ampere"),
            ("1 kelvin", "kelvin"),
            ("1 mole", "mole"),
            ("1 gram", "gram"),
            ("1 volt", "volt"),
        ] {
            let q = run_numeric(expr).unwrap();
            assert!((q.value() - 1.0).abs() < 1e-10, "{}", expr);
            assert_eq!(q.unit().iter().next().unwrap().unit_name, unit_name, "{}", expr);
        }
    }

    #[test]
    fn add_same_dimension_different_units_mass() {
        let q = run_numeric("1 kg + 500 g").unwrap();
        assert!((q.value() - 1500.0).abs() < 1e-6);
        assert_eq!(q.unit().iter().next().unwrap().unit_name, "g");
    }

    #[test]
    fn sub_same_dimension_different_units() {
        let q = run_numeric("1 km - 300 m").unwrap();
        assert!((q.value() - 700.0).abs() < 1e-6);
        assert_eq!(q.unit().iter().next().unwrap().unit_name, "m");

        let q2 = run_numeric("1 hour - 15 minute").unwrap();
        assert!((q2.value() - 45.0).abs() < 1e-6);
        assert_eq!(q2.unit().iter().next().unwrap().unit_name, "minute");
    }

    #[test]
    fn add_different_dimensions_errors() {
        assert!(run("1 m + 1 s").is_err());
        assert!(run("1 kg + 1 s").is_err());
        assert!(run("1 hour - 1 m").is_err());
    }

    #[test]
    fn run_numbat_parity_mile_parsec_ev() {
        let q_mile = run_numeric("1 mile").unwrap();
        assert!((q_mile.value() - 1.0).abs() < 1e-10);
        assert_eq!(q_mile.unit().iter().next().unwrap().unit_name, "mile");
        let q_parsec = run_numeric("1 parsec").unwrap();
        assert!((q_parsec.value() - 1.0).abs() < 1e-10);
        let q_ev = run_numeric("1 eV").unwrap();
        assert!((q_ev.value() - 1.0).abs() < 1e-10);
    }

    #[test]
    fn run_long_form_units_kilometers() {
        let q = run_numeric("32 kilometers").unwrap();
        assert!((q.value() - 32.0).abs() < 1e-10);
        assert_eq!(q.unit().iter().next().unwrap().unit_name, "kilometer");
    }

    #[test]
    fn plural_unit_input_resolves_to_canonical_singular() {
        let q_meters = run_numeric("2 meters").unwrap();
        assert!((q_meters.value() - 2.0).abs() < 1e-10);
        assert_eq!(q_meters.unit().iter().next().unwrap().unit_name, "meter");

        let q_seconds = run_numeric("1 seconds").unwrap();
        assert!((q_seconds.value() - 1.0).abs() < 1e-10);
        assert_eq!(q_seconds.unit().iter().next().unwrap().unit_name, "second");
    }

    #[test]
    fn run_numbat_parity_compound_velocity() {
        let q = run_numeric("100 km / hour").unwrap();
        assert!((q.value() - 100.0).abs() < 1e-10);
        let factors: Vec<_> = q.unit().iter().collect();
        assert_eq!(factors.len(), 2);
    }

    #[test]
    fn run_per_alias_for_division() {
        let q_slash = run_numeric("3 kilometers / hour").unwrap();
        let q_per = run_numeric("3 kilometers per hour").unwrap();
        assert!((q_slash.value() - q_per.value()).abs() < 1e-10);
        assert_eq!(q_slash.unit(), q_per.unit());
        assert!((q_per.value() - 3.0).abs() < 1e-10);
        // Plural "kilometers" resolves to canonical singular in compound units
        let factors: Vec<_> = q_slash.unit().iter().map(|f| f.unit_name.as_str()).collect();
        assert!(factors.contains(&"kilometer"), "compound with plural should use canonical singular: {:?}", factors);
    }

    #[test]
    fn run_symbolic_default_pi() {
        let v = run("1 + pi").unwrap();
        let s = v.to_string();
        assert!(s.contains("pi") || s.contains("π"), "expected 1 + pi or 1 + π, got {s}");
        let v = run("3 + 2 + pi + 1").unwrap();
        let s = v.to_string();
        assert!(s.contains("6") && (s.contains("pi") || s.contains("π")), "expected 6 + π, got {s}");
    }

    #[test]
    fn run_numeric_substitutes_pi() {
        let q = run_numeric("1 + pi").unwrap();
        assert!((q.value() - (1.0 + std::f64::consts::PI)).abs() < 1e-10);
        assert!(q.unit().is_scalar());
    }

    #[test]
    fn parse_unicode_pi_symbol() {
        let v = run("π").unwrap();
        assert!(matches!(v, Value::Symbolic(_)));
        assert_eq!(v.to_string(), "π");
    }

    #[test]
    fn run_symbolic_mul_div_neg() {
        let v = run("2 * pi").unwrap();
        let s = v.to_string();
        assert!(s.contains("2") && (s.contains("pi") || s.contains("π")), "2*π: {s}");
        let v = run("(1 + pi) / 2").unwrap();
        let s = v.to_string();
        assert!(s.contains("1") || s.contains("pi") || s.contains("π"), " (1+π)/2: {s}");
        let v = run("-pi").unwrap();
        assert!(matches!(v, Value::Symbolic(_)));
        let s = v.to_string();
        assert!(s.starts_with('-') && (s.contains("pi") || s.contains("π")), "-π: {s}");
    }

    #[test]
    fn run_symbolic_add_mixed_units_same_dimension() {
        let v = run("1 km + pi * 1 m").unwrap();
        assert!(matches!(v, Value::Symbolic(_)));
        let s = v.to_string();
        assert!(s.contains("m") && (s.contains("1000") || s.contains("π") || s.contains("pi")), "1 km + π*1 m in m: {s}");
        let q = run_numeric("1 km + pi * 1 m").unwrap();
        assert!((q.value() - (1000.0 + std::f64::consts::PI)).abs() < 1e-6);
        assert_eq!(q.unit().iter().next().unwrap().unit_name, "m");
    }

    #[test]
    fn run_cas_symbolic_like_terms_2pi_plus_3pi() {
        let v = run("2*pi + 3*pi").unwrap();
        let s = v.to_string();
        assert!(s.contains("5") && (s.contains("π") || s.contains("pi")), "expected 5π, got {s}");
    }

    #[test]
    fn run_neg2_abc_over_2_simplifies_to_neg_abc() {
        // "(-2 abc)/2" parses as Neg(2 abc)/2; should simplify to -(abc)
        let v = run("(-2 abc)/2").unwrap();
        let s = v.to_string();
        assert!(
            !s.contains(" / ") && s.contains("abc"),
            "expected -abc (no division), got {s}"
        );
    }

    #[test]
    fn run_cas_numeric_2pi_plus_3pi() {
        let q = run_numeric("2*pi + 3*pi").unwrap();
        let expected = 5.0 * std::f64::consts::PI;
        assert!((q.value() - expected).abs() < 1e-10);
        assert!(q.unit().is_scalar());
    }

    #[test]
    fn parse_sin_call() {
        let e = parse("sin(1)").unwrap();
        let inner = match &e {
            ExprDef::Block(v) if v.len() == 1 => &v[0],
            _ => panic!("expected Block([Call]), got {:?}", e),
        };
        match inner {
            ExprDef::Call(name, args) => {
                assert_eq!(name, "sin");
                assert_eq!(args.len(), 1);
                match &args[0] {
                    CallArg::Positional(inner) => assert!(matches!(inner.as_ref(), ExprDef::LitScalar(_))),
                    _ => panic!("expected positional arg"),
                }
            }
            _ => panic!("expected Call, got {:?}", inner),
        }
    }

    #[test]
    fn parse_max_two_args() {
        let e = parse("max(1, 2)").unwrap();
        let inner = match &e {
            ExprDef::Block(v) if v.len() == 1 => &v[0],
            _ => panic!("expected Block([Call])"),
        };
        match inner {
            ExprDef::Call(name, args) => {
                assert_eq!(name, "max");
                assert_eq!(args.len(), 2);
                assert!(matches!(&args[0], CallArg::Positional(_)), "first arg positional");
                assert!(matches!(&args[1], CallArg::Positional(_)), "second arg positional");
            }
            _ => panic!("expected Call"),
        }
    }

    #[test]
    fn parse_max_named_args() {
        let e = parse("max(a: 1, b: 2)").unwrap();
        let inner = match &e {
            ExprDef::Block(v) if v.len() == 1 => &v[0],
            _ => panic!("expected Block([Call])"),
        };
        match inner {
            ExprDef::Call(name, args) => {
                assert_eq!(name, "max");
                assert_eq!(args.len(), 2);
                match &args[0] {
                    CallArg::Named(n, _) => assert_eq!(n, "a"),
                    _ => panic!("expected named"),
                }
                match &args[1] {
                    CallArg::Named(n, _) => assert_eq!(n, "b"),
                    _ => panic!("expected named"),
                }
            }
            _ => panic!("expected Call"),
        }
    }

    #[test]
    fn eval_sin_zero() {
        let v = run("sin(0 rad)").unwrap();
        let q = v.to_quantity(&SymbolRegistry::default_registry()).unwrap();
        assert!((q.value() - 0.0).abs() < 1e-10);
    }

    #[test]
    fn eval_max() {
        let v = run_numeric("max(3, 2)").unwrap();
        assert!((v.value() - 3.0).abs() < 1e-10);
        let v = run_numeric("min(3, 2)").unwrap();
        assert!((v.value() - 2.0).abs() < 1e-10);
    }

    #[test]
    fn eval_max_min_named_args_only() {
        let v = run_numeric("max(a: 1, b: 2)").unwrap();
        assert!((v.value() - 2.0).abs() < 1e-10, "max(a: 1, b: 2) = 2");
        let v = run_numeric("min(a: 1, b: 2)").unwrap();
        assert!((v.value() - 1.0).abs() < 1e-10, "min(a: 1, b: 2) = 1");
    }

    #[test]
    fn eval_max_min_mixed_positional_and_named_args() {
        let v = run_numeric("max(1, b: 2)").unwrap();
        assert!((v.value() - 2.0).abs() < 1e-10, "max(1, b: 2) = 2");
        let v = run_numeric("max(a: 1, 2)").unwrap();
        assert!((v.value() - 2.0).abs() < 1e-10, "max(a: 1, 2) = 2");
        let v = run_numeric("min(10, b: 3)").unwrap();
        assert!((v.value() - 3.0).abs() < 1e-10, "min(10, b: 3) = 3");
    }

    #[test]
    fn run_numeric_sin_pi() {
        let q = run_numeric("sin(pi * rad)").unwrap();
        assert!(q.value().abs() < 1e-10);
    }

    #[test]
    fn run_sin_pi_returns_numeric_zero() {
        // sin(pi * rad) returns exact symbolic 0 (or numeric 0); to_quantity yields zero.
        let v = run("sin(pi * rad)").unwrap();
        let q = v.to_quantity(&SymbolRegistry::default_registry()).unwrap();
        assert!(q.value().abs() < 1e-10, "sin(pi * rad) should evaluate to 0");
    }

    #[test]
    fn run_symbolic_sin_pi() {
        // sin(x) with unknown x stays symbolic
        let v = run("sin(x)").unwrap();
        let s = format!("{}", v);
        assert!(s.contains("sin"));
        assert!(s.contains("x"));
    }

    #[test]
    fn run_unknown_function_errors() {
        let e = run("foo(1)");
        assert!(matches!(e, Err(RunError::UnknownFunction(_))));
    }

    // --- User-defined functions ---

    #[test]
    fn parse_anonymous_lambda() {
        let parsed = parse("fn (a, b) => (a + b)").unwrap();
        assert!(matches!(parsed, ExprDef::Block(ref v) if v.len() == 1 && matches!(&v[0], ExprDef::Lambda(_, _))));
        if let ExprDef::Block(ref v) = parsed {
            if let ExprDef::Lambda(params, _) = &v[0] {
                assert_eq!(params.len(), 2);
                assert_eq!(params[0].0, "a");
                assert_eq!(params[1].0, "b");
                assert!(params[0].1.is_none());
                assert!(params[1].1.is_none());
            }
        }
    }

    #[test]
    fn parse_named_function() {
        let parsed = parse("fn mysum(a, b) => (a + b)").unwrap();
        assert!(matches!(parsed, ExprDef::Block(ref v) if v.len() == 1));
        if let ExprDef::Block(ref v) = parsed {
            assert!(matches!(&v[0], ExprDef::Binding(ref n, ref rhs) if n == "mysum" && matches!(rhs.as_ref(), ExprDef::Lambda(_, _))));
        }
    }

    #[test]
    fn parse_lambda_default_param() {
        let parsed = parse("fn (a, b = 0) => (a + b)").unwrap();
        assert!(matches!(parsed, ExprDef::Block(ref v) if v.len() == 1 && matches!(&v[0], ExprDef::Lambda(_, _))));
        if let ExprDef::Block(ref v) = parsed {
            if let ExprDef::Lambda(params, _) = &v[0] {
                assert_eq!(params.len(), 2);
                assert!(params[0].1.is_none());
                assert!(params[1].1.is_some());
            }
        }
    }

    #[test]
    fn run_named_function_call() {
        let v = run_with_registry(
            "fn mysum(a, b) => (a + b)\nmysum(1, 2)",
            &default_si_registry(),
        )
        .unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric, got {:?}", v) };
        assert!((q.value() - 3.0).abs() < 1e-10);
    }

    #[test]
    fn run_user_function_default_param() {
        let v = run_with_registry(
            "fn add(a, b = 10) => (a + b)\nadd(5)",
            &default_si_registry(),
        )
        .unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric") };
        assert!((q.value() - 15.0).abs() < 1e-10);
    }

    #[test]
    fn run_user_function_positional_args() {
        let v = run_with_registry(
            "fn sub(a, b) => (a - b)\nsub(10, 2)",
            &default_si_registry(),
        )
        .unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric") };
        assert!((q.value() - 8.0).abs() < 1e-10, "sub(10, 2) = 8");
    }

    #[test]
    fn run_user_function_named_args() {
        let v = run_with_registry(
            "fn sub(a, b) => (a - b)\nsub(b: 2, a: 10)",
            &default_si_registry(),
        )
        .unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric") };
        assert!((q.value() - 8.0).abs() < 1e-10, "named order b,a => a - b = 10 - 2 = 8");
    }

    #[test]
    fn run_user_function_mixed_positional_and_named_args() {
        let v = run_with_registry(
            "fn sub(a, b) => (a - b)\nsub(10, b: 2)",
            &default_si_registry(),
        )
        .unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric") };
        assert!((q.value() - 8.0).abs() < 1e-10, "sub(10, b: 2) => a=10, b=2 => 8");
        let v = run_with_registry(
            "fn sub(a, b) => (a - b)\nsub(a: 10, 2)",
            &default_si_registry(),
        )
        .unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric") };
        assert!((q.value() - 8.0).abs() < 1e-10, "sub(a: 10, 2) => a=10, b=2 => 8");
    }

    #[test]
    fn run_user_function_unknown_parameter_name() {
        let e = run_with_registry(
            "fn sub(a, b) => (a - b)\nsub(z: 1, b: 2)",
            &default_si_registry(),
        )
        .unwrap_err();
        assert!(
            matches!(e, RunError::UnknownFunction(ref s) if s.contains("unknown parameter") && s.contains("z")),
            "expected unknown parameter 'z', got {:?}",
            e
        );
    }

    #[test]
    fn run_user_function_duplicate_parameter() {
        let e = run_with_registry(
            "fn sub(a, b) => (a - b)\nsub(a: 10, a: 2)",
            &default_si_registry(),
        )
        .unwrap_err();
        assert!(
            matches!(e, RunError::UnknownFunction(ref s) if s.contains("duplicate parameter") && s.contains("a")),
            "expected duplicate parameter 'a', got {:?}",
            e
        );
    }

    #[test]
    fn run_user_function_too_many_args() {
        let e = run_with_registry(
            "fn sub(a, b) => (a - b)\nsub(1, 2, 3)",
            &default_si_registry(),
        )
        .unwrap_err();
        assert!(
            matches!(e, RunError::UnknownFunction(ref s) if s.contains("too many arguments") && s.contains("expected 2")),
            "expected too many arguments (expected 2), got {:?}",
            e
        );
    }

    #[test]
    fn run_user_function_closure() {
        // Function uses variable x defined outside the function (closure over outer scope).
        let v = run_with_registry(
            "x = 100\nfn addx(n) => (n + x)\naddx(5)",
            &default_si_registry(),
        )
        .unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric") };
        assert!((q.value() - 105.0).abs() < 1e-10, "addx(5) = 5 + 100 = 105");
    }

    #[test]
    fn run_user_function_closure_multiple_outer_variables() {
        // Function uses several variables defined outside the function (closure over a, b, c).
        let v = run_with_registry(
            "a = 1\nb = 2\nc = 3\nfn sum_outer(_) => (a + b + c)\nsum_outer(0)",
            &default_si_registry(),
        )
        .unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric") };
        assert!((q.value() - 6.0).abs() < 1e-10, "1 + 2 + 3 = 6");
    }

    #[test]
    fn run_user_function_closure_uses_definition_scope_not_call_scope() {
        // Closure captures bindings at definition time; rebinding the same name at call site does not change the function's view.
        let v = run_with_registry(
            "x = 10\nfn get_x(_) => (x)\n{ x = 99; get_x(0) }",
            &default_si_registry(),
        )
        .unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric") };
        assert!((q.value() - 10.0).abs() < 1e-10, "get_x captures x=10 at definition, not 99 at call site");
    }

    #[test]
    fn run_user_function_parameter_shadows_outer() {
        // Parameter shadows outer variable of the same name; body sees the argument, not the outer binding.
        let v = run_with_registry(
            "x = 100\nfn f(x) => (x + 1)\nf(2)",
            &default_si_registry(),
        )
        .unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric") };
        assert!((q.value() - 3.0).abs() < 1e-10, "f(2) uses param x=2, not outer 100");
    }

    #[test]
    fn run_cannot_obfuscate_builtin_sin() {
        let e = run_with_registry("sin = 3", &default_si_registry()).unwrap_err();
        assert!(matches!(e, RunError::CannotObfuscateBuiltin(s) if s == "sin"));
    }

    #[test]
    fn run_cannot_obfuscate_builtin_max() {
        let e = run_with_registry("max = fn (a, b) => (a + b)", &default_si_registry()).unwrap_err();
        assert!(matches!(e, RunError::CannotObfuscateBuiltin(s) if s == "max"));
    }

    #[test]
    fn run_user_function_block_body() {
        let v = run_with_registry(
            "fn myCrazySumPlus42(param1, param2) => { otherVar = param1 + param2; otherVar + 42 }\nmyCrazySumPlus42(10, 5)",
            &default_si_registry(),
        )
        .unwrap();
        let Value::Numeric(q) = v else { panic!("expected numeric") };
        assert!((q.value() - 57.0).abs() < 1e-10, "10+5=15, 15+42=57");
    }

    #[test]
    fn run_user_function_missing_required_arg() {
        let e = run_with_registry(
            "fn needTwo(a, b) => (a + b)\nneedTwo(1)",
            &default_si_registry(),
        )
        .unwrap_err();
        assert!(
            matches!(e, RunError::UnknownFunction(ref s) if s.contains("missing") && s.contains("b")),
            "expected missing argument for parameter 'b', got {:?}",
            e
        );
    }

    #[test]
    fn run_format_function_result_prints_function() {
        // Program that only defines a function: result is Value::Function; display as <function>.
        assert_eq!(
            run_format("fn ABCDFFF(n) => { 32 + n }").unwrap(),
            "<function>"
        );
    }

    // --- Vector literal and vector type ---

    #[test]
    fn parse_vector_literal() {
        use crate::ir::ExprDef;
        let r = parse("[1]").unwrap();
        assert!(matches!(r, ExprDef::Block(ref v) if v.len() == 1 && matches!(&v[0], ExprDef::VecLiteral(e) if e.len() == 1)));
        let r = parse("[1, 2*3]").unwrap();
        assert!(matches!(r, ExprDef::Block(ref v) if v.len() == 1 && matches!(&v[0], ExprDef::VecLiteral(e) if e.len() == 2)));
        let r = parse("[]").unwrap();
        assert!(matches!(r, ExprDef::Block(ref v) if v.len() == 1 && matches!(&v[0], ExprDef::VecLiteral(e) if e.is_empty())));
    }

    #[test]
    fn parse_vector_transpose() {
        use crate::ir::ExprDef;
        let r = parse("[1, 2, 3]'").unwrap();
        assert!(matches!(r, ExprDef::Block(ref v) if v.len() == 1 && matches!(&v[0], ExprDef::Transpose(ref b) if matches!(b.as_ref(), ExprDef::VecLiteral(e) if e.len() == 3))));
    }

    #[test]
    fn run_vector_transpose_format() {
        assert_eq!(run_format("[1, 2, 3]'").unwrap(), "[1, 2, 3]");
        assert_eq!(run_format("([1, 2] + 10)'").unwrap(), "[11, 12]");
        // Chained transpose: still identity for 1D
        assert_eq!(run_format("[1, 2, 3]''").unwrap(), "[1, 2, 3]");
        // 2D transpose: rows become columns
        assert_eq!(
            run_format("[[1, 4], [2, 2], [3, 5]]'").unwrap(),
            "[[1, 2, 3], [4, 2, 5]]"
        );
        // 2D transpose with empty rows: 3×0 -> 0×3, so no columns
        assert_eq!(run_format("[[], [], []]'").unwrap(), "[]");
    }

    #[test]
    fn run_transpose_non_vector_errors() {
        let e = run("3'").unwrap_err();
        assert!(matches!(e, RunError::ExpectedVector));
        let e = run("(1 + 2)'").unwrap_err();
        assert!(matches!(e, RunError::ExpectedVector));
    }

    #[test]
    fn run_vector_literal_returns_vector() {
        let v = run("[1, 2, 3]").unwrap();
        assert!(matches!(v, Value::Vector(_)));
        assert_eq!(format!("{}", v), "<vector>");

        let v = run("[]").unwrap();
        assert!(matches!(v, Value::Vector(_)));
    }

    #[test]
    fn run_vector_orientation_column_row_transpose() {
        use crate::vector::VectorOrientation;

        // Literal: column by default
        let v = run("[1, 2, 3]").unwrap();
        let vec_val = match &v {
            Value::Vector(w) => w,
            _ => panic!("expected vector"),
        };
        assert_eq!(vec_val.orientation, VectorOrientation::Column, "literal is column");

        // Single transpose: row
        let v = run("[1, 2, 3]'").unwrap();
        let vec_val = match &v {
            Value::Vector(w) => w,
            _ => panic!("expected vector"),
        };
        assert_eq!(vec_val.orientation, VectorOrientation::Row, "transposed is row");

        // Chained transpose: column again
        let v = run("[1, 2, 3]''").unwrap();
        let vec_val = match &v {
            Value::Vector(w) => w,
            _ => panic!("expected vector"),
        };
        assert_eq!(
            vec_val.orientation,
            VectorOrientation::Column,
            "double transpose is column"
        );

        // Map preserves orientation: row vector + scalar → row
        let v = run("[1, 2, 3]' + 0").unwrap();
        let vec_val = match &v {
            Value::Vector(w) => w,
            _ => panic!("expected vector"),
        };
        assert_eq!(
            vec_val.orientation,
            VectorOrientation::Row,
            "map preserves row orientation"
        );
    }

    #[test]
    fn run_numeric_vector_returns_err() {
        let e = run_numeric("[1, 2]").unwrap_err();
        assert!(matches!(e, RunError::UnsupportedVectorOperation));
    }

    #[test]
    fn run_vector_arithmetic_errors() {
        // Column + column is element-wise.
        assert_eq!(run_format("[1, 2] + [3, 4]").unwrap(), "[4, 6]");
        // Vector × vector with incompatible length: error when stream is consumed (format).
        let e = run_format("[1, 2] + [3, 4, 5]").unwrap_err();
        assert!(matches!(e, RunError::VectorLengthMismatch { .. }));
    }

    #[test]
    fn run_vector_vector_element_wise() {
        // Column × column: element-wise, result column.
        assert_eq!(run_format("[1, 2] + [3, 4]").unwrap(), "[4, 6]");
        assert_eq!(run_format("[5, 10] - [1, 2]").unwrap(), "[4, 8]");
        assert_eq!(run_format("[2, 3] * [4, 5]").unwrap(), "[8, 15]");
        assert_eq!(run_format("[10, 20] / [2, 4]").unwrap(), "[5, 5]");
        // Row × row: element-wise, result row.
        assert_eq!(run_format("[1, 2]' + [3, 4]'").unwrap(), "[4, 6]");
        assert_eq!(run_format("[2, 3]' * [4, 5]'").unwrap(), "[8, 15]");
    }

    #[test]
    fn run_vector_vector_outer_product() {
        // Column (N) × Row (M) → N×M matrix (vector of column vectors). Each column is left_i * row.
        let s = run_format("[1, 2] * [3, 4]'").unwrap();
        // Columns: col0 = [1*3, 2*3] = [3, 6], col1 = [1*4, 2*4] = [4, 8].
        assert_eq!(s, "[[3, 6], [4, 8]]");
    }

    #[test]
    fn run_vector_vector_dot_product() {
        // Row × Column → dot product (scalar). CAS preserves vector×vector Mul order, so dot stays dot.
        let v = run("[1, 2]' * [3, 4]").unwrap();
        match &v {
            Value::Numeric(q) => assert!((q.value() - 11.0).abs() < 1e-10, "1*3+2*4 = 11"),
            other => panic!("expected scalar 11, got {:?}", other),
        }
        let v2 = run("[3, 4]' * [1, 2]").unwrap();
        match &v2 {
            Value::Numeric(q) => assert!((q.value() - 11.0).abs() < 1e-10, "3*1+4*2 = 11"),
            other => panic!("expected scalar 11, got {:?}", other),
        }
        // Orthogonal: 1*0 + 0*1 = 0.
        let v0 = run("[1, 0]' * [0, 1]").unwrap();
        match &v0 {
            Value::Numeric(q) => assert!(q.value().abs() < 1e-10),
            other => panic!("expected scalar 0, got {:?}", other),
        }
    }

    #[test]
    fn run_vector_vector_empty() {
        // []' * [] = row×column = dot of empties = 0. CAS preserves vector×vector order.
        assert_eq!(run_format("[]' * []").unwrap(), "0");
        // Empty outer: empty col × row → no columns.
        assert_eq!(run_format("[] * [1, 2]'").unwrap(), "[]");
    }

    #[test]
    fn run_vector_scalar_binary_mapping() {
        assert_eq!(run_format("[1, 2, 3] + 10").unwrap(), "[11, 12, 13]");
        assert_eq!(run_format("10 + [1, 2, 3]").unwrap(), "[11, 12, 13]");
        assert_eq!(run_format("[1, 2, 3] * 2").unwrap(), "[2, 4, 6]");
        assert_eq!(run_format("10 - [1, 2, 3]").unwrap(), "[9, 8, 7]");
        assert_eq!(run_format("[1, 2, 3] - 1").unwrap(), "[0, 1, 2]");
        assert_eq!(run_format("[10, 20, 30] / 10").unwrap(), "[1, 2, 3]");
        assert_eq!(run_format("100 / [10, 20, 25]").unwrap(), "[10, 5, 4]");
    }

    #[test]
    fn run_vector_scalar_binary_mapping_with_units() {
        assert_eq!(run_format("[1 m, 2 m] + 3 m").unwrap(), "[4 m, 5 m]");
    }

    #[test]
    fn run_vector_unary_neg_mapping() {
        assert_eq!(run_format("-[1, 2, 3]").unwrap(), "[-1, -2, -3]");
    }

    #[test]
    fn run_vector_unary_func_mapping() {
        // cos(0 rad) = 1, cos(pi rad) = -1
        assert_eq!(run_format("cos([0 rad, pi rad])").unwrap(), "[1, -1]");
        // sin(0 rad) = 0
        assert_eq!(run_format("sin([0 rad])").unwrap(), "[0]");
    }

    #[test]
    fn run_vector_chained_mapping() {
        // cos([0, pi rad]) + 1 → [1, -1] + 1 → [2, 0]
        assert_eq!(run_format("cos([0 rad, pi rad]) + 1").unwrap(), "[2, 0]");
    }

    #[test]
    fn parse_vector_index_bracket() {
        use crate::ir::ExprDef;
        let r = parse("V[2]").unwrap();
        assert!(matches!(r, ExprDef::Block(ref v) if v.len() == 1 && matches!(&v[0], ExprDef::Index(_, _))));
    }

    #[test]
    fn parse_vector_index_dot() {
        use crate::ir::ExprDef;
        let r = parse("V.0").unwrap();
        assert!(matches!(r, ExprDef::Block(ref v) if v.len() == 1 && matches!(&v[0], ExprDef::Index(_, _))));
        let r = parse("V.1").unwrap();
        assert!(matches!(r, ExprDef::Block(ref v) if v.len() == 1 && matches!(&v[0], ExprDef::Index(_, _))));
    }

    #[test]
    fn parse_take_call() {
        use crate::ir::ExprDef;
        let r = parse("take(V, 0, 2)").unwrap();
        assert!(matches!(r, ExprDef::Block(ref v) if v.len() == 1 && matches!(&v[0], ExprDef::Call(n, _) if n == "take")));
    }

    #[test]
    fn run_take_slice() {
        assert_eq!(run_format("take([1, 2, 3, 4], 1, 2)").unwrap(), "[2, 3]");
        assert_eq!(run_format("take([1, 2, 3, 4], 0, 4)").unwrap(), "[1, 2, 3, 4]");
        assert_eq!(run_format("take([1, 2, 3, 4], 2, 1)").unwrap(), "[3]");
    }

    #[test]
    fn run_vector_index_bracket() {
        assert_eq!(run_format("[1, 2, 3, 4][2]").unwrap(), "3");
        assert_eq!(run_format("[1, 2, 3, 4][0]").unwrap(), "1");
    }

    #[test]
    fn run_vector_index_dot() {
        assert_eq!(run_format("[1, 2, 3, 4].0").unwrap(), "1");
        assert_eq!(run_format("[1, 2, 3, 4].1").unwrap(), "2");
    }

    #[test]
    fn run_vector_index_out_of_bounds() {
        let e = run("[1, 2, 3][3]").unwrap_err();
        assert!(matches!(e, RunError::IndexOutOfBounds { .. }));
        let e = run("[1, 2, 3][10]").unwrap_err();
        assert!(matches!(e, RunError::IndexOutOfBounds { .. }));
    }

    #[test]
    fn run_vector_index_invalid() {
        let e = run("[1, 2, 3][-1]").unwrap_err();
        assert!(matches!(e, RunError::InvalidIndex(_)));
        let e = run("[1, 2, 3][pi]").unwrap_err();
        assert!(matches!(e, RunError::InvalidIndex(_)));
    }

    #[test]
    fn parse_vector_property_length() {
        use crate::ir::ExprDef;
        let r = parse("V.length").unwrap();
        assert!(matches!(r, ExprDef::Block(ref v) if v.len() == 1 && matches!(&v[0], ExprDef::Member(_, name) if name == "length")));
    }

    #[test]
    fn parse_vector_method_map() {
        use crate::ir::ExprDef;
        let r = parse("V.map(fn (x) => (x+1))").unwrap();
        assert!(matches!(r, ExprDef::Block(ref v) if v.len() == 1 && matches!(&v[0], ExprDef::MethodCall(_, name, _) if name == "map")));
    }

    #[test]
    fn parse_vector_method_take() {
        use crate::ir::ExprDef;
        let r = parse("V.take(1, 3)").unwrap();
        assert!(matches!(r, ExprDef::Block(ref v) if v.len() == 1 && matches!(&v[0], ExprDef::MethodCall(_, name, _) if name == "take")));
    }

    #[test]
    fn run_vector_length() {
        assert_eq!(run_format("[1, 2, 3].length").unwrap(), "3");
        assert_eq!(run_format("[].length").unwrap(), "0");
        assert_eq!(run_format("[1 m, 2 m].length").unwrap(), "2");
        // Length is an exact count; variance should be 0.
        let q = run_numeric("[1, 2, 3].length").unwrap();
        assert_eq!(q.value(), 3.0);
        assert_eq!(q.variance(), 0.0);
    }

    #[test]
    fn run_vector_map_method() {
        assert_eq!(run_format("[1, 2, 3].map(fn (x) => (x+1))").unwrap(), "[2, 3, 4]");
        assert_eq!(run_format("[1, 2, 3].map(fn (x) => (x*2))").unwrap(), "[2, 4, 6]");
    }

    #[test]
    fn run_vector_take_method() {
        assert_eq!(run_format("[1, 2, 3, 4].take(1, 2)").unwrap(), "[2, 3]");
        assert_eq!(run_format("[1, 2, 3, 4].take(0, 4)").unwrap(), "[1, 2, 3, 4]");
    }

    #[test]
    fn run_vector_unknown_property() {
        let e = run("[1, 2, 3].foo").unwrap_err();
        assert!(matches!(e, RunError::UnknownProperty(name) if name == "foo"));
    }

    #[test]
    fn run_vector_unknown_method() {
        let e = run("[1, 2, 3].bar(1)").unwrap_err();
        assert!(matches!(e, RunError::UnknownMethod(name) if name == "bar"));
    }

    #[test]
    fn run_vector_member_on_non_vector() {
        let e = run("(1).length").unwrap_err();
        assert!(matches!(e, RunError::ExpectedVector));
    }

    #[test]
    fn run_vector_map_requires_one_parameter() {
        let e = run("[1, 2, 3].map(fn (a, b) => (a+b))").unwrap_err();
        match &e {
            RunError::UnknownFunction(msg) => assert!(
                msg.contains("one parameter") && msg.contains("2"),
                "expected message about one parameter, got: {}", msg
            ),
            _ => panic!("expected UnknownFunction, got {:?}", e),
        }
    }

    #[test]
    fn run_vector_map_with_closure() {
        assert_eq!(
            run_format("{ c = 10; [1, 2, 3].map(fn (x) => (x + c)) }").unwrap(),
            "[11, 12, 13]"
        );
    }

    #[test]
    fn run_vector_stream_yields_elements() {
        use crate::queries::{program, set_eval_registry, value, vector_into_stream};
        use crate::resolve;
        use crate::cas;
        use salsa::DatabaseImpl;

        let registry = default_si_registry();
        let root_def = parse("[1, 2, 3]").unwrap();
        let root_def = resolve::resolve(root_def, &registry).unwrap();
        let root_def = cas::simplify_symbolic(root_def, &registry).unwrap();
        set_eval_registry(registry.clone());
        let db = DatabaseImpl::new();
        let program_def = ProgramDef::new(&db, root_def);
        let root = program(&db, program_def);
        let v = value(&db, empty_scope(&db), root).unwrap();
        let lv = match &v {
            Value::Vector(v) => v.inner.clone(),
            _ => panic!("expected vector"),
        };
        let stream = vector_into_stream(&db, lv);
        let results: Vec<_> = futures::executor::block_on(async move {
            use futures::stream::StreamExt;
            stream.collect().await
        });
        assert_eq!(results.len(), 3);
        assert!(matches!(&results[0], Ok(Some(Value::Numeric(q))) if (q.value() - 1.0).abs() < 1e-10));
        assert!(matches!(&results[1], Ok(Some(Value::Numeric(q))) if (q.value() - 2.0).abs() < 1e-10));
        assert!(matches!(&results[2], Ok(Some(Value::Numeric(q))) if (q.value() - 3.0).abs() < 1e-10));
    }

    #[test]
    fn run_format_scalar() {
        assert_eq!(run_format("2 + 3").unwrap(), "5");
        assert_eq!(run_format("1 m + 2 m").unwrap(), "3 m");
    }

    #[test]
    fn run_format_symbolic() {
        assert_eq!(run_format("1 + pi").unwrap(), "1 + π");
    }

    #[test]
    fn run_format_nested_vector() {
        let s = run_format("[[1, 2], [3, 4]]").unwrap();
        assert_eq!(s, "[[1, 2], [3, 4]]");
    }

    #[test]
    fn run_format_triple_nested_vector() {
        let s = run_format("[[[1], [2]], [[3]]]").unwrap();
        assert_eq!(s, "[[[1], [2]], [[3]]]");
    }

    #[test]
    fn run_function_wrong_arity_errors() {
        let e = run("sin(1, 2)");
        assert!(matches!(e, Err(RunError::UnknownFunction(s)) if s.contains("sin") && s.contains("argument")));
        let e = run("max(1)");
        assert!(matches!(e, Err(RunError::UnknownFunction(s)) if s.contains("max") && s.contains("argument")));
    }

    #[test]
    fn run_function_dimension_mismatch_errors() {
        let e = run_numeric("sin(1 m)");
        assert!(matches!(e, Err(RunError::ExpectedAngle { .. })));
        let e = run_numeric("sin(pi)").unwrap_err();
        assert!(matches!(e, RunError::ExpectedAngle { .. }));
        let err_msg = format!("{e}");
        assert!(err_msg.contains("rad unit"), "dimensionless argument should suggest adding rad unit: {err_msg}");
        let e = run_numeric("max(1 m, 2 s)");
        assert!(matches!(e, Err(RunError::DimensionMismatch { .. })));
    }

    #[test]
    fn run_sin_180_degree_equals_zero() {
        let q = run_numeric("sin(180 degree)").unwrap();
        assert!(q.value().abs() < 1e-10, "sin(180 degree) ≈ 0");
    }

    #[test]
    fn resolve_180_times_degrees_as_unit() {
        // Identifiers stay as LitSymbol after resolve; unit lookup happens at eval/substitute time.
        // So 180 * degrees still evaluates to 180 degree via substitute_symbols (unit registry).
        let q = run_numeric("180 * degrees").unwrap();
        assert!((q.value() - 180.0).abs() < 1e-10);
        assert_eq!(q.unit().iter().next().map(|f| f.unit_name.as_str()), Some("degree"));
    }

    #[test]
    fn simplify_sin_180_times_degrees_arg_is_180_degree() {
        // After full pipeline the sin argument must be 180 degree (not 180 scalar)
        let reg = default_si_registry();
        let sym_reg = SymbolRegistry::default_registry();
        let root = parse("sin(180 * degrees)").unwrap();
        let resolved = resolve::resolve(root, &reg).unwrap();
        let simplified = cas::simplify_numeric(resolved, &reg, &sym_reg).unwrap();
        let arg = match &simplified {
            ExprDef::Block(v) if v.len() == 1 => match &v[0] {
                ExprDef::Call(_, args) => match args.first() {
                    Some(CallArg::Positional(e)) => e.as_ref(),
                    _ => panic!("expected one positional arg"),
                },
                _ => panic!("expected Block([Call]), got {simplified:?}"),
            },
            _ => panic!("expected Block([Call]), got {simplified:?}"),
        };
        if let ExprDef::Lit(q) = arg {
            let rad = Unit::from_base_unit("rad");
            assert!(
                reg.same_dimension(q.unit(), &rad).unwrap_or(false),
                "sin argument must have angle dimension, got unit {:?}",
                q.unit()
            );
            let as_rad = q.clone().convert_to(&reg, &rad).unwrap();
            assert!(
                (as_rad.value() - std::f64::consts::PI).abs() < 1e-6,
                "sin argument should be 180° = π rad, got {} rad",
                as_rad.value()
            );
        } else {
            panic!("expected sin argument to be folded to Lit(180 degree), got {arg:?}");
        }
    }

    #[test]
    fn run_sin_180_times_degrees_equals_zero() {
        // "180 * degrees" must resolve to 180 degree (same as "180 degree")
        let q = run_numeric("sin(180 * degrees)").unwrap();
        assert!(q.value().abs() < 1e-10, "sin(180 * degrees) = sin(180°) = 0, got {}", q.value());
    }

    #[test]
    fn run_sin_90_degree_equals_one() {
        let q = run_numeric("sin(90 degree)").unwrap();
        assert!((q.value() - 1.0).abs() < 1e-10, "sin(90 degree) ≈ 1");
    }

    #[test]
    fn run_sin_90_degree_symbolic_exact() {
        // 90 degree → π/2 rad should match known angle and return symbolic 1
        let v = run("sin(90 degree)").unwrap();
        let q = v.to_quantity(&SymbolRegistry::default_registry()).unwrap();
        assert!((q.value() - 1.0).abs() < 1e-10, "sin(90 degree) = 1");
    }

    #[test]
    fn run_sin_pi_fourth_symbolic_sqrt2_over_2() {
        let v = run("sin(pi/4 * rad)").unwrap();
        let s = format!("{v}");
        assert!(
            s.contains("√2") && (s.contains("2") || s.contains("/")),
            "sin(π/4) should display with √2, got {s}"
        );
        // Substitution yields numeric √2/2
        let q = v.to_quantity(&SymbolRegistry::default_registry()).unwrap();
        assert!(
            (q.value() - 2_f64.sqrt() / 2.0).abs() < 1e-10,
            "sin(π/4) ≈ √2/2"
        );
    }

    #[test]
    fn run_numeric_sin_pi_fourth_is_number() {
        let q = run_numeric("sin(pi/4 * rad)").unwrap();
        assert!(
            (q.value() - 2_f64.sqrt() / 2.0).abs() < 1e-10,
            "run_numeric sin(π/4) should be a number ≈ √2/2"
        );
    }

    #[test]
    fn run_numeric_trig_result_is_number() {
        // When numeric is required, result must be a number (no leftover symbols).
        let q = run_numeric("cos(pi/3 * rad)").unwrap();
        assert!((q.value() - 0.5).abs() < 1e-10, "cos(π/3) = 1/2");
        let q2 = run_numeric("tan(pi/4 * rad)").unwrap();
        assert!((q2.value() - 1.0).abs() < 1e-10, "tan(π/4) = 1");
    }

    #[test]
    fn run_symbolic_trig_well_known_angles() {
        // Symbolic run keeps constants like √2, π in display.
        let v_cos = run("cos(pi/4 * rad)").unwrap();
        let s = format!("{v_cos}");
        assert!(s.contains("√2"), "cos(π/4) should show √2, got {s}");
        let v_sin = run("sin(pi/3 * rad)").unwrap();
        let s2 = format!("{v_sin}");
        assert!(s2.contains("√3"), "sin(π/3) should show √3, got {s2}");
    }

    #[test]
    fn run_trig_angle_plus_pi_numeric() {
        // sin(5π/4) = -√2/2, cos(3π/2) = 0, sin(270 degree) = -1
        let q = run_numeric("sin(5 * pi / 4 * rad)").unwrap();
        assert!(
            (q.value() - (-2_f64.sqrt() / 2.0)).abs() < 1e-10,
            "sin(5π/4) = -√2/2"
        );
        let q2 = run_numeric("cos(3 * pi / 2 * rad)").unwrap();
        assert!(q2.value().abs() < 1e-10, "cos(3π/2) = 0");
        let q3 = run_numeric("sin(270 degree)").unwrap();
        assert!((q3.value() - (-1.0)).abs() < 1e-10, "sin(270°) = -1");
    }

    #[test]
    fn run_trig_angle_plus_pi_symbolic() {
        // sin((pi + pi/4) * rad) = sin(5π/4) = -√2/2: symbolic result shows negated √2/2
        let v = run("sin((pi + pi/4) * rad)").unwrap();
        let s = format!("{v}");
        assert!(s.contains("√2"), "sin((π+π/4) rad) should show √2, got {s}");
        let q = v.to_quantity(&SymbolRegistry::default_registry()).unwrap();
        assert!(
            (q.value() - (-2_f64.sqrt() / 2.0)).abs() < 1e-10,
            "sin((π+π/4) rad) = -√2/2"
        );
    }

    #[test]
    fn reactivity_when_program_changes_value_updates() {
        let registry = default_si_registry();
        set_eval_registry(registry.clone());
        let sym = SymbolRegistry::default_registry();
        let db = salsa::DatabaseImpl::new();
        let parsed = parse("1 + 2").unwrap();
        let resolved = resolve::resolve(parsed, &default_si_registry()).unwrap();
        let program_def = ProgramDef::new(&db, resolved);
        let root = program(&db, program_def);
        assert_eq!(
            value(&db, empty_scope(&db), root).unwrap().to_quantity(&sym).unwrap().value(),
            3.0
        );
        let parsed2 = parse("10 + 2").unwrap();
        let resolved2 = resolve::resolve(parsed2, &default_si_registry()).unwrap();
        let program_def2 = ProgramDef::new(&db, resolved2);
        let root2 = program(&db, program_def2);
        assert_eq!(
            value(&db, empty_scope(&db), root2).unwrap().to_quantity(&sym).unwrap().value(),
            12.0
        );
    }
}
