//! snaq-lite: reactive arithmetic language (Salsa-based).

pub mod cas;
pub mod dimension;
pub mod error;
pub mod functions;
pub mod ir;
pub mod lexer;
pub mod parser;
pub mod prefix;
pub mod quantity;
pub mod queries;
pub mod resolve;
pub mod symbol_registry;
pub mod symbolic;
pub mod unit;
pub mod unit_registry;

pub use error::{ParseError, RunError};
pub use quantity::{Quantity, QuantityError, SnaqNumber};
pub use unit::Unit;
pub use ir::{ExprDef, Expression, ProgramDef};
pub use parser::parse;
pub use queries::{program, set_eval_registry, value};
pub use symbol_registry::SymbolRegistry;
pub use symbolic::{SymbolicQuantity, SymbolicExpr, Value};
pub use unit_registry::{default_si_registry, UnitRegistry};

/// Parse and evaluate the expression, returning a Value (symbolic by default, e.g. "6 + π").
///
/// Supports float literals, quantity literals (e.g. `100 m`), symbols (e.g. `pi`, `π`, `e`),
/// implicit multiplication, division as `/` or `per`, and unit conversion with `as` (e.g. `10 km as m`).
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
    value(&db, root)
}

/// Evaluate and substitute all symbols with their numeric values; returns a single Quantity.
/// Errors if any symbol has no value in the default symbol registry.
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
    let v = value(&db, root)?;
    v.to_quantity(symbol_registry)
}

/// Evaluate in numeric mode and return the scalar value only if dimensionless.
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
    use crate::ir::{CallArg, ExprDef};
    use ordered_float::OrderedFloat;

    fn lit_scalar(n: f64) -> ExprDef {
        ExprDef::LitScalar(OrderedFloat::from(n))
    }

    #[test]
    fn parse_lit() {
        assert_eq!(parse("1").unwrap(), lit_scalar(1.0));
        assert_eq!(parse("42").unwrap(), lit_scalar(42.0));
        assert_eq!(parse("0").unwrap(), lit_scalar(0.0));
        assert_eq!(parse("1.5").unwrap(), lit_scalar(1.5));
        assert_eq!(parse(".5").unwrap(), lit_scalar(0.5));
        assert_eq!(parse("2e1").unwrap(), lit_scalar(20.0));
        assert_eq!(
            parse("9223372036854775807").unwrap(),
            lit_scalar(9223372036854775807.0)
        );
    }

    #[test]
    fn parse_add() {
        assert_eq!(
            parse("1 + 2").unwrap(),
            ExprDef::Add(Box::new(lit_scalar(1.0)), Box::new(lit_scalar(2.0)))
        );
    }

    #[test]
    fn parse_sub() {
        assert_eq!(
            parse("1 - 2").unwrap(),
            ExprDef::Sub(Box::new(lit_scalar(1.0)), Box::new(lit_scalar(2.0)))
        );
    }

    #[test]
    fn parse_unary_minus() {
        assert_eq!(
            parse("-1").unwrap(),
            ExprDef::Neg(Box::new(lit_scalar(1.0)))
        );
        assert_eq!(
            parse("-(2 * 3)").unwrap(),
            ExprDef::Neg(Box::new(ExprDef::Mul(
                Box::new(lit_scalar(2.0)),
                Box::new(lit_scalar(3.0))
            )))
        );
    }

    #[test]
    fn parse_mul() {
        assert_eq!(
            parse("2 * 3").unwrap(),
            ExprDef::Mul(Box::new(lit_scalar(2.0)), Box::new(lit_scalar(3.0)))
        );
    }

    #[test]
    fn parse_implicit_mul() {
        assert_eq!(
            parse("10 20").unwrap(),
            ExprDef::Mul(Box::new(lit_scalar(10.0)), Box::new(lit_scalar(20.0)))
        );
    }

    #[test]
    fn parse_div() {
        assert_eq!(
            parse("6 / 2").unwrap(),
            ExprDef::Div(Box::new(lit_scalar(6.0)), Box::new(lit_scalar(2.0)))
        );
    }

    #[test]
    fn parse_per_same_as_div() {
        assert_eq!(
            parse("6 per 2").unwrap(),
            ExprDef::Div(Box::new(lit_scalar(6.0)), Box::new(lit_scalar(2.0)))
        );
    }

    #[test]
    fn parse_ident_containing_per_still_ident() {
        // "per" is reserved as operator; identifiers like "percent" are still parsed as Ident
        assert_eq!(
            parse("1 percent").unwrap(),
            ExprDef::Mul(
                Box::new(ExprDef::LitScalar(OrderedFloat::from(1.0))),
                Box::new(ExprDef::LitUnit("percent".to_string()))
            )
        );
    }

    #[test]
    fn parse_with_parens() {
        assert_eq!(
            parse("(1 + 2) - 1").unwrap(),
            ExprDef::Sub(
                Box::new(ExprDef::Add(Box::new(lit_scalar(1.0)), Box::new(lit_scalar(2.0)))),
                Box::new(lit_scalar(1.0))
            )
        );
    }

    #[test]
    fn parse_precedence_mul_tighter_than_add() {
        assert_eq!(
            parse("1 + 2 * 3").unwrap(),
            ExprDef::Add(
                Box::new(lit_scalar(1.0)),
                Box::new(ExprDef::Mul(Box::new(lit_scalar(2.0)), Box::new(lit_scalar(3.0))))
            )
        );
    }

    #[test]
    fn parse_precedence_div_tighter_than_sub() {
        assert_eq!(
            parse("6 - 4 / 2").unwrap(),
            ExprDef::Sub(
                Box::new(lit_scalar(6.0)),
                Box::new(ExprDef::Div(Box::new(lit_scalar(4.0)), Box::new(lit_scalar(2.0))))
            )
        );
    }

    #[test]
    fn parse_precedence_parens_override() {
        assert_eq!(
            parse("(1 + 2) * 3").unwrap(),
            ExprDef::Mul(
                Box::new(ExprDef::Add(Box::new(lit_scalar(1.0)), Box::new(lit_scalar(2.0)))),
                Box::new(lit_scalar(3.0))
            )
        );
    }

    #[test]
    fn parse_quantity_literal() {
        // "100 m" and "10 m" parse as implicit mul (number * unit) and resolve to same quantity
        assert_eq!(
            parse("100 m").unwrap(),
            ExprDef::Mul(
                Box::new(ExprDef::LitScalar(OrderedFloat::from(100.0))),
                Box::new(ExprDef::LitUnit("m".to_string()))
            )
        );
        assert_eq!(
            parse("10 m").unwrap(),
            ExprDef::Mul(
                Box::new(ExprDef::LitScalar(OrderedFloat::from(10.0))),
                Box::new(ExprDef::LitUnit("m".to_string()))
            )
        );
        // "1.5 * km" parses as Mul(LitScalar(1.5), LitUnit("km")) and resolves to 1.5 km
        assert_eq!(
            parse("1.5 * km").unwrap(),
            ExprDef::Mul(
                Box::new(ExprDef::LitScalar(OrderedFloat::from(1.5))),
                Box::new(ExprDef::LitUnit("km".to_string()))
            )
        );
        assert_eq!(parse("hour").unwrap(), ExprDef::LitUnit("hour".to_string()));
    }

    #[test]
    fn parse_2_pi_rad_implicit_mul() {
        // "2 pi rad" parses as implicit mul chain (2 * pi * rad); pi → symbol, rad → unit
        let parsed = parse("2 pi rad").unwrap();
        let expected = ExprDef::Mul(
            Box::new(ExprDef::Mul(
                Box::new(ExprDef::LitScalar(OrderedFloat::from(2.0))),
                Box::new(ExprDef::LitUnit("pi".to_string())),
            )),
            Box::new(ExprDef::LitUnit("rad".to_string())),
        );
        assert_eq!(parsed, expected);
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
        // "10 km as m" parses as Expr::As(Term(10 km), UnitTerm(m))
        let parsed = parse("10 km as m").unwrap();
        assert!(matches!(parsed, ExprDef::As(_, _)));
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
        assert_eq!(parsed, expected);
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
    fn parse_empty_is_error() {
        assert!(parse("").is_err());
        assert!(parse("   ").is_err());
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
        assert!(run("").is_err());
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
        match &e {
            ExprDef::Call(name, args) => {
                assert_eq!(name, "sin");
                assert_eq!(args.len(), 1);
                match &args[0] {
                    CallArg::Positional(inner) => assert!(matches!(inner.as_ref(), ExprDef::LitScalar(_))),
                    _ => panic!("expected positional arg"),
                }
            }
            _ => panic!("expected Call, got {:?}", e),
        }
    }

    #[test]
    fn parse_max_two_args() {
        let e = parse("max(1, 2)").unwrap();
        match &e {
            ExprDef::Call(name, args) => {
                assert_eq!(name, "max");
                assert_eq!(args.len(), 2);
            }
            _ => panic!("expected Call"),
        }
    }

    #[test]
    fn parse_max_named_args() {
        let e = parse("max(a: 1, b: 2)").unwrap();
        match &e {
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
        // "degrees" must resolve as unit so 180 * degrees = 180 degree
        use crate::ir::ExprDef;
        let reg = default_si_registry();
        let root = parse("180 * degrees").unwrap();
        let resolved = resolve::resolve(root, &reg).unwrap();
        // Should be Mul(Lit(180), Lit(1 degree)), not Mul(..., LitSymbol("degrees"))
        let (l, r) = match &resolved {
            ExprDef::Mul(a, b) => (a.as_ref(), b.as_ref()),
            _ => panic!("expected Mul, got {resolved:?}"),
        };
        assert!(!matches!(l, ExprDef::LitSymbol(_)), "left should be Lit(180), got {l:?}");
        assert!(!matches!(r, ExprDef::LitSymbol(_)), "\"degrees\" must resolve as unit, got {r:?}");
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
            ExprDef::Call(_, args) => match args.first() {
                Some(CallArg::Positional(e)) => e.as_ref(),
                _ => panic!("expected one positional arg"),
            },
            _ => panic!("expected Call, got {simplified:?}"),
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
            value(&db, root).unwrap().to_quantity(&sym).unwrap().value(),
            3.0
        );
        let parsed2 = parse("10 + 2").unwrap();
        let resolved2 = resolve::resolve(parsed2, &default_si_registry()).unwrap();
        let program_def2 = ProgramDef::new(&db, resolved2);
        let root2 = program(&db, program_def2);
        assert_eq!(
            value(&db, root2).unwrap().to_quantity(&sym).unwrap().value(),
            12.0
        );
    }
}
