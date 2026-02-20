//! snaq-lite: reactive arithmetic language (Salsa-based).

pub mod dimension;
pub mod error;
pub mod ir;
pub mod parser;
pub mod prefix;
pub mod quantity;
pub mod queries;
pub mod resolve;
pub mod unit;
pub mod unit_registry;

pub use error::{ParseError, RunError};
pub use quantity::{Quantity, QuantityError, SnaqNumber};
pub use unit::Unit;
pub use ir::{ExprDef, Expression, ProgramDef};
pub use parser::parse;
pub use queries::{program, set_eval_registry, value};
pub use unit_registry::{default_si_registry, UnitRegistry};

/// Parse the expression string and evaluate it, returning a Quantity (value + unit).
///
/// Supports float literals, quantity literals (e.g. `100 m`, `1.5 * km`), unit-as-factor (e.g. `hour`),
/// implicit multiplication when the next token is a number or parenthesized expression (e.g. `10 20` → 200, `2 (3+4)` → 14).
/// Division can be written as `/` or `per` (e.g. `3 kilometers per hour`).
/// Uses the default registry: all 7 SI base units (m, kg, s, A, K, mol, cd), SI derived (J, C, V, F, ohm, S, Wb, T, H, Hz, N, Pa, W, lm, lx, Bq, Gy, Sv, kat), time/length (km, hour, minute, second, seconds), plus mile, au, parsec, light_year, joule, eV, celsius.
/// Errors on parse failure, unknown unit, dimension mismatch (add/sub), or division by zero.
pub fn run(input: &str) -> Result<Quantity, RunError> {
    run_with_registry(input, &default_si_registry())
}

/// Like [run], but with a custom unit registry (e.g. for custom units or tests).
pub fn run_with_registry(input: &str, registry: &UnitRegistry) -> Result<Quantity, RunError> {
    let root_def = parse(input).map_err(RunError::from)?;
    let root_def = resolve::resolve(root_def, registry)?;
    set_eval_registry(registry.clone());
    let db = salsa::DatabaseImpl::new();
    let program_def = ProgramDef::new(&db, root_def);
    let root = program(&db, program_def);
    value(&db, root)
}

/// Evaluate and return the numeric value only if the result is dimensionless (scalar).
/// Use this when you expect a plain number (e.g. `"1 + 2"` → `3.0`); errors if the result has a unit.
pub fn run_scalar(input: &str) -> Result<f64, RunError> {
    let q = run(input)?;
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
    use crate::ir::ExprDef;
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
            ExprDef::LitWithUnit(OrderedFloat::from(1.0), "percent".to_string())
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
        assert_eq!(
            parse("100 m").unwrap(),
            ExprDef::LitWithUnit(OrderedFloat::from(100.0), "m".to_string())
        );
        // "10 m" is one quantity literal, not implicit mul 10 * m
        assert_eq!(
            parse("10 m").unwrap(),
            ExprDef::LitWithUnit(OrderedFloat::from(10.0), "m".to_string())
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
    fn eval_lit() {
        assert_eq!(run_scalar("1").unwrap(), 1.0);
        assert_eq!(run_scalar("42").unwrap(), 42.0);
        assert_eq!(run_scalar("1.5").unwrap(), 1.5);
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
        let q = run("1.5 km + 500 m").unwrap();
        assert!((q.value() - 2000.0).abs() < 1e-10);
        assert_eq!(q.unit().iter().next().unwrap().unit_name, "m");
    }

    #[test]
    fn eval_implicit_mul_with_units() {
        let q = run("10 m 2").unwrap();
        assert!((q.value() - 20.0).abs() < 1e-10);
        assert_eq!(q.unit().iter().next().unwrap().unit_name, "m");
    }

    #[test]
    fn eval_compound_unit() {
        let q = run("10 m / 2 s").unwrap();
        assert!((q.value() - 5.0).abs() < 1e-10);
        let factors: Vec<_> = q.unit().iter().collect();
        assert_eq!(factors.len(), 2);
    }

    #[test]
    fn parse_implicit_mul_rhs_not_ident() {
        // Implicit mul RHS is only number or (expr); "2 3 m" has no operator between 3 and m, so parse error
        assert!(parse("2 3 m").is_err());
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
    fn run_unknown_unit_returns_err() {
        assert!(run("1 foo").is_err());
        assert!(run("bar").is_err());
    }

    #[test]
    fn run_division_by_zero_returns_err() {
        let e = run("1 / 0").unwrap_err();
        assert!(matches!(e, RunError::DivisionByZero));
        let e = run("3 m / 0 s").unwrap_err();
        assert!(matches!(e, RunError::DivisionByZero));
    }

    #[test]
    fn run_dimension_mismatch_returns_err() {
        let e = run("1 m + 1 s").unwrap_err();
        assert!(matches!(e, RunError::DimensionMismatch { .. }));
    }

    /// Adding or subtracting quantities with *different units* but the *same dimension* is supported:
    /// both are converted to the smaller unit and the result is in that unit.
    #[test]
    fn add_same_dimension_different_units_length() {
        let q = run("1 km + 500 m").unwrap();
        assert!((q.value() - 1500.0).abs() < 1e-6, "1 km + 500 m = 1500 m");
        assert_eq!(q.unit().iter().next().unwrap().unit_name, "m");

        let q2 = run("500 m + 1 km").unwrap();
        assert!((q2.value() - 1500.0).abs() < 1e-6, "commutativity: 500 m + 1 km = 1500 m");
        assert_eq!(q2.unit().iter().next().unwrap().unit_name, "m");

        let q3 = run("1 mile + 1 km").unwrap();
        assert!((q3.value() - 2.609_344).abs() < 1e-3, "1 mile + 1 km = 2.609344 km (result in smaller unit)");
        assert_eq!(q3.unit().iter().next().unwrap().unit_name, "km");
    }

    #[test]
    fn add_same_dimension_different_units_time() {
        let q = run("1 hour + 30 minute").unwrap();
        assert!((q.value() - 90.0).abs() < 1e-6, "1 h + 30 min = 90 min (result in smaller unit)");
        assert_eq!(q.unit().iter().next().unwrap().unit_name, "minute");

        let q2 = run("60 minute + 1 hour").unwrap();
        assert!((q2.value() - 120.0).abs() < 1e-6, "60 min + 1 h = 120 min");
        assert_eq!(q2.unit().iter().next().unwrap().unit_name, "minute");
    }

    #[test]
    fn second_and_seconds_recognized_as_time_units() {
        let q = run("1 second").unwrap();
        assert!((q.value() - 1.0).abs() < 1e-10);
        assert_eq!(q.unit().iter().next().unwrap().unit_name, "second");

        let q2 = run("5 seconds").unwrap();
        assert!((q2.value() - 5.0).abs() < 1e-10);
        assert_eq!(q2.unit().iter().next().unwrap().unit_name, "seconds");

        let q3 = run("1 minute + 30 seconds").unwrap();
        assert!((q3.value() - 90.0).abs() < 1e-6, "1 min + 30 s = 90 s");
        assert_eq!(q3.unit().iter().next().unwrap().unit_name, "seconds");
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
            let q = run(expr).unwrap();
            assert!((q.value() - 1.0).abs() < 1e-10, "{}", expr);
            assert_eq!(q.unit().iter().next().unwrap().unit_name, unit_name, "{}", expr);
        }
    }

    #[test]
    fn add_same_dimension_different_units_mass() {
        let q = run("1 kg + 500 g").unwrap();
        assert!((q.value() - 1500.0).abs() < 1e-6, "1 kg + 500 g = 1500 g (smaller unit)");
        assert_eq!(q.unit().iter().next().unwrap().unit_name, "g");
    }

    #[test]
    fn sub_same_dimension_different_units() {
        let q = run("1 km - 300 m").unwrap();
        assert!((q.value() - 700.0).abs() < 1e-6, "1 km - 300 m = 700 m");
        assert_eq!(q.unit().iter().next().unwrap().unit_name, "m");

        let q2 = run("1 hour - 15 minute").unwrap();
        assert!((q2.value() - 45.0).abs() < 1e-6, "1 h - 15 min = 45 min");
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
        let q_mile = run("1 mile").unwrap();
        assert!((q_mile.value() - 1.0).abs() < 1e-10);
        assert_eq!(q_mile.unit().iter().next().unwrap().unit_name, "mile");
        let q_parsec = run("1 parsec").unwrap();
        assert!((q_parsec.value() - 1.0).abs() < 1e-10);
        let q_ev = run("1 eV").unwrap();
        assert!((q_ev.value() - 1.0).abs() < 1e-10);
    }

    #[test]
    fn run_long_form_units_kilometers() {
        let q = run("32 kilometers").unwrap();
        assert!((q.value() - 32.0).abs() < 1e-10);
        assert_eq!(q.unit().iter().next().unwrap().unit_name, "kilometers");
    }

    #[test]
    fn run_numbat_parity_compound_velocity() {
        let q = run("100 km / hour").unwrap();
        assert!((q.value() - 100.0).abs() < 1e-10);
        let factors: Vec<_> = q.unit().iter().collect();
        assert_eq!(factors.len(), 2);
    }

    #[test]
    fn run_per_alias_for_division() {
        let q_slash = run("3 kilometers / hour").unwrap();
        let q_per = run("3 kilometers per hour").unwrap();
        assert!((q_slash.value() - q_per.value()).abs() < 1e-10);
        assert_eq!(q_slash.unit(), q_per.unit());
        assert!((q_per.value() - 3.0).abs() < 1e-10);
    }

    #[test]
    fn reactivity_when_program_changes_value_updates() {
        let registry = default_si_registry();
        set_eval_registry(registry);
        let db = salsa::DatabaseImpl::new();
        let parsed = parse("1 + 2").unwrap();
        let resolved = resolve::resolve(parsed, &crate::unit_registry::default_si_registry()).unwrap();
        let program_def = ProgramDef::new(&db, resolved);
        let root = program(&db, program_def);
        assert_eq!(value(&db, root).unwrap().value(), 3.0);
        let parsed2 = parse("10 + 2").unwrap();
        let resolved2 = resolve::resolve(parsed2, &crate::unit_registry::default_si_registry()).unwrap();
        let program_def2 = ProgramDef::new(&db, resolved2);
        let root2 = program(&db, program_def2);
        assert_eq!(value(&db, root2).unwrap().value(), 12.0);
    }
}
