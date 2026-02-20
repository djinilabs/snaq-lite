//! snaq-lite: reactive arithmetic language (Salsa-based).

pub mod error;
pub mod ir;
pub mod parser;
pub mod queries;

pub use error::{ParseError, RunError};
pub use ir::{ExprDef, Expression, ProgramDef};
pub use parser::parse;
pub use queries::{program, value};

/// Parse the expression string and evaluate it.
///
/// Supports float literals (conventional syntax), `+`, `-`, `*`, `/`, and parentheses.
/// Multiplication and division bind tighter than addition and subtraction; `*` and `/` are
/// left-associative. Invalid literals or overflow are reported as a parse error.
/// The computation is reactive (Salsa): changing inputs would invalidate only dependent nodes.
/// This function creates a fresh database each call; for incremental updates, construct the
/// database and inputs yourself and use [`program`] and [`value`].
pub fn run(input: &str) -> Result<f64, RunError> {
    let root_def = parse(input).map_err(RunError::from)?;
    let db = salsa::DatabaseImpl::new();
    let program_def = ProgramDef::new(&db, root_def);
    let root = program(&db, program_def);
    let result = value(&db, root);
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::ExprDef;
    use ordered_float::OrderedFloat;

    fn lit(n: f64) -> ExprDef {
        ExprDef::Lit(OrderedFloat::from(n))
    }

    #[test]
    fn parse_lit() {
        assert_eq!(parse("1").unwrap(), lit(1.0));
        assert_eq!(parse("42").unwrap(), lit(42.0));
        assert_eq!(parse("0").unwrap(), lit(0.0));
        assert_eq!(parse("1.5").unwrap(), lit(1.5));
        assert_eq!(parse(".5").unwrap(), lit(0.5));
        assert_eq!(parse("2e1").unwrap(), lit(20.0));
        assert_eq!(
            parse("9223372036854775807").unwrap(),
            lit(9223372036854775807.0)
        );
    }

    #[test]
    fn parse_add() {
        assert_eq!(
            parse("1 + 2").unwrap(),
            ExprDef::Add(Box::new(lit(1.0)), Box::new(lit(2.0)))
        );
    }

    #[test]
    fn parse_sub() {
        assert_eq!(
            parse("1 - 2").unwrap(),
            ExprDef::Sub(Box::new(lit(1.0)), Box::new(lit(2.0)))
        );
    }

    #[test]
    fn parse_mul() {
        assert_eq!(
            parse("2 * 3").unwrap(),
            ExprDef::Mul(Box::new(lit(2.0)), Box::new(lit(3.0)))
        );
    }

    #[test]
    fn parse_div() {
        assert_eq!(
            parse("6 / 2").unwrap(),
            ExprDef::Div(Box::new(lit(6.0)), Box::new(lit(2.0)))
        );
    }

    #[test]
    fn parse_with_parens() {
        assert_eq!(
            parse("(1 + 2) - 1").unwrap(),
            ExprDef::Sub(
                Box::new(ExprDef::Add(Box::new(lit(1.0)), Box::new(lit(2.0)))),
                Box::new(lit(1.0))
            )
        );
    }

    #[test]
    fn parse_precedence_mul_tighter_than_add() {
        // 1 + 2 * 3 must parse as Add(1, Mul(2, 3)), not Mul(Add(1,2), 3)
        assert_eq!(
            parse("1 + 2 * 3").unwrap(),
            ExprDef::Add(
                Box::new(lit(1.0)),
                Box::new(ExprDef::Mul(Box::new(lit(2.0)), Box::new(lit(3.0))))
            )
        );
    }

    #[test]
    fn parse_precedence_div_tighter_than_sub() {
        // 6 - 4 / 2 must parse as Sub(6, Div(4, 2))
        assert_eq!(
            parse("6 - 4 / 2").unwrap(),
            ExprDef::Sub(
                Box::new(lit(6.0)),
                Box::new(ExprDef::Div(Box::new(lit(4.0)), Box::new(lit(2.0))))
            )
        );
    }

    #[test]
    fn parse_precedence_parens_override() {
        // (1 + 2) * 3 must parse as Mul(Add(1,2), 3)
        assert_eq!(
            parse("(1 + 2) * 3").unwrap(),
            ExprDef::Mul(
                Box::new(ExprDef::Add(Box::new(lit(1.0)), Box::new(lit(2.0)))),
                Box::new(lit(3.0))
            )
        );
    }

    #[test]
    fn eval_lit() {
        assert_eq!(run("1").unwrap(), 1.0);
        assert_eq!(run("42").unwrap(), 42.0);
        assert_eq!(run("1.5").unwrap(), 1.5);
    }

    #[test]
    fn eval_add() {
        assert_eq!(run("1 + 2").unwrap(), 3.0);
    }

    #[test]
    fn eval_sub() {
        assert_eq!(run("1 - 2").unwrap(), -1.0);
    }

    #[test]
    fn eval_mul() {
        assert_eq!(run("2 * 3").unwrap(), 6.0);
    }

    #[test]
    fn eval_div() {
        assert_eq!(run("6 / 2").unwrap(), 3.0);
    }

    #[test]
    fn eval_parens() {
        assert_eq!(run("(1 + 2) - 1").unwrap(), 2.0);
    }

    #[test]
    fn eval_precedence_mul_tighter_than_add() {
        assert_eq!(run("1 + 2 * 3").unwrap(), 7.0);
    }

    #[test]
    fn eval_precedence_div_tighter_than_sub() {
        assert_eq!(run("6 - 4 / 2").unwrap(), 4.0);
    }

    #[test]
    fn eval_precedence_mul_div_left_to_right() {
        assert_eq!(run("8 / 4 / 2").unwrap(), 1.0);
        assert_eq!(run("2 * 3 * 4").unwrap(), 24.0);
    }

    #[test]
    fn eval_precedence_parens_override() {
        assert_eq!(run("(1 + 2) * 3").unwrap(), 9.0);
        assert_eq!(run("6 / (1 + 1)").unwrap(), 3.0);
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
    fn parse_invalid_float_is_error() {
        assert!(parse("1.2.3").is_err());
        assert!(parse("e10").is_err());
    }

    #[test]
    fn run_parse_error_returns_err() {
        assert!(run("1 +").is_err());
        assert!(run("").is_err());
    }

    #[test]
    fn reactivity_when_program_changes_value_updates() {
        let db = salsa::DatabaseImpl::new();
        let program_def = ProgramDef::new(&db, parse("1 + 2").unwrap());
        let root = program(&db, program_def);
        assert_eq!(value(&db, root), 3.0);
        let program_def2 = ProgramDef::new(&db, parse("10 + 2").unwrap());
        let root2 = program(&db, program_def2);
        assert_eq!(value(&db, root2), 12.0);
    }
}
