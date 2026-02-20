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
/// Integer literals must fit in `i64`; overflow is reported as a parse error.
/// The computation is reactive (Salsa): changing inputs would invalidate only dependent nodes.
/// This function creates a fresh database each call; for incremental updates, construct the
/// database and inputs yourself and use [`program`] and [`value`].
pub fn run(input: &str) -> Result<i64, RunError> {
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

    #[test]
    fn parse_lit() {
        assert_eq!(parse("1").unwrap(), ExprDef::Lit(1));
        assert_eq!(parse("42").unwrap(), ExprDef::Lit(42));
        assert_eq!(parse("0").unwrap(), ExprDef::Lit(0));
        assert_eq!(
            parse("9223372036854775807").unwrap(),
            ExprDef::Lit(i64::MAX)
        );
    }

    #[test]
    fn parse_add() {
        assert_eq!(
            parse("1 + 2").unwrap(),
            ExprDef::Add(Box::new(ExprDef::Lit(1)), Box::new(ExprDef::Lit(2)))
        );
    }

    #[test]
    fn parse_sub() {
        assert_eq!(
            parse("1 - 2").unwrap(),
            ExprDef::Sub(Box::new(ExprDef::Lit(1)), Box::new(ExprDef::Lit(2)))
        );
    }

    #[test]
    fn parse_with_parens() {
        assert_eq!(
            parse("(1 + 2) - 1").unwrap(),
            ExprDef::Sub(
                Box::new(ExprDef::Add(
                    Box::new(ExprDef::Lit(1)),
                    Box::new(ExprDef::Lit(2))
                )),
                Box::new(ExprDef::Lit(1))
            )
        );
    }

    #[test]
    fn eval_lit() {
        assert_eq!(run("1").unwrap(), 1);
        assert_eq!(run("42").unwrap(), 42);
    }

    #[test]
    fn eval_add() {
        assert_eq!(run("1 + 2").unwrap(), 3);
    }

    #[test]
    fn eval_sub() {
        assert_eq!(run("1 - 2").unwrap(), -1);
    }

    #[test]
    fn eval_parens() {
        assert_eq!(run("(1 + 2) - 1").unwrap(), 2);
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
    fn parse_integer_overflow_is_error() {
        // i64::MAX + 1
        assert!(parse("9223372036854775808").is_err());
        assert!(parse("99999999999999999999").is_err());
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
        assert_eq!(value(&db, root), 3);
        let program_def2 = ProgramDef::new(&db, parse("10 + 2").unwrap());
        let root2 = program(&db, program_def2);
        assert_eq!(value(&db, root2), 12);
    }
}
