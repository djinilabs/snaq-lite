//! snaq-lite: reactive arithmetic language (Salsa-based).

pub mod error;
pub mod ir;
pub mod parser;
pub mod queries;

pub use error::{ParseError, RunError};
pub use ir::{ExprDef, Expression, Numbers, ProgramDef};
pub use parser::parse;
pub use queries::{program, value};

/// Parse the expression string, run it with the two number arguments, and return the result.
///
/// The computation is reactive (Salsa): changing inputs would invalidate only dependent nodes.
/// This function creates a fresh database each call; for incremental updates, construct the
/// database and inputs yourself and use [`program`] and [`value`].
pub fn run(input: &str, a: i64, b: i64) -> Result<i64, RunError> {
    let root_def = parse(input).map_err(RunError::from)?;
    let db = salsa::DatabaseImpl::new();
    let numbers = Numbers::new(&db, a, b);
    let program_def = ProgramDef::new(&db, root_def);
    let root = program(&db, program_def);
    let result = value(&db, numbers, root);
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::ExprDef;
    use salsa::Setter;

    #[test]
    fn parse_lit_a() {
        assert_eq!(parse("a").unwrap(), ExprDef::LitA);
    }

    #[test]
    fn parse_lit_b() {
        assert_eq!(parse("b").unwrap(), ExprDef::LitB);
    }

    #[test]
    fn parse_add() {
        assert_eq!(
            parse("a + b").unwrap(),
            ExprDef::Add(Box::new(ExprDef::LitA), Box::new(ExprDef::LitB))
        );
    }

    #[test]
    fn parse_sub() {
        assert_eq!(
            parse("a - b").unwrap(),
            ExprDef::Sub(Box::new(ExprDef::LitA), Box::new(ExprDef::LitB))
        );
    }

    #[test]
    fn parse_with_parens() {
        assert_eq!(
            parse("(a + b) - a").unwrap(),
            ExprDef::Sub(
                Box::new(ExprDef::Add(
                    Box::new(ExprDef::LitA),
                    Box::new(ExprDef::LitB)
                )),
                Box::new(ExprDef::LitA)
            )
        );
    }

    #[test]
    fn eval_lit_a() {
        assert_eq!(run("a", 1, 2).unwrap(), 1);
    }

    #[test]
    fn eval_lit_b() {
        assert_eq!(run("b", 1, 2).unwrap(), 2);
    }

    #[test]
    fn eval_add() {
        assert_eq!(run("a + b", 1, 2).unwrap(), 3);
    }

    #[test]
    fn eval_sub() {
        assert_eq!(run("a - b", 1, 2).unwrap(), -1);
    }

    #[test]
    fn eval_parens() {
        assert_eq!(run("(a + b) - a", 1, 2).unwrap(), 2);
    }

    #[test]
    fn parse_empty_is_error() {
        assert!(parse("").is_err());
        assert!(parse("   ").is_err());
    }

    #[test]
    fn parse_invalid_char_is_error() {
        assert!(parse("!").is_err());
        assert!(parse("a + *").is_err());
    }

    #[test]
    fn run_parse_error_returns_err() {
        assert!(run("a +", 1, 2).is_err());
        assert!(run("", 1, 2).is_err());
    }

    #[test]
    fn reactivity_when_number_changes_value_updates() {
        let mut db = salsa::DatabaseImpl::new();
        let numbers = Numbers::new(&db, 1, 2);
        let program_def = ProgramDef::new(&db, parse("a + b").unwrap());
        let root = program(&db, program_def);
        assert_eq!(value(&db, numbers, root), 3);
        numbers.set_a(&mut db).to(10);
        let root = program(&db, program_def);
        assert_eq!(value(&db, numbers, root), 12);
    }
}
