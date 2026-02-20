//! Parser: expression string → `ExprDef`.
//! Uses LALRPOP-generated grammar (integer literals, +, -, parentheses).

use crate::error::ParseError;
use crate::ir::ExprDef;
use lalrpop_util::lalrpop_mod;

lalrpop_mod!(
    #[allow(clippy::ptr_arg)]
    #[allow(clippy::empty_line_after_outer_attr)]
    #[allow(clippy::uninlined_format_args)]
    #[allow(clippy::type_complexity)]
    #[allow(dead_code)]
    expr
);

/// Parse a single expression. Leading/trailing whitespace is skipped by the grammar.
pub fn parse(input: &str) -> Result<ExprDef, ParseError> {
    expr::ExprParser::new()
        .parse(input)
        .map_err(|e| ParseError::new(format!("{e}")))
}
