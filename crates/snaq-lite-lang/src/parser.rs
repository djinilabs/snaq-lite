//! Parser: expression string → `ExprDef`.
//! Uses LALRPOP-generated grammar with custom lexer (Ident vs FuncIdent for calls).

use crate::error::ParseError;
use crate::ir::ExprDef;
use crate::lexer;
use lalrpop_util::lalrpop_mod;

lalrpop_mod!(
    #[allow(clippy::ptr_arg)]
    #[allow(clippy::empty_line_after_outer_attr)]
    #[allow(clippy::uninlined_format_args)]
    #[allow(clippy::type_complexity)]
    #[allow(dead_code)]
    #[allow(unused_imports)] // generated code imports Tok; type is used via full path in extern enum
    expr
);

/// Parse a single expression. Uses custom lexer so "sin(1)" is a call and "sin" is a symbol.
pub fn parse(input: &str) -> Result<ExprDef, ParseError> {
    let lexer = lexer::Lexer::new(input);
    expr::ExprParser::new()
        .parse(lexer)
        .map_err(|e| ParseError::new(format!("{e:?}")))
}
