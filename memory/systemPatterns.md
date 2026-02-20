# System patterns

- **Parsing:** LALRPOP grammar in `crates/snaq-lite-lang/src/expr.lalrpop`; generated parser wired via `lalrpop_mod!(...)` in `parser.rs`. Build script `build.rs` runs `lalrpop::process_src()`. Float literals use conventional syntax; fallible actions (=>?) so invalid/overflow yields a parse error. Precedence: Expr (+, -) ← Term (*, /) ← Factor (literal, parentheses).
- **IR:** `ExprDef` / `ExprData`: `Lit(OrderedFloat<f64>)`, `Add`, `Sub`, `Mul`, `Div`. No separate inputs for variables; evaluation is expression-only.
- **Errors:** LALRPOP `ParseError` is mapped to `crate::error::ParseError` in the parser wrapper. Generated code has targeted `#[allow(...)]` for Clippy.
