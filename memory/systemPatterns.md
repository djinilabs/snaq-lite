# System patterns

- **Parsing:** LALRPOP grammar in `crates/snaq-lite-lang/src/expr.lalrpop`; generated parser wired via `lalrpop_mod!(...)` in `parser.rs`. Build script `build.rs` runs `lalrpop::process_src()`. Number literals use fallible actions (=>?) so overflow yields a parse error, not a panic.
- **IR:** `ExprDef` / `ExprData`: `Lit(i64)`, `Add`, `Sub`. No separate inputs for variables; evaluation is expression-only.
- **Errors:** LALRPOP `ParseError` is mapped to `crate::error::ParseError` in the parser wrapper. Generated code has targeted `#[allow(...)]` for Clippy.
