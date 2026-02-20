# System patterns

- **Parsing:** LALRPOP grammar in `crates/snaq-lite-lang/src/expr.lalrpop`; generated parser wired via `lalrpop_mod!(...)` in `parser.rs`. Build script `build.rs` runs `lalrpop::process_src()`. Float literals use conventional syntax; fallible actions (=>?) so invalid/overflow yields a parse error. Precedence: Expr (+, -) ← Term (*, /) ← Factor (literal, parentheses).
- **IR:** `ExprDef` has parse-time variants `LitScalar`, `LitWithUnit`, `LitUnit` and resolved `Lit(Quantity)`; binary `Add`, `Sub`, `Mul`, `Div`. Two-step flow: parse → resolve (with unit registry) → `ExprDef` with only `Lit(Quantity)` for literals. `ExprData` / evaluation use `Lit(Quantity)`; `value()` returns `Result<Quantity, RunError>`.
- **Units:** Default registry (`default_si_registry`) provides SI base (m, s, kg) + derived (km, hour, minute, mile, au, parsec, light_year, joule, eV). Prefix resolution via `get_unit_with_prefix` (e.g. km, mm). Quantity has `full_simplify` and `full_simplify_with_registry`.
- **Errors:** LALRPOP `ParseError` is mapped to `crate::error::ParseError` in the parser wrapper. Generated code has targeted `#[allow(...)]` for Clippy.
