# Active context

## Just completed
- **Parser: floats, parentheses, and full arithmetic:** IR switched to `Lit(OrderedFloat<f64>)` and added `Mul`/`Div`. Grammar: float literals (conventional syntax), three-level precedence (Expr/Term/Factor), `*` and `/`. Queries: build and value for Mul/Div; `value` returns `f64`. `run()` returns `Result<f64, RunError>`. Unit tests verify precedence (mul/div tighter than add/sub, left-to-right for * and /, parentheses override).

## Next steps
- None specified.
