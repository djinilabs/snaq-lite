# Product context

- **Goal:** Reactive arithmetic language (Salsa-based); runs natively or via WASM.
- **Language (current):** Float literals (conventional syntax), `+`, `-`, `*`, `/`, and parentheses. No bindings or variables. Precedence: `*` and `/` tighter than `+` and `-`.
- **API:** `run(expression: &str) -> Result<f64, RunError>`.
