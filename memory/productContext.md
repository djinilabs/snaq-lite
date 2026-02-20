# Product context

- **Goal:** Reactive arithmetic language (Salsa-based); runs natively or via WASM.
- **Language (current):** Integer literals and `+` / `-` with parentheses. No bindings or variables.
- **API:** `run(expression: &str) -> Result<i64, RunError>`.
