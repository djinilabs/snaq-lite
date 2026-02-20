# Active context

## Just completed
- **GitHub CI workflow:** Added `.github/workflows/ci.yml` that runs on push/PR to main/master: checkout, Rust stable + clippy (from toolchain), wasm32 target, wasm-pack, Node LTS, Swatinem/rust-cache, then `cargo test --workspace`, `cargo clippy --workspace -- -D warnings`, and `wasm-pack test --node crates/snaq-lite-wasm`.

- **WASM generation and runtime tests:** (1) Added `wasm-bindgen-test` dev-dependency and four `#[wasm_bindgen_test]` tests in snaq-lite-wasm (evaluate success: simple add, mul+parens, float+precedence; error: parse error message). Runtime tests run with `wasm-pack test --node crates/snaq-lite-wasm`. (2) README documents WASM test commands (generation: `cargo build -p snaq-lite-wasm --target wasm32-unknown-unknown` or `./scripts/check-wasm-build.sh`; runtime: wasm-pack test). (3) `scripts/check-wasm-build.sh` builds for wasm32 and asserts the .wasm artifact exists.

## Next steps
- None specified.
