# CLI file-format integration tests

## Overview

Add a comprehensive suite of CLI integration tests that run the snaq-lite binary with `--stream` against all supported file types (numeric .txt, CSV, and Parquet/Arrow), varying file sizes and internal shapes, and assert correct stdout and exit codes. **Parquet and Arrow tests must run both locally and on CI.**

---

## When a test fails: fix implementation, not the test

**Rule:** If a test fails and the test correctly reflects the expected behavior—from the language design, the implementation’s intended behavior, and what a user would reasonably expect—then **fix the implementation**, not the test.

- Treat test assertions as the specification: they encode the desired behavior (e.g. empty file → `[]`, CSV column access, error messages, exit codes).
- Do **not** relax or change assertions (e.g. accept wrong output, or remove a check) just to make the test pass when the current implementation is wrong.
- Only change a test when the test itself is wrong: e.g. typo in expected string, wrong language semantics, or the intended behavior has been explicitly revised (in which case update both docs and test).

This applies to both writing new tests and debugging failures during or after implementation.

---

## Parquet and Arrow: run locally and on CI

**Requirement:** Parquet and Arrow CLI integration tests must execute when developers run the standard test command locally and when CI runs.

**Approach (choose one):**

### Option A — Parquet as default feature for CLI (recommended)

- In [crates/snaq-lite-cli/Cargo.toml](crates/snaq-lite-cli/Cargo.toml): set `default = ["parquet"]` in `[features]`.
- **CI:** No change. The existing step `cargo test --workspace` builds each crate with its default features, so `snaq-lite-cli` is built with `parquet` and all CLI tests (including Parquet/Arrow) run.
- **Local:** `cargo test` and `cargo test --workspace` (and the command in .cursorrules) already run workspace tests; the CLI will use default features and Parquet/Arrow tests will run.
- **Trade-off:** Default CLI build gets arrow/parquet dependencies (heavier). Acceptable if the project wants a single test command and full coverage by default.

### Option B — Explicit Parquet test step

- Keep `default = []` for `snaq-lite-cli`.
- **CI:** Add a step after "Run tests" in [.github/workflows/test.yml](.github/workflows/test.yml):
  ```yaml
  - name: Run CLI tests with Parquet/Arrow
    run: cargo test -p snaq-lite-cli --features parquet
  ```
- **Local:** Update `.cursorrules` so the required check includes Parquet CLI tests, e.g.:
  ```text
  cargo test && cargo test -p snaq-lite-cli --features parquet && cargo clippy --workspace && wasm-pack test --node crates/snaq-lite-wasm
  ```
- **Trade-off:** Two test invocations; default CLI build stays light.

**Implementation:** When writing the integration tests, use **Option A** (default = ["parquet"]) so that a single `cargo test --workspace` in CI and locally runs all tests. If the project later prefers a lighter default CLI build, switch to Option B and add the CI step and .cursorrules line above.

---

## Rest of the plan (summary)

- **Test file:** New `crates/snaq-lite-cli/tests/cli_file_formats_integration.rs` with shared helper (e.g. `run_cli(args)`, `cli_bin()`), unique temp paths, and cleanup.
- **Numeric (.txt):** Empty file → `[]`; single value; multiple values `$x * 2` → `[2,4,6]`; blank lines skipped; large file (chunking); `--numeric` one-per-line.
- **CSV:** Headers-only → `[]`; single/multi row; multiple columns; empty cell → `?`; many rows (chunking); `--numeric`.
- **Parquet/Arrow:** `#[cfg(feature = "parquet")]` tests; optional dev-dependencies (arrow, arrow-ipc, parquet) enabled by parquet feature; write temp .parquet/.arrow via Arrow RecordBatch + writers; run CLI `--stream p=<path>` and assert stdout.
- **Errors:** File not found; invalid numeric line; optional invalid CSV cell.
- **Non-stream:** `snaq-lite "1 + 2"` → `3`; `--numeric`; parse error → non-zero exit.
- **Cargo.toml:** Optional dev-dependencies for parquet feature (so tests that write Arrow/Parquet compile when feature is on). If using Option A, parquet is default so those deps are always built for the CLI when testing.
