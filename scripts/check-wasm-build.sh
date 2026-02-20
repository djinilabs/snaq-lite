#!/usr/bin/env bash
# Check that the WASM crate builds for wasm32-unknown-unknown and produces a .wasm artifact.
# Run from repo root. Requires: rustup target add wasm32-unknown-unknown

set -e

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

echo "[INFO] Building snaq-lite-wasm for wasm32-unknown-unknown..."
cargo build -p snaq-lite-wasm --target wasm32-unknown-unknown

WASM_ARTIFACT="$REPO_ROOT/target/wasm32-unknown-unknown/debug/snaq_lite_wasm.wasm"
if [[ ! -f "$WASM_ARTIFACT" ]]; then
    echo "[ERROR] Expected .wasm artifact not found: $WASM_ARTIFACT" >&2
    exit 1
fi

echo "[OK] WASM build succeeded: $WASM_ARTIFACT"
