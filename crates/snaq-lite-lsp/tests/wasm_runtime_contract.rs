//! Tier A (plan): minimal WASM contract for [`snaq_lite_lsp::runtime_engine`] without JSON-RPC.
#![cfg(target_arch = "wasm32")]

use wasm_bindgen_test::*;

#[wasm_bindgen_test]
async fn wasm_runtime_engine_ping_round_trip() {
    let rt = snaq_lite_lsp::runtime_engine::RuntimeEngine::spawn();
    rt.ping().await;
}
