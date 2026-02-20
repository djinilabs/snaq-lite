use wasm_bindgen::prelude::*;
use snaq_lite_lang::run;

#[wasm_bindgen]
pub fn evaluate(input: &str) -> String {
    run(input)
        .map(|n| n.to_string())
        .unwrap_or_else(|e| e.to_string())
}
