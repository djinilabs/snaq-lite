use wasm_bindgen::prelude::*;
use snaq_lite_lang::run;

#[wasm_bindgen]
pub fn evaluate(input: &str, a: i32, b: i32) -> String {
    run(input, a as i64, b as i64)
        .map(|n| n.to_string())
        .unwrap_or_else(|e| e.to_string())
}
