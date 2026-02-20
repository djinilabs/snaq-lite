use wasm_bindgen::prelude::*;
use snaq_lite_lang::run;

#[wasm_bindgen]
pub fn evaluate(input: &str) -> String {
    run(input).map(|()| String::new()).unwrap_or_else(|()| "error".into())
}
