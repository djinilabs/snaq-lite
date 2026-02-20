use wasm_bindgen::prelude::*;
use snaq_lite_lang::run;

#[wasm_bindgen]
pub fn evaluate(input: &str) -> String {
    run(input)
        .map(|n| n.to_string())
        .unwrap_or_else(|e| e.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use wasm_bindgen_test::*;

    #[wasm_bindgen_test]
    fn evaluate_simple_add() {
        assert_eq!(evaluate("1 + 2"), "3");
    }

    #[wasm_bindgen_test]
    fn evaluate_mul_and_parens() {
        assert_eq!(evaluate("2 * (10 - 3)"), "14");
    }

    #[wasm_bindgen_test]
    fn evaluate_float_and_precedence() {
        assert_eq!(evaluate("1.5 * 2 + 1"), "4");
    }

    #[wasm_bindgen_test]
    fn evaluate_error_returns_parse_error_message() {
        let out = evaluate("1 + ");
        assert!(out.starts_with("parse error: "), "expected parse error, got: {out}");
    }
}
