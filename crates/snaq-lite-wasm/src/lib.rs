mod host;

use js_sys::{Array, Object};
use wasm_bindgen::prelude::*;
use snaq_lite_lang::{run, run_numeric};

#[wasm_bindgen]
pub fn evaluate(input: &str) -> String {
    run(input)
        .map(|v| v.to_string())
        .unwrap_or_else(|e| e.to_string())
}

#[wasm_bindgen]
pub fn evaluate_numeric(input: &str) -> String {
    run_numeric(input)
        .map(|q| q.to_string())
        .unwrap_or_else(|e| e.to_string())
}

/// Create a new stream input. Returns a stream index (u32) to use in runWithStreamInputs
/// (as value in the stream_input_map) and in pushChunk / closeStream.
#[wasm_bindgen(js_name = createStreamInput)]
pub fn create_stream_input_js() -> u32 {
    host::create_stream_input_host()
}

/// Run script with external stream inputs. stream_input_map is a JS object mapping
/// stream names (e.g. "data") to stream indices returned by createStreamInput.
/// Returns { runIndex, isVector }. Use runIndex in consumeOutputStream.
#[wasm_bindgen(js_name = runWithStreamInputs)]
pub fn run_with_stream_inputs_js(
    script: &str,
    stream_input_map: &Object,
) -> Result<JsValue, JsValue> {
    let result = host::run_with_stream_inputs_host(script, stream_input_map)?;
    let obj = Object::new();
    js_sys::Reflect::set(&obj, &JsValue::from_str("runIndex"), &JsValue::from(result.run_index))?;
    js_sys::Reflect::set(&obj, &JsValue::from_str("isVector"), &JsValue::from(result.is_vector))?;
    Ok(obj.into())
}

/// Push a chunk of values to a stream. chunk is a JS array of numbers (or null for sparse).
/// Converts to scalar dimensionless values (variance 0).
#[wasm_bindgen(js_name = pushChunk)]
pub fn push_chunk_js(stream_index: u32, chunk: &Array) -> Result<(), JsValue> {
    host::push_chunk_host(stream_index, chunk)
}

/// Signal end-of-stream for a stream. After this, pushChunk for this index will fail.
#[wasm_bindgen(js_name = closeStream)]
pub fn close_stream_js(stream_index: u32) -> Result<(), JsValue> {
    host::close_stream_host(stream_index)
}

/// Start a feeder that reads from a JS ReadableStream (e.g. response.body or file.stream()),
/// parses newline-delimited numbers, and pushes chunks to the stream. Yields to the event loop
/// periodically. Closes the stream when the ReadableStream ends.
#[wasm_bindgen(js_name = startFeeder)]
pub fn start_feeder_js(stream_index: u32, readable_stream: JsValue) -> Result<(), JsValue> {
    host::start_feeder_host(stream_index, readable_stream)
}

/// Consume the output stream from a run (runIndex from runWithStreamInputs). Callbacks:
/// - onChunk(element): called for each element (number, null for sparse, or object for uncertain).
/// - onDone(): called when the stream ends.
/// - onError(message): called on error or if run result already consumed / not a vector.
/// Yields to the event loop every 16 elements so the UI stays responsive.
#[wasm_bindgen(js_name = consumeOutputStream)]
pub fn consume_output_stream_js(
    run_index: u32,
    on_chunk: &js_sys::Function,
    on_done: &js_sys::Function,
    on_error: &js_sys::Function,
) -> Result<(), JsValue> {
    host::consume_output_stream_host(run_index, on_chunk, on_done, on_error)
}

#[cfg(test)]
mod tests {
    use super::*;
    use wasm_bindgen_test::*;

    #[wasm_bindgen_test]
    fn create_stream_input_returns_number() {
        let idx = create_stream_input_js();
        assert!(idx <= u32::MAX as u32);
    }

    #[wasm_bindgen_test]
    fn run_with_stream_inputs_scalar_returns_run_index_and_is_vector_false() {
        let empty = Object::new();
        let result = run_with_stream_inputs_js("1 + 1", &empty).unwrap();
        let run_index = js_sys::Reflect::get(&result, &JsValue::from_str("runIndex")).unwrap();
        assert!(run_index.as_f64().is_some(), "runIndex should be a number");
        let is_vector = js_sys::Reflect::get(&result, &JsValue::from_str("isVector")).unwrap();
        assert_eq!(is_vector.as_bool(), Some(false), "1+1 is scalar, isVector should be false");
    }

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
        assert!(
            out.starts_with("parse error: ") || out.starts_with("parse error at "),
            "expected parse error, got: {out}"
        );
    }
}
