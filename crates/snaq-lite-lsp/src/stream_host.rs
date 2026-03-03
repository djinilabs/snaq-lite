//! WASM host API for stream indices (createStreamInput/pushChunk/closeStream/getStreamHandleId).
//! Used so the frontend can create/feed streams and the LSP can resolve external_streams for subscribeWidget.

use std::cell::RefCell;
use std::collections::HashMap;

use snaq_lite_lang::{create_stream_input, Chunk, Quantity, StreamHandleId, Value};
use wasm_bindgen::prelude::*;

thread_local! {
    /// index (u32) → (StreamHandleId, Some(Sender) until close). After close we keep (HandleId, None) so resolve_external_streams can still resolve index → handle.
    static STREAM_MAP: RefCell<HashMap<u32, (StreamHandleId, Option<futures::channel::mpsc::UnboundedSender<Chunk>>)>> = RefCell::new(HashMap::new());
    static NEXT_INDEX: RefCell<u32> = RefCell::new(0);
}

fn next_index() -> u32 {
    NEXT_INDEX.with(|r| {
        let mut n = r.borrow_mut();
        let i = *n;
        *n = n.saturating_add(1);
        i
    })
}

/// Create a new stream input. Returns stream index for pushChunk/closeStream and for externalStreams.
#[wasm_bindgen]
pub fn create_stream_input_js() -> u32 {
    let (id, sender) = create_stream_input();
    let index = next_index();
    STREAM_MAP.with(|m| {
        m.borrow_mut().insert(index, (id, Some(sender)));
    });
    index
}

/// Convert JS array of numbers to Chunk (v1: newline-delimited numbers).
fn js_array_to_chunk(arr: &js_sys::Array) -> Result<Chunk, JsValue> {
    let mut chunk = Vec::with_capacity(arr.length() as usize);
    for i in 0..arr.length() {
        let v = arr.get(i);
        if v.is_null() || v.is_undefined() {
            chunk.push(Ok(None));
        } else {
            let n = v
                .as_f64()
                .ok_or_else(|| JsValue::from_str("chunk element must be number or null"))?;
            let q = Quantity::from_scalar(n);
            chunk.push(Ok(Some(Value::Numeric(q))));
        }
    }
    Ok(chunk)
}

/// Push a chunk (JS array of numbers) to the stream. Returns error string on failure.
#[wasm_bindgen]
pub fn push_chunk_js(stream_index: u32, chunk_js: &js_sys::Array) -> Result<(), JsValue> {
    let sender = STREAM_MAP
        .with(|m| m.borrow().get(&stream_index).and_then(|(_, s)| s.as_ref()).cloned())
        .ok_or_else(|| JsValue::from_str(&format!("stream index {stream_index} not found or closed")))?;
    let chunk = js_array_to_chunk(chunk_js)?;
    sender
        .unbounded_send(chunk)
        .map_err(|_| JsValue::from_str("stream sender closed"))?;
    Ok(())
}

/// Close the stream (signal EOF). Drops the sender but keeps the handle in the map so getStreamHandleId still works for subscribeWidget.
#[wasm_bindgen]
pub fn close_stream_js(stream_index: u32) -> Result<(), JsValue> {
    STREAM_MAP.with(|m| {
        let mut map = m.borrow_mut();
        let entry = map
            .get_mut(&stream_index)
            .ok_or_else(|| JsValue::from_str(&format!("stream index {stream_index} not found")))?;
        entry.1 = None;
        Ok(())
    })
}

/// Resolve (input name → stream index) to (input name → StreamHandleId) for run_node_with_graph_inputs.
/// Called from resolve_external_streams in lib.rs. Returns None if any index is invalid.
pub fn resolve_external_streams(
    name_to_index: &HashMap<String, u32>,
) -> Option<HashMap<String, StreamHandleId>> {
    let mut out = HashMap::new();
    for (name, &index) in name_to_index {
        let handle = get_stream_handle_id(index)?;
        out.insert(name.clone(), handle);
    }
    Some(out)
}

/// Get StreamHandleId for a stream index (for resolve_external_streams). Returns None if index invalid or stream closed.
fn get_stream_handle_id(stream_index: u32) -> Option<StreamHandleId> {
    STREAM_MAP.with(|m| m.borrow().get(&stream_index).map(|(id, _)| *id))
}

// close_stream_js returns Result<(), JsValue>; the .map(|_| ()) fixes the type (we want Ok(()) from the inner map)
