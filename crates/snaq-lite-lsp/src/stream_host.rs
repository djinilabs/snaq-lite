//! WASM host API for stream indices (createStreamInput/pushChunk/closeStream/startFeeder/getStreamHandleId).
//! Used so the frontend can create/feed streams and the LSP can resolve external_streams for subscribeWidget.
//! Uses bounded channels so feeders apply back-pressure.

use std::cell::RefCell;
use std::collections::HashMap;

use futures::sink::SinkExt;
use snaq_lite_lang::{
    create_stream_input,
    csv_stream_parse::{csv_delimiter_from_line, parse_csv_line_to_record, strip_bom},
    map_registry::record_to_chunk_element,
    Chunk, Quantity, Record, StreamHandleId, StreamChunkSender, Unit, Value,
};
use wasm_bindgen::prelude::*;

thread_local! {
    /// index (u32) → (StreamHandleId, Some(Sender) until close). After close we keep (HandleId, None) so resolve_external_streams can still resolve index → handle.
    static STREAM_MAP: RefCell<HashMap<u32, (StreamHandleId, Option<StreamChunkSender>)>> = RefCell::new(HashMap::new());
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

/// Create a new stream input. Returns stream index for pushChunk/closeStream/startFeeder and for externalStreams.
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

/// Push a chunk (JS array of numbers) to the stream. Spawns a task to send so the JS thread is not blocked; back-pressure is applied in the worker.
#[wasm_bindgen]
pub fn push_chunk_js(stream_index: u32, chunk_js: &js_sys::Array) -> Result<(), JsValue> {
    let sender = STREAM_MAP
        .with(|m| m.borrow().get(&stream_index).and_then(|(_, s)| s.as_ref()).cloned())
        .ok_or_else(|| JsValue::from_str(&format!("stream index {stream_index} not found or closed")))?;
    let chunk = js_array_to_chunk(chunk_js)?;
    wasm_bindgen_futures::spawn_local(async move {
        let mut s = sender;
        let _ = s.send(chunk).await;
    });
    Ok(())
}

/// Convert JS array of row objects (each row = object with string keys and number values) to a Chunk of map values.
fn js_rows_to_chunk(arr: &js_sys::Array) -> Result<Chunk, JsValue> {
    let mut chunk = Vec::with_capacity(arr.length() as usize);
    for i in 0..arr.length() {
        let row_js = arr.get(i);
        let obj = row_js
            .dyn_ref::<js_sys::Object>()
            .ok_or_else(|| JsValue::from_str("each row must be an object"))?;
        let keys = js_sys::Object::keys(obj);
        let mut record: Record = Vec::new();
        for j in 0..keys.length() {
            let key_js = keys.get(j);
            let key = key_js
                .as_string()
                .ok_or_else(|| JsValue::from_str("row key must be string"))?;
            let val_js = js_sys::Reflect::get(obj, &key_js)
                .map_err(|_| JsValue::from_str("row value get failed"))?;
            let value = if val_js.is_null() || val_js.is_undefined() {
                Value::Undefined
            } else {
                let n = val_js
                    .as_f64()
                    .ok_or_else(|| JsValue::from_str("row value must be number or null"))?;
                Value::Numeric(Quantity::from_scalar(n))
            };
            record.push((key, value));
        }
        let elem = record_to_chunk_element(record)
            .map_err(|e| JsValue::from_str(&e.to_string()))?;
        chunk.push(Ok(elem));
    }
    Ok(chunk)
}

/// Push a chunk of row-as-map values (JS array of objects: each object = column name → number). Spawns send in background for back-pressure.
#[wasm_bindgen]
pub fn push_chunk_maps_js(stream_index: u32, rows_js: &js_sys::Array) -> Result<(), JsValue> {
    let sender = STREAM_MAP
        .with(|m| m.borrow().get(&stream_index).and_then(|(_, s)| s.as_ref()).cloned())
        .ok_or_else(|| JsValue::from_str(&format!("stream index {stream_index} not found or closed")))?;
    let chunk = js_rows_to_chunk(rows_js)?;
    wasm_bindgen_futures::spawn_local(async move {
        let mut s = sender;
        let _ = s.send(chunk).await;
    });
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

/// Parse newline-delimited numbers from buffer. Returns (chunk of scalar values, remaining bytes).
fn parse_newline_delimited_numbers(buffer: &[u8], scalar: &Unit) -> (Chunk, Vec<u8>) {
    let mut chunk = Vec::new();
    let mut rest = buffer;
    loop {
        let line_end = rest.iter().position(|&b| b == b'\n');
        match line_end {
            Some(i) => {
                let line = &rest[..i];
                rest = &rest[i + 1..];
                let s = match std::str::from_utf8(line) {
                    Ok(x) => x.trim(),
                    Err(_) => continue,
                };
                if s.is_empty() {
                    continue;
                }
                if let Ok(n) = s.parse::<f64>() {
                    let q = Quantity::with_number(
                        snaq_lite_lang::SnaqNumber::new(n, 0.0),
                        scalar.clone(),
                    );
                    chunk.push(Ok(Some(Value::Numeric(q))));
                }
            }
            None => break,
        }
    }
    (chunk, rest.to_vec())
}

/// Yield to the event loop so the UI stays responsive.
async fn yield_to_event_loop() {
    let promise = js_sys::Promise::resolve(&JsValue::NULL);
    let _ = wasm_bindgen_futures::JsFuture::from(promise).await;
}

/// Start a feeder task that reads from a JS ReadableStream, parses newline-delimited numbers,
/// and pushes chunks with send().await (back-pressure). Drops the sender when done.
#[wasm_bindgen]
pub fn start_feeder_js(stream_index: u32, readable_stream: JsValue) -> Result<(), JsValue> {
    use web_sys::ReadableStreamDefaultReader;

    let sender = STREAM_MAP
        .with(|m| {
            let mut map = m.borrow_mut();
            map.get_mut(&stream_index)
                .and_then(|(_, s)| s.take())
                .ok_or_else(|| JsValue::from_str(&format!("stream index {stream_index} not found or already feeding")))
        })
        .map_err(|e| e)?;

    let stream = readable_stream
        .dyn_into::<web_sys::ReadableStream>()
        .map_err(|_| JsValue::from_str("argument must be a ReadableStream"))?;

    const FEEDER_YIELD_EVERY: u32 = 4;

    wasm_bindgen_futures::spawn_local(async move {
        let reader = match ReadableStreamDefaultReader::new(&stream) {
            Ok(r) => r,
            Err(_) => return,
        };

        let scalar = Unit::scalar();
        let mut buffer = Vec::<u8>::new();
        let mut read_count = 0u32;
        let mut sender = sender;

        loop {
            let promise = reader.read();
            let result = match wasm_bindgen_futures::JsFuture::from(promise).await {
                Ok(r) => r,
                Err(_) => break,
            };

            let done = js_sys::Reflect::get(&result, &JsValue::from_str("done"))
                .ok()
                .and_then(|v| v.as_bool())
                .unwrap_or(true);

            if done {
                if !buffer.is_empty() {
                    let (chunk, _) = parse_newline_delimited_numbers(&buffer, &scalar);
                    if !chunk.is_empty() {
                        let _ = sender.send(chunk).await;
                    }
                }
                break;
            }

            let value_js = js_sys::Reflect::get(&result, &JsValue::from_str("value")).ok();
            if let Some(arr) = value_js {
                if let Some(arr) = arr.dyn_ref::<js_sys::Uint8Array>() {
                    let len = arr.length() as usize;
                    let mut bytes = vec![0u8; len];
                    arr.copy_to(&mut bytes);
                    buffer.extend_from_slice(&bytes);
                }
            }

            let (chunk, remainder) = parse_newline_delimited_numbers(&buffer, &scalar);
            buffer = remainder;
            if !chunk.is_empty() {
                if sender.send(chunk).await.is_err() {
                    break;
                }
            }

            read_count += 1;
            if read_count % FEEDER_YIELD_EVERY == 0 {
                yield_to_event_loop().await;
            }
        }

        drop(sender);
    });

    Ok(())
}

/// Maximum CSV rows per chunk before sending (back-pressure).
const CSV_CHUNK_SIZE: usize = 512;

/// Start a feeder task that reads from a JS ReadableStream, parses CSV (first line = headers, rest = rows),
/// builds row-as-map chunks, and pushes with send().await (back-pressure). Drops the sender when done.
#[wasm_bindgen]
pub fn start_csv_feeder_js(stream_index: u32, readable_stream: JsValue) -> Result<(), JsValue> {
    use web_sys::ReadableStreamDefaultReader;

    let sender = STREAM_MAP
        .with(|m| {
            let mut map = m.borrow_mut();
            map.get_mut(&stream_index)
                .and_then(|(_, s)| s.take())
                .ok_or_else(|| {
                    JsValue::from_str(&format!(
                        "stream index {stream_index} not found or already feeding"
                    ))
                })
        })
        .map_err(|e| e)?;

    let stream = readable_stream
        .dyn_into::<web_sys::ReadableStream>()
        .map_err(|_| JsValue::from_str("argument must be a ReadableStream"))?;

    const FEEDER_YIELD_EVERY: u32 = 4;

    wasm_bindgen_futures::spawn_local(async move {
        let reader = match ReadableStreamDefaultReader::new(&stream) {
            Ok(r) => r,
            Err(_) => return,
        };

        let scalar = Unit::scalar();
        let mut buffer = Vec::<u8>::new();
        let mut read_count = 0u32;
        let mut sender = sender;
        let mut headers: Option<Vec<String>> = None;
        let mut delimiter = ',';
        let mut chunk: Chunk = Vec::with_capacity(CSV_CHUNK_SIZE);

        // Process complete lines from buffer. Returns (remainder, chunk_to_send if any).
        let process_buffer = |buf: &[u8],
                                  headers: &mut Option<Vec<String>>,
                                  delimiter: &mut char,
                                  chunk: &mut Chunk|
         -> (Vec<u8>, Option<Chunk>) {
            let last_newline = buf.iter().rposition(|&b| b == b'\n');
            let (complete, remainder) = match last_newline {
                Some(i) => (&buf[..i + 1], buf[i + 1..].to_vec()),
                None => return (buf.to_vec(), None),
            };
            let complete = strip_bom(complete);
            // Use lossy decoding so invalid UTF-8 does not stall the feeder (replacement chars may fail as numbers).
            let s = String::from_utf8_lossy(complete);
            let lines: Vec<&str> = s.lines().collect();

            let mut i = 0;
            if headers.is_none() && !lines.is_empty() {
                let first = lines[0].trim();
                *delimiter = csv_delimiter_from_line(first);
                *headers = Some(
                    first
                        .split(*delimiter)
                        .map(|c| c.trim().to_string())
                        .collect(),
                );
                i = 1;
            }
            let Some(ref h) = headers else {
                return (remainder, None);
            };
            let mut to_send = None;
            for line in lines.iter().skip(i) {
                let line = line.trim();
                if line.is_empty() {
                    continue;
                }
                match parse_csv_line_to_record(line, h, *delimiter, &scalar) {
                    Ok(record) => {
                        match record_to_chunk_element(record) {
                            Ok(elem) => chunk.push(Ok(elem)),
                            Err(e) => chunk.push(Err(e)),
                        }
                        if chunk.len() >= CSV_CHUNK_SIZE {
                            to_send = Some(std::mem::take(chunk));
                            chunk.reserve(CSV_CHUNK_SIZE);
                        }
                    }
                    Err(e) => chunk.push(Err(e)),
                }
            }
            (remainder, to_send)
        };

        loop {
            let promise = reader.read();
            let result = match wasm_bindgen_futures::JsFuture::from(promise).await {
                Ok(r) => r,
                Err(_) => break,
            };

            let done = js_sys::Reflect::get(&result, &JsValue::from_str("done"))
                .ok()
                .and_then(|v| v.as_bool())
                .unwrap_or(true);

            if done {
                if !buffer.is_empty() {
                    let (rem, to_send) =
                        process_buffer(&buffer, &mut headers, &mut delimiter, &mut chunk);
                    if let Some(c) = to_send {
                        if sender.send(c).await.is_err() {
                            break;
                        }
                    }
                    if !rem.is_empty() {
                        let rem_trimmed = strip_bom(&rem);
                        let lossy = String::from_utf8_lossy(rem_trimmed).into_owned();
                        let s = lossy.trim();
                        if headers.is_none() && !s.is_empty() {
                            // File had no newline: single line is header only, no data rows.
                            delimiter = csv_delimiter_from_line(s);
                            let _ = headers.insert(
                                s.split(delimiter)
                                    .map(|c| c.trim().to_string())
                                    .collect(),
                            );
                        } else if !s.is_empty() && headers.is_some() {
                            let h = headers.as_ref().unwrap();
                            match parse_csv_line_to_record(s, h, delimiter, &scalar) {
                                Ok(record) => {
                                    if let Ok(elem) = record_to_chunk_element(record) {
                                        chunk.push(Ok(elem));
                                    }
                                }
                                Err(e) => chunk.push(Err(e)),
                            }
                        }
                    }
                }
                if !chunk.is_empty() {
                    let _ = sender.send(std::mem::take(&mut chunk)).await;
                }
                break;
            }

            let value_js = js_sys::Reflect::get(&result, &JsValue::from_str("value")).ok();
            if let Some(arr) = value_js {
                if let Some(arr) = arr.dyn_ref::<js_sys::Uint8Array>() {
                    let len = arr.length() as usize;
                    let mut bytes = vec![0u8; len];
                    arr.copy_to(&mut bytes);
                    buffer.extend_from_slice(&bytes);
                }
            }

            let (rem, to_send) =
                process_buffer(&buffer, &mut headers, &mut delimiter, &mut chunk);
            if let Some(c) = to_send {
                if sender.send(c).await.is_err() {
                    break;
                }
            }
            buffer = rem;

            read_count += 1;
            if read_count % FEEDER_YIELD_EVERY == 0 {
                yield_to_event_loop().await;
            }
        }

        drop(sender);
    });

    Ok(())
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
