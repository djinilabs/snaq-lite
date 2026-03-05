//! WASM Host: stream input registry, run result storage, and JS-facing helpers.
//! Bridges browser I/O and the Salsa reactive runtime without blocking the event loop.

use wasm_bindgen::{JsCast, JsValue};

use futures::stream::StreamExt;
use web_sys::ReadableStreamDefaultReader;
use futures::sink::SinkExt;
use snaq_lite_lang::{
    create_stream_input, default_si_registry, run_with_stream_inputs, vector_into_stream,
    Chunk, FuzzyBool, Quantity, SnaqNumber, StreamChunkSender, StreamHandleId, Unit, Value,
};
use std::cell::RefCell;
use std::collections::HashMap;

/// Yield to the event loop every this many elements in the consumer loop.
const CONSUMER_YIELD_EVERY: u32 = 16;
/// Yield to the event loop every this many read() calls in the feeder loop.
const FEEDER_YIELD_EVERY: u32 = 4;

/// Host-held stream: handle id (for Salsa registry) and sender (None after close or when feeder owns it).
struct HostStreamHandle {
    id: StreamHandleId,
    sender: RefCell<Option<StreamChunkSender>>,
}

type RunResultSlot = RefCell<Option<(Value, salsa::DatabaseImpl)>>;

thread_local! {
    /// Index -> (StreamHandleId, Sender). createStreamInput pushes and returns index.
    static STREAM_HANDLES: RefCell<Vec<HostStreamHandle>> = const { RefCell::new(Vec::new()) };

    /// Run index -> (Value, Database). runWithStreamInputs pushes; consumeOutputStream takes.
    static RUN_RESULTS: RefCell<Vec<RunResultSlot>> = const { RefCell::new(Vec::new()) };
}

/// Create a new stream input. Returns an index (u32) to use as stream id in runWithStreamInputs and pushChunk.
pub fn create_stream_input_host() -> u32 {
    let (id, sender) = create_stream_input();
    STREAM_HANDLES.with(|handles| {
        let mut h = handles.borrow_mut();
        let index = h.len();
        h.push(HostStreamHandle {
            id,
            sender: RefCell::new(Some(sender)),
        });
        index as u32
    })
}

/// Look up StreamHandleId and Sender by index. Returns None if index is invalid or stream closed.
fn get_stream_handle(index: u32) -> Option<(StreamHandleId, StreamChunkSender)> {
    STREAM_HANDLES.with(|handles| {
        let h = handles.borrow();
        let i = index as usize;
        h.get(i)
            .and_then(|x| x.sender.borrow().as_ref().map(|s| (x.id, s.clone())))
    })
}

/// Build stream input map from JS object: keys are names (e.g. "data"), values are stream indices (u32).
pub fn stream_input_map_from_js(
    obj: &js_sys::Object,
) -> Result<HashMap<String, StreamHandleId>, JsValue> {
    let keys = js_sys::Object::keys(obj);
    let mut map = HashMap::new();
    for i in 0..keys.length() {
        let key = keys.get(i);
        let key_str = key.as_string().ok_or_else(|| JsValue::from_str("stream_input_map key must be string"))?;
        let val = js_sys::Reflect::get(obj, &key).map_err(|_| JsValue::from_str("stream_input_map get failed"))?;
        let f = val
            .as_f64()
            .ok_or_else(|| JsValue::from_str("stream_input_map value must be a number (stream index)"))?;
        if f < 0.0 || f >= u32::MAX as f64 || f.fract() != 0.0 {
            return Err(JsValue::from_str(
                "stream_input_map value must be a non-negative integer (stream index from createStreamInput)",
            ));
        }
        let index = f as u32;
        let (id, _) = get_stream_handle(index)
            .ok_or_else(|| JsValue::from_str(&format!("stream index {index} not found")))?;
        map.insert(key_str, id);
    }
    Ok(map)
}

/// Run with stream inputs and store the result. Returns run index for consumeOutputStream.
pub fn run_with_stream_inputs_host(
    script: &str,
    stream_input_map_js: &js_sys::Object,
) -> Result<RunResultJs, JsValue> {
    let registry = default_si_registry();
    let stream_inputs = stream_input_map_from_js(stream_input_map_js)?;
    let (value, db) = run_with_stream_inputs(script, &registry, stream_inputs)
        .map_err(|e| JsValue::from_str(&e.to_string()))?;

    let is_vector = matches!(&value, Value::Vector(_));
    let run_index = RUN_RESULTS.with(|results| {
        let mut r = results.borrow_mut();
        let index = r.len();
        r.push(RefCell::new(Some((value, db))));
        index as u32
    });

    Ok(RunResultJs {
        run_index,
        is_vector,
    })
}

/// Small struct returned to JS from runWithStreamInputs.
#[derive(Clone)]
pub struct RunResultJs {
    pub run_index: u32,
    pub is_vector: bool,
}

/// Convert a JS array of numbers to a Chunk (scalar dimensionless values, variance 0).
pub fn js_array_to_chunk(arr: &js_sys::Array) -> Result<Chunk, JsValue> {
    let scalar = Unit::scalar();
    let mut chunk = Vec::with_capacity(arr.length() as usize);
    for i in 0..arr.length() {
        let v = arr.get(i);
        if v.is_null() || v.is_undefined() {
            chunk.push(Ok(None));
        } else {
            let n = v
                .as_f64()
                .ok_or_else(|| JsValue::from_str("chunk element must be number or null"))?;
            let q = Quantity::with_number(SnaqNumber::new(n, 0.0), scalar.clone());
            chunk.push(Ok(Some(Value::Numeric(q))));
        }
    }
    Ok(chunk)
}

/// Push a chunk to a stream by index. Spawns send in background so JS thread is not blocked.
pub fn push_chunk_host(stream_index: u32, chunk_js: &js_sys::Array) -> Result<(), JsValue> {
    let sender = get_stream_handle(stream_index)
        .map(|(_, s)| s)
        .ok_or_else(|| JsValue::from_str(&format!("stream index {stream_index} not found or closed")))?;
    let chunk = js_array_to_chunk(chunk_js)?;
    wasm_bindgen_futures::spawn_local(async move {
        let mut s = sender;
        let _ = s.send(chunk).await;
    });
    Ok(())
}

/// Close the stream (signal EOF). After this, pushChunk will fail.
pub fn close_stream_host(stream_index: u32) -> Result<(), JsValue> {
    STREAM_HANDLES.with(|handles| {
        let mut h = handles.borrow_mut();
        let i = stream_index as usize;
        let handle = h.get_mut(i).ok_or_else(|| JsValue::from_str(&format!("stream index {stream_index} not found")))?;
        handle.sender = RefCell::new(None);
        Ok(())
    })
}

/// Take the (Value, Database) for a run index. Returns None if already consumed or invalid index.
pub fn take_run_result(run_index: u32) -> Option<(Value, salsa::DatabaseImpl)> {
    RUN_RESULTS.with(|results| {
        let r = results.borrow();
        let i = run_index as usize;
        r.get(i).and_then(|cell| cell.borrow_mut().take())
    })
}

/// Yield control back to the browser event loop so the UI stays responsive.
pub async fn yield_to_event_loop() {
    let promise = js_sys::Promise::resolve(&JsValue::NULL);
    let _ = wasm_bindgen_futures::JsFuture::from(promise).await;
}

/// Serialize a single Value to JsValue for passing to JS callbacks.
/// Numeric -> number, Undefined -> null, FuzzyBool -> "true"/"false"/object, rest -> display string.
pub fn value_to_js(value: &Value) -> JsValue {
    match value {
        Value::Numeric(q) => JsValue::from_f64(q.value()),
        Value::Undefined => JsValue::NULL,
        Value::FuzzyBool(fb) => match fb {
            FuzzyBool::True => JsValue::from_str("true"),
            FuzzyBool::False => JsValue::from_str("false"),
            FuzzyBool::Uncertain(p) => {
                let obj = js_sys::Object::new();
                let _ = js_sys::Reflect::set(&obj, &JsValue::from_str("uncertain"), &JsValue::from_f64(p.0));
                obj.into()
            }
        },
        Value::Symbolic(sq) => JsValue::from_str(&sq.to_string()),
        Value::Vector(_) => JsValue::from_str("<vector>"),
        Value::Function(_) | Value::BuiltinFunction(_) => JsValue::from_str("<function>"),
        Value::Map(_) => JsValue::from_str("<map>"),
        Value::Date(gd) => JsValue::from_str(&gd.to_string()),
    }
}

/// Run the output stream for a run result (must be a vector). Calls onChunk(element) for each
/// element, onDone() at end, onError(message) on error. Yields to the event loop periodically.
pub fn consume_output_stream_host(
    run_index: u32,
    on_chunk: &js_sys::Function,
    on_done: &js_sys::Function,
    on_error: &js_sys::Function,
) -> Result<(), JsValue> {
    let on_chunk = on_chunk.clone();
    let on_done = on_done.clone();
    let on_error = on_error.clone();

    wasm_bindgen_futures::spawn_local(async move {
        let (value, db) = match take_run_result(run_index) {
            Some(x) => x,
            None => {
                let _ = on_error.call1(&JsValue::NULL, &JsValue::from_str("run result already consumed or invalid runIndex"));
                return;
            }
        };
        let inner = match &value {
            Value::Vector(v) => v.inner.clone(),
            _ => {
                let _ = on_error.call1(&JsValue::NULL, &JsValue::from_str("run result is not a vector"));
                return;
            }
        };

        let mut stream = vector_into_stream(&db, inner);
        let mut yield_count = 0u32;

        loop {
            match stream.next().await {
                Some(Ok(Some(v))) => {
                    let js = value_to_js(&v);
                    let _ = on_chunk.call1(&JsValue::NULL, &js);
                    yield_count += 1;
                    if yield_count.is_multiple_of(CONSUMER_YIELD_EVERY) {
                        yield_to_event_loop().await;
                    }
                }
                Some(Ok(None)) => {
                    let _ = on_chunk.call1(&JsValue::NULL, &JsValue::NULL);
                    yield_count += 1;
                    if yield_count.is_multiple_of(CONSUMER_YIELD_EVERY) {
                        yield_to_event_loop().await;
                    }
                }
                Some(Err(e)) => {
                    let _ = on_error.call1(&JsValue::NULL, &JsValue::from_str(&e.to_string()));
                    break;
                }
                None => {
                    let _ = on_done.call0(&JsValue::NULL);
                    break;
                }
            }
        }
    });

    Ok(())
}

/// Parse newline-delimited numbers from buffer. Returns (chunk of scalar values, remaining bytes).
fn parse_newline_delimited_numbers(
    buffer: &[u8],
    scalar: &Unit,
) -> (Chunk, Vec<u8>) {
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
                    let q = Quantity::with_number(SnaqNumber::new(n, 0.0), scalar.clone());
                    chunk.push(Ok(Some(Value::Numeric(q))));
                }
            }
            None => break,
        }
    }
    (chunk, rest.to_vec())
}

/// Start a feeder task that reads from a JS ReadableStream, parses newline-delimited numbers,
/// and pushes chunks with send().await (back-pressure). Drops the sender when done.
pub fn start_feeder_host(
    stream_index: u32,
    readable_stream: JsValue,
) -> Result<(), JsValue> {
    let sender = STREAM_HANDLES.with(|handles| {
        let mut h = handles.borrow_mut();
        let i = stream_index as usize;
        h.get_mut(i)
            .and_then(|handle| handle.sender.borrow_mut().take())
            .ok_or_else(|| JsValue::from_str(&format!("stream index {stream_index} not found or already feeding")))
    })?;

    let stream = readable_stream
        .dyn_into::<web_sys::ReadableStream>()
        .map_err(|_| JsValue::from_str("argument must be a ReadableStream"))?;

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
            if !chunk.is_empty() && sender.send(chunk).await.is_err() {
                break;
            }

            read_count += 1;
            if read_count.is_multiple_of(FEEDER_YIELD_EVERY) {
                yield_to_event_loop().await;
            }
        }

        drop(sender);
    });

    Ok(())
}
