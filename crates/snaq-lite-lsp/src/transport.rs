//! WASM transport: bridge LSP I/O to Web Worker postMessage/onmessage.

use futures::channel::mpsc;
use futures::io::{AsyncRead, AsyncWrite};
use futures::stream::Stream;
use std::pin::Pin;
use std::task::{Context, Poll};
use tower_lsp::Server;
use wasm_bindgen::prelude::*;
use wasm_bindgen_futures::spawn_local;

/// Reader that yields bytes from messages pushed by the host (Worker onmessage).
pub struct WasmMessageReader {
    receiver: mpsc::UnboundedReceiver<Vec<u8>>,
    buffer: std::io::Cursor<Vec<u8>>,
}

impl WasmMessageReader {
    pub fn new(receiver: mpsc::UnboundedReceiver<Vec<u8>>) -> Self {
        Self {
            receiver,
            buffer: std::io::Cursor::new(Vec::new()),
        }
    }
}

impl AsyncRead for WasmMessageReader {
    fn poll_read(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &mut [u8],
    ) -> Poll<std::io::Result<usize>> {
        if buf.is_empty() {
            return Poll::Ready(Ok(0));
        }
        let this = self.get_mut();
        if this.buffer.position() as usize >= this.buffer.get_ref().len() {
            match Pin::new(&mut this.receiver).poll_next(cx) {
                Poll::Ready(Some(bytes)) => {
                    this.buffer = std::io::Cursor::new(bytes);
                }
                Poll::Ready(None) => return Poll::Ready(Ok(0)),
                Poll::Pending => return Poll::Pending,
            }
        }
        let n = std::io::Read::read(&mut this.buffer, buf).map_err(|e| {
            std::io::Error::new(std::io::ErrorKind::Other, e)
        })?;
        Poll::Ready(Ok(n))
    }
}

/// LSP stdio framing: "Content-Length: N\r\n\r\n" then N bytes of body.
/// We only send to the host when we have at least one complete frame so we never
/// postMessage a partial header (e.g. "Conte") which would cause JSON parse errors.
fn take_one_lsp_frame(buf: &[u8]) -> Option<(usize, usize)> {
    const PREFIX: &[u8] = b"Content-Length: ";
    if buf.len() < PREFIX.len() || !buf.starts_with(PREFIX) {
        return None;
    }
    let after_prefix = &buf[PREFIX.len()..];
    let mut n_digits = 0;
    for b in after_prefix {
        if b.is_ascii_digit() {
            n_digits += 1;
        } else {
            break;
        }
    }
    if n_digits == 0 {
        return None;
    }
    let n: usize = std::str::from_utf8(&after_prefix[..n_digits])
        .ok()
        .and_then(|s| s.parse().ok())?;
    let header_end = PREFIX.len() + n_digits;
    let rest = &buf[header_end..];
    let sep = if rest.starts_with(b"\r\n\r\n") {
        4
    } else if rest.starts_with(b"\n\n") {
        2
    } else {
        return None;
    };
    let body_start = header_end + sep;
    if buf.len() < body_start + n {
        return None;
    }
    Some((body_start + n, n))
}

/// Writer that sends bytes to the host via postMessage (callback set by host).
/// Buffers output until a complete LSP Content-Length frame is available so the
/// host never receives a partial frame (e.g. "Conte" from "Content-Length: ...").
pub struct WasmMessageWriter {
    sender: Option<js_sys::Function>,
    buffer: Vec<u8>,
}

impl WasmMessageWriter {
    pub fn new(sender: js_sys::Function) -> Self {
        Self {
            sender: Some(sender),
            buffer: Vec::new(),
        }
    }
}

impl AsyncWrite for WasmMessageWriter {
    fn poll_write(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &[u8],
    ) -> Poll<std::io::Result<usize>> {
        self.as_mut().get_mut().buffer.extend_from_slice(buf);
        let _ = self.as_mut().poll_flush(cx);
        Poll::Ready(Ok(buf.len()))
    }

    fn poll_flush(
        mut self: Pin<&mut Self>,
        _cx: &mut Context<'_>,
    ) -> Poll<std::io::Result<()>> {
        // Clone sender so we don't hold an immutable borrow of self while mutating self.buffer.
        let send = match self.sender.clone() {
            Some(s) => s,
            None => return Poll::Ready(Ok(())),
        };
        let buffer = &mut self.as_mut().get_mut().buffer;
        while let Some((frame_len, _body_len)) = take_one_lsp_frame(buffer) {
            let frame: Vec<u8> = buffer.drain(..frame_len).collect();
            if let Ok(s) = String::from_utf8(frame) {
                let _ = send.call1(&JsValue::NULL, &JsValue::from_str(&s));
            }
        }
        Poll::Ready(Ok(()))
    }

    fn poll_close(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<std::io::Result<()>> {
        let _ = self.as_mut().poll_flush(cx);
        self.sender = None;
        Poll::Ready(Ok(()))
    }
}

/// Sender for pushing incoming LSP messages (called from JS when Worker receives a message).
static mut INCOMING_SENDER: Option<mpsc::UnboundedSender<Vec<u8>>> = None;

/// Called by the host when the Worker receives an LSP message (e.g. from IDE).
/// The host should pass the raw string or bytes of the JSON-RPC message (including Content-Length header if present).
#[wasm_bindgen]
pub fn push_lsp_message(s: &str) {
    unsafe {
        if let Some(ref tx) = INCOMING_SENDER {
            let _ = tx.unbounded_send(s.as_bytes().to_vec());
        }
    }
}

/// Start the LSP server in the Web Worker. Call once after loading the module.
/// `post_message_callback` is a JS function that will be called with the response string to send back (host should call self.postMessage(result)).
#[wasm_bindgen]
pub fn start_snaq_lite_lsp(post_message_callback: js_sys::Function) {
    let (tx, rx) = mpsc::unbounded();
    unsafe {
        INCOMING_SENDER = Some(tx);
    }
    let reader = WasmMessageReader::new(rx);
    let writer = WasmMessageWriter::new(post_message_callback);
    let (service, socket) = crate::create_lsp_service();
    let server = Server::new(reader, writer, socket);
    spawn_local(async move {
        server.serve(service).await;
    });
}

#[cfg(test)]
mod tests {
    use super::take_one_lsp_frame;

    #[test]
    fn writer_emits_only_complete_lsp_frames() {
        let body = r#"{"jsonrpc":"2.0","id":1}"#;
        let msg = format!("Content-Length: {}\r\n\r\n{}", body.len(), body);
        let bytes = msg.as_bytes();
        let full = take_one_lsp_frame(bytes);
        assert!(full.is_some());
        let partial = take_one_lsp_frame(&bytes[..bytes.len() - 1]);
        assert!(partial.is_none());
    }

    #[test]
    fn reader_handles_back_to_back_framed_messages() {
        let body1 = r#"{"jsonrpc":"2.0","id":1}"#;
        let body2 = r#"{"jsonrpc":"2.0","id":2}"#;
        let msg1 = format!("Content-Length: {}\r\n\r\n{}", body1.len(), body1);
        let msg2 = format!("Content-Length: {}\r\n\r\n{}", body2.len(), body2);
        let bytes = [msg1.as_bytes(), msg2.as_bytes()].concat();
        let first = take_one_lsp_frame(&bytes).expect("first frame");
        let second = take_one_lsp_frame(&bytes[first.0..]).expect("second frame");
        assert!(second.0 > 0);
    }

    #[test]
    fn control_messages_do_not_corrupt_lsp_frame_stream() {
        assert!(take_one_lsp_frame(br#"{"type":"init"}"#).is_none());
        let body = r#"{"jsonrpc":"2.0","id":3}"#;
        let msg = format!("Content-Length: {}\r\n\r\n{}", body.len(), body);
        assert!(take_one_lsp_frame(msg.as_bytes()).is_some());
    }
}
