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

/// Writer that sends bytes to the host via postMessage (callback set by host).
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
        if !self.buffer.is_empty() {
            if let Some(ref send) = self.sender {
                let s = String::from_utf8_lossy(&self.buffer);
                let _ = send.call1(&JsValue::NULL, &JsValue::from_str(&s));
                self.buffer.clear();
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
