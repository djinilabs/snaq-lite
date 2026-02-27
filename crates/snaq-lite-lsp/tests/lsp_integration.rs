//! Native integration tests: run LSP server with mock stdio, send LSP messages, assert responses.

#![cfg(not(target_arch = "wasm32"))]

use std::io::Read;
use std::time::Duration;
use tokio::io::{duplex, AsyncReadExt, AsyncWriteExt};
use tokio::time::timeout;

/// LSP message format: "Content-Length: N\r\n\r\n{body}"
fn lsp_message(body: &str) -> Vec<u8> {
    let mut msg = format!("Content-Length: {}\r\n\r\n", body.len());
    msg.push_str(body);
    msg.into_bytes()
}

/// Parse Content-Length from response and read body (sync, for a buffer).
fn read_lsp_response(mut r: impl Read) -> std::io::Result<String> {
    let mut header = String::new();
    loop {
        let mut b = [0u8; 1];
        if r.read(&mut b)? == 0 {
            return Ok(header);
        }
        let c = b[0] as char;
        header.push(c);
        if header.ends_with("\r\n\r\n") {
            break;
        }
    }
    let len = header
        .lines()
        .find(|l| l.starts_with("Content-Length:"))
        .and_then(|l| l.trim_start_matches("Content-Length:").trim().parse::<usize>().ok())
        .unwrap_or(0);
    let mut body = vec![0u8; len];
    r.read_exact(&mut body)?;
    String::from_utf8(body).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))
}

/// Read one LSP message from async stream (header + body).
async fn read_one_lsp_message_async(
    r: &mut (impl tokio::io::AsyncRead + Unpin),
) -> std::io::Result<String> {
    let mut header = String::new();
    loop {
        let mut b = [0u8; 1];
        if r.read_exact(&mut b).await.is_err() {
            break;
        }
        header.push(b[0] as char);
        if header.ends_with("\r\n\r\n") {
            break;
        }
    }
    let len = header
        .lines()
        .find(|l| l.starts_with("Content-Length:"))
        .and_then(|l| l.trim_start_matches("Content-Length:").trim().parse::<usize>().ok())
        .unwrap_or(0);
    let mut body = vec![0u8; len];
    r.read_exact(&mut body).await?;
    String::from_utf8(body).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))
}

#[tokio::test]
async fn native_initialize_returns_capabilities() {
    let (client_w, server_r) = duplex(4096);
    let (server_w, client_r) = duplex(4096);

    let server_handle = tokio::spawn(async move {
        snaq_lite_lsp::run_native(server_r, server_w).await
    });

    let init_request = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "initialize",
        "params": {
            "processId": null,
            "rootUri": null,
            "capabilities": {},
            "clientInfo": { "name": "test", "version": "0.1.0" }
        }
    });
    let msg = lsp_message(&init_request.to_string());

    let mut client_w = client_w;
    let mut client_r = client_r;
    client_w.write_all(&msg).await.unwrap();
    client_w.flush().await.unwrap();
    drop(client_w);

    let response = timeout(Duration::from_secs(5), async {
        let mut buf = Vec::new();
        client_r.read_to_end(&mut buf).await.unwrap();
        buf
    })
    .await
    .expect("timeout waiting for initialize response");

    let body = read_lsp_response(response.as_slice()).unwrap();
    let response: serde_json::Value = serde_json::from_str(&body).unwrap();
    let result = response.get("result").expect("response has result");
    let capabilities = result.get("capabilities").expect("result has capabilities");
    assert!(capabilities.get("hoverProvider").is_some());
    assert!(capabilities.get("textDocumentSync").is_some());

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn native_did_open_and_hover_returns_value() {
    let (client_w, server_r) = duplex(8192);
    let (server_w, client_r) = duplex(8192);

    let server_handle = tokio::spawn(async move {
        snaq_lite_lsp::run_native(server_r, server_w).await
    });

    let mut client_w = client_w;
    let mut client_r = client_r;

    // Initialize
    let init_request = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "initialize",
        "params": {
            "processId": null,
            "rootUri": null,
            "capabilities": {},
            "clientInfo": { "name": "test", "version": "0.1.0" }
        }
    });
    client_w.write_all(&lsp_message(&init_request.to_string())).await.unwrap();
    client_w.flush().await.unwrap();

    let init_body = timeout(
        Duration::from_secs(5),
        read_one_lsp_message_async(&mut client_r),
    )
    .await
    .expect("timeout on initialize")
    .unwrap();
    let _init: serde_json::Value = serde_json::from_str(&init_body).unwrap();

    // Initialized notification (no response)
    let initialized = serde_json::json!({
        "jsonrpc": "2.0",
        "method": "initialized",
        "params": {}
    });
    client_w.write_all(&lsp_message(&initialized.to_string())).await.unwrap();
    client_w.flush().await.unwrap();

    // didOpen with "1 + 2"
    let did_open = serde_json::json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didOpen",
        "params": {
            "textDocument": {
                "uri": "file:///doc.snaq",
                "languageId": "snaq",
                "version": 1,
                "text": "1 + 2"
            }
        }
    });
    client_w.write_all(&lsp_message(&did_open.to_string())).await.unwrap();
    client_w.flush().await.unwrap();

    // Hover at (0, 2) - around the "+"
    let hover_request = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "textDocument/hover",
        "params": {
            "textDocument": { "uri": "file:///doc.snaq" },
            "position": { "line": 0, "character": 2 }
        }
    });
    client_w.write_all(&lsp_message(&hover_request.to_string())).await.unwrap();
    client_w.flush().await.unwrap();

    // Server may send logMessage etc.; read until we get the hover response (id: 2)
    let hover_body = timeout(
        Duration::from_secs(5),
        async {
            loop {
                let body = read_one_lsp_message_async(&mut client_r).await.unwrap();
                let v: serde_json::Value = serde_json::from_str(&body).unwrap();
                if v.get("id").and_then(|i| i.as_u64()) == Some(2) {
                    return body;
                }
            }
        },
    )
    .await
    .expect("timeout on hover");
    let hover_response: serde_json::Value = serde_json::from_str(&hover_body).unwrap();
    let result = hover_response.get("result").and_then(|r| r.as_object());
    assert!(result.is_some(), "hover returned result: {}", hover_body);
    let contents_val = result.and_then(|r| r.get("contents"));
    let content = contents_val
        .and_then(|c| c.as_str())
        .or_else(|| contents_val.and_then(|c| c.get("value")).and_then(|v| v.as_str()))
        .unwrap_or_default();
    assert!(!content.is_empty(), "hover result has contents: {}", hover_body);
    assert!(content.contains("3") || content.contains("1") || content.contains("2"), "hover content: {}", content);

    server_handle.abort();
    let _ = server_handle.await;
}
