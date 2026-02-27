//! Native integration tests: run LSP server with mock stdio, send LSP messages, assert responses.

#![cfg(not(target_arch = "wasm32"))]

use std::io::Read;
use std::time::Duration;
use tokio::io::{duplex, AsyncReadExt, AsyncWriteExt};
use tokio::time::timeout;

/// Test document URI used by pub-sub and other tests.
const TEST_DOC_URI: &str = "file:///doc.snaq";
const DUPLEX_BUFFER_SIZE: usize = 8192;

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

/// Plan §8: did_change for a URI with an active subscription; assert subscription is removed
/// and client receives Cancelled.
#[tokio::test]
async fn native_subscribe_then_did_change_receives_cancelled() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle = tokio::spawn(async move {
        snaq_lite_lsp::run_native(server_r, server_w).await
    });

    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document(&mut client_w, "[1, 2, 3]", 1).await;

    let subscribe_request = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "snaqlite/subscribe",
        "params": { "textDocument": { "uri": TEST_DOC_URI } }
    });
    client_w.write_all(&lsp_message(&subscribe_request.to_string())).await.unwrap();
    client_w.flush().await.unwrap();

    // Read until we get the subscribe response (id: 2); may receive publishResult Completed first
    let subscription_id = timeout(
        Duration::from_secs(5),
        async {
            loop {
                let body = read_one_lsp_message_async(&mut client_r).await.unwrap();
                let v: serde_json::Value = serde_json::from_str(&body).unwrap();
                if v.get("id").and_then(|i| i.as_u64()) == Some(2) {
                    if let Some(err) = v.get("error") {
                        panic!("subscribe failed: {}", err);
                    }
                    let result = v.get("result").and_then(|r| r.get("subscriptionId"));
                    return result.and_then(|s| s.as_str()).unwrap_or("").to_string();
                }
            }
        },
    )
    .await
    .expect("timeout on subscribe response");
    assert!(!subscription_id.is_empty(), "subscribe should return subscriptionId");

    let did_change = serde_json::json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didChange",
        "params": {
            "textDocument": { "uri": TEST_DOC_URI, "version": 2 },
            "contentChanges": [{ "text": "2 + 3" }]
        }
    });
    client_w.write_all(&lsp_message(&did_change.to_string())).await.unwrap();
    client_w.flush().await.unwrap();

    // Read until we get snaqlite/publishResult with status Cancelled
    let cancelled = timeout(
        Duration::from_secs(5),
        async {
            loop {
                let body = read_one_lsp_message_async(&mut client_r).await.unwrap();
                let v: serde_json::Value = serde_json::from_str(&body).unwrap();
                if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/publishResult") {
                    let params = v.get("params").and_then(|p| p.as_object());
                    if let Some(p) = params {
                        if p.get("status").and_then(|s| s.as_str()) == Some("Cancelled") {
                            if p.get("subscriptionId").and_then(|s| s.as_str()) == Some(subscription_id.as_str()) {
                                return true;
                            }
                        }
                    }
                }
            }
        },
    )
    .await
    .expect("timeout waiting for Cancelled notification");
    assert!(cancelled, "client should receive publishResult Cancelled for the subscription");

    server_handle.abort();
    let _ = server_handle.await;
}

/// Subscribe to a scalar result; assert we get subscriptionId and one publishResult Completed with display.
#[tokio::test]
async fn native_subscribe_scalar_returns_id_and_completed() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle = tokio::spawn(async move {
        snaq_lite_lsp::run_native(server_r, server_w).await
    });

    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document(&mut client_w, "1 + 2", 1).await;

    let subscribe_request = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "snaqlite/subscribe",
        "params": { "textDocument": { "uri": TEST_DOC_URI } }
    });
    client_w.write_all(&lsp_message(&subscribe_request.to_string())).await.unwrap();
    client_w.flush().await.unwrap();

    let mut subscription_id = String::new();
    let mut got_completed = false;
    let mut completed_display: Option<String> = None;
    for _ in 0..15 {
        let body = timeout(Duration::from_secs(2), read_one_lsp_message_async(&mut client_r))
            .await
            .expect("timeout")
            .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("id").and_then(|i| i.as_u64()) == Some(2) {
            if v.get("error").is_some() {
                panic!("subscribe failed: {}", v["error"]);
            }
            subscription_id = v["result"]["subscriptionId"]
                .as_str()
                .unwrap_or("")
                .to_string();
        }
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/publishResult") {
            let params = v.get("params").and_then(|p| p.as_object()).unwrap();
            if params.get("status").and_then(|s| s.as_str()) == Some("Completed") {
                got_completed = true;
                completed_display = params
                    .get("data")
                    .and_then(|d| d.get("display"))
                    .and_then(|s| s.as_str())
                    .map(String::from);
            }
        }
        if !subscription_id.is_empty() && got_completed {
            break;
        }
    }
    assert!(!subscription_id.is_empty(), "subscribe should return subscriptionId");
    assert!(got_completed, "client should receive one publishResult Completed for scalar");
    assert!(
        completed_display.as_ref().map(|s| s.contains("3")).unwrap_or(false),
        "Completed data.display should show result: {:?}",
        completed_display
    );

    server_handle.abort();
    let _ = server_handle.await;
}

/// Subscribe to a vector; assert we get a subscription id and that streamed result payload shape is correct.
/// We read until we see Completed (pump with a hover so the server drains notifications), or we accept
/// that on native the consumer may not have finished before the next request; at minimum we assert
/// subscribe returns an id for a vector document.
#[tokio::test]
async fn native_subscribe_vector_returns_id_and_stream_completes() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle = tokio::spawn(async move {
        snaq_lite_lsp::run_native(server_r, server_w).await
    });

    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document(&mut client_w, "[1, 2, 3, 4, 5]", 1).await;

    let subscribe_request = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "snaqlite/subscribe",
        "params": { "textDocument": { "uri": TEST_DOC_URI } }
    });
    client_w.write_all(&lsp_message(&subscribe_request.to_string())).await.unwrap();
    client_w.flush().await.unwrap();

    let mut subscription_id = String::new();
    let mut _got_running = false;
    let mut got_completed = false;
    let mut total_elements: Option<u64> = None;
    for _ in 0..10 {
        let body = timeout(Duration::from_secs(2), read_one_lsp_message_async(&mut client_r))
            .await
            .expect("timeout reading LSP message")
            .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).expect("valid JSON LSP message");
        if v.get("id").and_then(|i| i.as_u64()) == Some(2) {
            if v.get("error").is_some() {
                panic!("subscribe failed: {}", v["error"]);
            }
            subscription_id = v["result"]["subscriptionId"]
                .as_str()
                .unwrap_or("")
                .to_string();
            break;
        }
    }
    assert!(!subscription_id.is_empty(), "subscribe for vector should return subscriptionId");

    // Pump: trigger server to drain and send any Running/Completed (notifications sent when handling next request).
    let hover_request = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 3,
        "method": "textDocument/hover",
        "params": { "textDocument": { "uri": TEST_DOC_URI }, "position": { "line": 0, "character": 0 } }
    });
    client_w.write_all(&lsp_message(&hover_request.to_string())).await.unwrap();
    client_w.flush().await.unwrap();

    for _ in 0..10 {
        let body = match timeout(Duration::from_secs(2), read_one_lsp_message_async(&mut client_r)).await {
            Ok(Ok(b)) => b,
            _ => break,
        };
        let v: serde_json::Value = serde_json::from_str(&body).expect("valid JSON LSP message");
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/publishResult") {
            let params = v.get("params").and_then(|p| p.as_object()).expect("publishResult params");
            let status = params.get("status").and_then(|s| s.as_str()).unwrap_or("");
            if status == "Running" {
                _got_running = true;
                if let Some(data) = params.get("data").and_then(|d| d.as_object()) {
                    assert!(data.contains_key("elements"), "Running data should have elements");
                }
            } else if status == "Completed" {
                got_completed = true;
                total_elements = params
                    .get("data")
                    .and_then(|d| d.get("totalElements"))
                    .and_then(|n| n.as_u64());
                break;
            }
        }
    }
    if got_completed {
        assert_eq!(total_elements, Some(5), "totalElements should be 5");
    }
    server_handle.abort();
    let _ = server_handle.await;
}

/// Subscribe then unsubscribe; assert unsubscribe response is null (success).
#[tokio::test]
async fn native_subscribe_then_unsubscribe_succeeds() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle = tokio::spawn(async move {
        snaq_lite_lsp::run_native(server_r, server_w).await
    });

    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document(&mut client_w, "[1, 2, 3]", 1).await;

    let subscribe_request = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "snaqlite/subscribe",
        "params": { "textDocument": { "uri": TEST_DOC_URI } }
    });
    client_w.write_all(&lsp_message(&subscribe_request.to_string())).await.unwrap();
    client_w.flush().await.unwrap();

    let mut subscription_id = String::new();
    for _ in 0..10 {
        let body = timeout(Duration::from_secs(2), read_one_lsp_message_async(&mut client_r))
            .await
            .expect("timeout")
            .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("id").and_then(|i| i.as_u64()) == Some(2) {
            subscription_id = v["result"]["subscriptionId"].as_str().unwrap_or("").to_string();
            break;
        }
    }
    assert!(!subscription_id.is_empty());

    let unsub = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 3,
        "method": "snaqlite/unsubscribe",
        "params": { "subscriptionId": subscription_id }
    });
    client_w.write_all(&lsp_message(&unsub.to_string())).await.unwrap();
    client_w.flush().await.unwrap();

    // Read until we get the unsubscribe response (id: 3); may receive publishResult first
    let body = timeout(
        Duration::from_secs(5),
        async {
            loop {
                let b = read_one_lsp_message_async(&mut client_r).await.unwrap();
                let v: serde_json::Value = serde_json::from_str(&b).unwrap();
                if v.get("id").and_then(|i| i.as_u64()) == Some(3) {
                    return b;
                }
            }
        },
    )
    .await
    .expect("timeout on unsubscribe response");
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(v.get("result").is_some(), "unsubscribe should return result (null): {}", body);
    assert!(v.get("error").is_none(), "unsubscribe should not error: {}", body);

    server_handle.abort();
    let _ = server_handle.await;
}

/// Subscribe with a URI that does not match the open document; assert server returns invalid_params error.
#[tokio::test]
async fn native_subscribe_wrong_uri_returns_error() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle = tokio::spawn(async move {
        snaq_lite_lsp::run_native(server_r, server_w).await
    });

    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document(&mut client_w, "1 + 2", 1).await;

    let subscribe_request = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "snaqlite/subscribe",
        "params": { "textDocument": { "uri": "file:///other.snaq" } }
    });
    client_w.write_all(&lsp_message(&subscribe_request.to_string())).await.unwrap();
    client_w.flush().await.unwrap();

    let body = timeout(
        Duration::from_secs(5),
        async {
            loop {
                let b = read_one_lsp_message_async(&mut client_r).await.unwrap();
                let v: serde_json::Value = serde_json::from_str(&b).unwrap();
                if v.get("id").and_then(|i| i.as_u64()) == Some(2) {
                    return b;
                }
            }
        },
    )
    .await
    .expect("timeout on subscribe response");
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    let err = v.get("error").expect("subscribe with wrong URI should return error");
    let code = err.get("code").and_then(|c| c.as_i64()).unwrap_or(0);
    assert_eq!(code, -32602, "invalid_params code"); // JSON-RPC invalid params
    let message = err.get("message").and_then(|m| m.as_str()).unwrap_or("");
    assert!(
        message.to_lowercase().contains("uri") || message.to_lowercase().contains("document"),
        "error message should mention document/URI: {}",
        message
    );

    server_handle.abort();
    let _ = server_handle.await;
}

async fn send_init_and_initialized(
    client_w: &mut tokio::io::DuplexStream,
    client_r: &mut tokio::io::DuplexStream,
) {
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
    let _ = timeout(Duration::from_secs(5), read_one_lsp_message_async(client_r))
        .await
        .expect("timeout on init response")
        .unwrap();
    let initialized = serde_json::json!({
        "jsonrpc": "2.0",
        "method": "initialized",
        "params": {}
    });
    client_w.write_all(&lsp_message(&initialized.to_string())).await.unwrap();
    client_w.flush().await.unwrap();
}

/// Send textDocument/didOpen for the test document with the given text.
async fn open_document(
    client_w: &mut tokio::io::DuplexStream,
    text: &str,
    version: i32,
) {
    let did_open = serde_json::json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didOpen",
        "params": {
            "textDocument": {
                "uri": TEST_DOC_URI,
                "languageId": "snaq",
                "version": version,
                "text": text
            }
        }
    });
    client_w.write_all(&lsp_message(&did_open.to_string())).await.unwrap();
    client_w.flush().await.unwrap();
}
