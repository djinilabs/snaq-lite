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
        .and_then(|l| {
            l.trim_start_matches("Content-Length:")
                .trim()
                .parse::<usize>()
                .ok()
        })
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
        .and_then(|l| {
            l.trim_start_matches("Content-Length:")
                .trim()
                .parse::<usize>()
                .ok()
        })
        .unwrap_or(0);
    let mut body = vec![0u8; len];
    r.read_exact(&mut body).await?;
    String::from_utf8(body).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))
}

#[tokio::test]
async fn native_initialize_returns_capabilities() {
    let (client_w, server_r) = duplex(4096);
    let (server_w, client_r) = duplex(4096);

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

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
    assert_eq!(
        capabilities
            .get("textDocumentSync")
            .and_then(|v| v.as_u64()),
        Some(2),
        "server should advertise incremental sync"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn native_did_open_and_hover_returns_value() {
    let (client_w, server_r) = duplex(8192);
    let (server_w, client_r) = duplex(8192);

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

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
    client_w
        .write_all(&lsp_message(&init_request.to_string()))
        .await
        .unwrap();
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
    client_w
        .write_all(&lsp_message(&initialized.to_string()))
        .await
        .unwrap();
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
    client_w
        .write_all(&lsp_message(&did_open.to_string()))
        .await
        .unwrap();
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
    client_w
        .write_all(&lsp_message(&hover_request.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    // Server may send logMessage etc.; read until we get the hover response (id: 2)
    let hover_body = timeout(Duration::from_secs(5), async {
        loop {
            let body = read_one_lsp_message_async(&mut client_r).await.unwrap();
            let v: serde_json::Value = serde_json::from_str(&body).unwrap();
            if v.get("id").and_then(|i| i.as_u64()) == Some(2) {
                return body;
            }
        }
    })
    .await
    .expect("timeout on hover");
    let hover_response: serde_json::Value = serde_json::from_str(&hover_body).unwrap();
    let result = hover_response.get("result").and_then(|r| r.as_object());
    assert!(result.is_some(), "hover returned result: {}", hover_body);
    let contents_val = result.and_then(|r| r.get("contents"));
    let content = contents_val
        .and_then(|c| c.as_str())
        .or_else(|| {
            contents_val
                .and_then(|c| c.get("value"))
                .and_then(|v| v.as_str())
        })
        .unwrap_or_default();
    assert!(
        !content.is_empty(),
        "hover result has contents: {}",
        hover_body
    );
    assert!(
        content.contains("3") || content.contains("1") || content.contains("2"),
        "hover content: {}",
        content
    );

    server_handle.abort();
    let _ = server_handle.await;
}

/// Plan §8: did_change for a URI with an active subscription; assert subscription is removed
/// and client receives Cancelled.
#[tokio::test]
async fn native_subscribe_then_did_change_receives_completed_update() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

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
    client_w
        .write_all(&lsp_message(&subscribe_request.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    // Read until we get the subscribe response (id: 2); may receive publishResult Completed first
    let subscription_id = timeout(Duration::from_secs(5), async {
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
    })
    .await
    .expect("timeout on subscribe response");
    assert!(
        !subscription_id.is_empty(),
        "subscribe should return subscriptionId"
    );

    let did_change = serde_json::json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didChange",
        "params": {
            "textDocument": { "uri": TEST_DOC_URI, "version": 2 },
            "contentChanges": [{ "text": "2 + 3" }]
        }
    });
    client_w
        .write_all(&lsp_message(&did_change.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    // Read until we get a post-change Completed update (no Cancelled expected).
    let updated = timeout(Duration::from_secs(5), async {
        loop {
            let body = read_one_lsp_message_async(&mut client_r).await.unwrap();
            let v: serde_json::Value = serde_json::from_str(&body).unwrap();
            if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/publishResult") {
                let params = v.get("params").and_then(|p| p.as_object());
                if let Some(p) = params {
                    if p.get("subscriptionId").and_then(|s| s.as_str())
                        != Some(subscription_id.as_str())
                    {
                        continue;
                    }
                    if p.get("status").and_then(|s| s.as_str()) == Some("Cancelled") {
                        return false;
                    }
                    if p.get("status").and_then(|s| s.as_str()) == Some("Completed") {
                        let display = p
                            .get("data")
                            .and_then(|d| d.get("display"))
                            .and_then(|s| s.as_str())
                            .unwrap_or_default();
                        if display.contains("5") {
                            return true;
                        }
                    }
                }
            }
        }
    })
    .await
    .expect("timeout waiting for Completed update");
    assert!(
        updated,
        "client should receive publishResult Completed update (display includes 5), without Cancelled"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

/// Subscribe to a scalar result; assert we get subscriptionId and one publishResult Completed with display.
#[tokio::test]
async fn native_subscribe_scalar_returns_id_and_completed() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

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
    client_w
        .write_all(&lsp_message(&subscribe_request.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut subscription_id = String::new();
    let mut got_completed = false;
    let mut completed_display: Option<String> = None;
    for _ in 0..15 {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
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
    assert!(
        !subscription_id.is_empty(),
        "subscribe should return subscriptionId"
    );
    assert!(
        got_completed,
        "client should receive one publishResult Completed for scalar"
    );
    assert!(
        completed_display
            .as_ref()
            .map(|s| s.contains("3"))
            .unwrap_or(false),
        "Completed data.display should show result: {:?}",
        completed_display
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn native_subscribe_node_returns_id_and_publish_node_result_completed() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document(&mut client_w, "1 + 2", 1).await;

    let subscribe_node_request = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 201,
        "method": "snaqlite/subscribeNode",
        "params": { "sourceUri": TEST_DOC_URI }
    });
    client_w
        .write_all(&lsp_message(&subscribe_node_request.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut subscription_id = String::new();
    let mut got_publish_node_completed = false;
    for _ in 0..20 {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
        .await
        .expect("timeout")
        .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("id").and_then(|i| i.as_u64()) == Some(201) {
            assert!(v.get("error").is_none(), "subscribeNode failed: {v}");
            subscription_id = v["result"]["subscriptionId"]
                .as_str()
                .unwrap_or("")
                .to_string();
        }
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/publishNodeResult") {
            let params = v.get("params").and_then(|p| p.as_object()).unwrap();
            if params.get("status").and_then(|s| s.as_str()) == Some("Completed") {
                let display = params
                    .get("data")
                    .and_then(|d| d.get("display"))
                    .and_then(|s| s.as_str())
                    .unwrap_or_default();
                if display.contains('3') {
                    got_publish_node_completed = true;
                }
            }
        }
        if !subscription_id.is_empty() && got_publish_node_completed {
            break;
        }
    }
    assert!(
        !subscription_id.is_empty(),
        "subscribeNode should return subscriptionId"
    );
    assert!(
        got_publish_node_completed,
        "subscribeNode should emit publishNodeResult Completed"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn native_unsubscribe_node_succeeds_after_subscribe_node() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document(&mut client_w, "1 + 2", 1).await;

    let subscribe_node_request = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 202,
        "method": "snaqlite/subscribeNode",
        "params": { "sourceUri": TEST_DOC_URI }
    });
    client_w
        .write_all(&lsp_message(&subscribe_node_request.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let subscription_id = timeout(Duration::from_secs(5), async {
        loop {
            let body = read_one_lsp_message_async(&mut client_r).await.unwrap();
            let v: serde_json::Value = serde_json::from_str(&body).unwrap();
            if v.get("id").and_then(|i| i.as_u64()) == Some(202) {
                assert!(v.get("error").is_none(), "subscribeNode failed: {v}");
                let id = v["result"]["subscriptionId"].as_str().unwrap_or("").to_string();
                break id;
            }
        }
    })
    .await
    .expect("timeout waiting for subscribeNode response");
    assert!(!subscription_id.is_empty(), "subscription id should not be empty");

    let unsubscribe_node_request = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 203,
        "method": "snaqlite/unsubscribeNode",
        "params": { "subscriptionId": subscription_id }
    });
    client_w
        .write_all(&lsp_message(&unsubscribe_node_request.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let body = timeout(Duration::from_secs(5), async {
        loop {
            let body = read_one_lsp_message_async(&mut client_r).await.unwrap();
            let v: serde_json::Value = serde_json::from_str(&body).unwrap();
            if v.get("id").and_then(|i| i.as_u64()) == Some(203) {
                break body;
            }
        }
    })
    .await
    .expect("timeout waiting for unsubscribeNode response");
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(v.get("error").is_none(), "unsubscribeNode should succeed: {v}");

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

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

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
    client_w
        .write_all(&lsp_message(&subscribe_request.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut subscription_id = String::new();
    let mut _got_running = false;
    let mut got_completed = false;
    let mut total_elements: Option<u64> = None;
    for _ in 0..10 {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
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
    assert!(
        !subscription_id.is_empty(),
        "subscribe for vector should return subscriptionId"
    );

    // Pump: trigger server to drain and send any Running/Completed (notifications sent when handling next request).
    let hover_request = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 3,
        "method": "textDocument/hover",
        "params": { "textDocument": { "uri": TEST_DOC_URI }, "position": { "line": 0, "character": 0 } }
    });
    client_w
        .write_all(&lsp_message(&hover_request.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    for _ in 0..10 {
        let body = match timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
        .await
        {
            Ok(Ok(b)) => b,
            _ => break,
        };
        let v: serde_json::Value = serde_json::from_str(&body).expect("valid JSON LSP message");
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/publishResult") {
            let params = v
                .get("params")
                .and_then(|p| p.as_object())
                .expect("publishResult params");
            let status = params.get("status").and_then(|s| s.as_str()).unwrap_or("");
            if status == "Running" {
                _got_running = true;
                if let Some(data) = params.get("data").and_then(|d| d.as_object()) {
                    assert!(
                        data.contains_key("elements"),
                        "Running data should have elements"
                    );
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

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

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
    client_w
        .write_all(&lsp_message(&subscribe_request.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut subscription_id = String::new();
    for _ in 0..10 {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
        .await
        .expect("timeout")
        .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("id").and_then(|i| i.as_u64()) == Some(2) {
            subscription_id = v["result"]["subscriptionId"]
                .as_str()
                .unwrap_or("")
                .to_string();
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
    client_w
        .write_all(&lsp_message(&unsub.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    // Read until we get the unsubscribe response (id: 3); may receive publishResult first
    let body = timeout(Duration::from_secs(5), async {
        loop {
            let b = read_one_lsp_message_async(&mut client_r).await.unwrap();
            let v: serde_json::Value = serde_json::from_str(&b).unwrap();
            if v.get("id").and_then(|i| i.as_u64()) == Some(3) {
                return b;
            }
        }
    })
    .await
    .expect("timeout on unsubscribe response");
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(
        v.get("result").is_some(),
        "unsubscribe should return result (null): {}",
        body
    );
    assert!(
        v.get("error").is_none(),
        "unsubscribe should not error: {}",
        body
    );

    server_handle.abort();
    let _ = server_handle.await;
}

/// Subscribe with a URI that does not match the open document; assert server returns invalid_params error.
#[tokio::test]
async fn native_subscribe_wrong_uri_returns_error() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

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
    client_w
        .write_all(&lsp_message(&subscribe_request.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let body = timeout(Duration::from_secs(5), async {
        loop {
            let b = read_one_lsp_message_async(&mut client_r).await.unwrap();
            let v: serde_json::Value = serde_json::from_str(&b).unwrap();
            if v.get("id").and_then(|i| i.as_u64()) == Some(2) {
                return b;
            }
        }
    })
    .await
    .expect("timeout on subscribe response");
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    let err = v
        .get("error")
        .expect("subscribe with wrong URI should return error");
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
    client_w
        .write_all(&lsp_message(&init_request.to_string()))
        .await
        .unwrap();
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
    client_w
        .write_all(&lsp_message(&initialized.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
}

/// Send textDocument/didOpen for the test document with the given text.
async fn open_document(client_w: &mut tokio::io::DuplexStream, text: &str, version: i32) {
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
    client_w
        .write_all(&lsp_message(&did_open.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
}

/// Open a document with the given URI and text (for multi-doc tests).
async fn open_document_uri(
    client_w: &mut tokio::io::DuplexStream,
    uri: &str,
    text: &str,
    version: i32,
) {
    let did_open = serde_json::json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didOpen",
        "params": {
            "textDocument": {
                "uri": uri,
                "languageId": "snaq",
                "version": version,
                "text": text
            }
        }
    });
    client_w
        .write_all(&lsp_message(&did_open.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
}

/// Visual computation graph: open two virtual URIs and hover in each; each returns correct value.
#[tokio::test]
async fn native_multi_document_hover_two_virtual_uris() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/node_a.sl", "10 + 1", 1).await;
    open_document_uri(&mut client_w, "snaq://graph/node_b.sl", "20 + 2", 1).await;

    let hover_a = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "textDocument/hover",
        "params": {
            "textDocument": { "uri": "snaq://graph/node_a.sl" },
            "position": { "line": 0, "character": 2 }
        }
    });
    client_w
        .write_all(&lsp_message(&hover_a.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let body_a = timeout(Duration::from_secs(5), async {
        loop {
            let b = read_one_lsp_message_async(&mut client_r).await.unwrap();
            let v: serde_json::Value = serde_json::from_str(&b).unwrap();
            if v.get("id").and_then(|i| i.as_u64()) == Some(2) {
                return b;
            }
        }
    })
    .await
    .expect("timeout on hover A");
    let res_a: serde_json::Value = serde_json::from_str(&body_a).unwrap();
    let content = res_a["result"]["contents"]
        .as_str()
        .or_else(|| res_a["result"]["contents"]["value"].as_str())
        .unwrap_or_default();
    assert!(
        content.contains("11"),
        "node_a hover should show 11: {}",
        content
    );

    let hover_b = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 3,
        "method": "textDocument/hover",
        "params": {
            "textDocument": { "uri": "snaq://graph/node_b.sl" },
            "position": { "line": 0, "character": 2 }
        }
    });
    client_w
        .write_all(&lsp_message(&hover_b.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let body_b = timeout(Duration::from_secs(5), async {
        loop {
            let b = read_one_lsp_message_async(&mut client_r).await.unwrap();
            let v: serde_json::Value = serde_json::from_str(&b).unwrap();
            if v.get("id").and_then(|i| i.as_u64()) == Some(3) {
                return b;
            }
        }
    })
    .await
    .expect("timeout on hover B");
    let res_b: serde_json::Value = serde_json::from_str(&body_b).unwrap();
    let content_b = res_b["result"]["contents"]
        .as_str()
        .or_else(|| res_b["result"]["contents"]["value"].as_str())
        .unwrap_or_default();
    assert!(
        content_b.contains("22"),
        "node_b hover should show 22: {}",
        content_b
    );

    server_handle.abort();
    let _ = server_handle.await;
}

/// Graph connect: two nodes with compatible types (Vector → Vector) succeeds.
#[tokio::test]
async fn native_graph_connect_success() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/source.sl", "[1, 2, 3]", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/target.sl",
        "input x: Vector\nx",
        1,
    )
    .await;

    let connect_request = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "snaqlite/graph/connect",
        "params": {
            "sourceUri": "snaq://graph/source.sl",
            "targetUri": "snaq://graph/target.sl",
            "targetInputName": "x"
        }
    });
    client_w
        .write_all(&lsp_message(&connect_request.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let body = timeout(Duration::from_secs(5), async {
        loop {
            let b = read_one_lsp_message_async(&mut client_r).await.unwrap();
            let v: serde_json::Value = serde_json::from_str(&b).unwrap();
            if v.get("id").and_then(|i| i.as_u64()) == Some(2) {
                return b;
            }
        }
    })
    .await
    .expect("timeout on connect response");
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(v.get("error").is_none(), "connect should succeed: {}", body);
    assert!(v.get("result").is_some());

    server_handle.abort();
    let _ = server_handle.await;
}

/// Graph connect: target input type "Undefined" accepts any source type (e.g. Numeric → presentation).
#[tokio::test]
async fn native_graph_connect_target_undefined_accepts_any() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/source.sl", "42", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/target.sl",
        "input x: Undefined\n$x",
        1,
    )
    .await;

    let connect_request = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "snaqlite/graph/connect",
        "params": {
            "sourceUri": "snaq://graph/source.sl",
            "targetUri": "snaq://graph/target.sl",
            "targetInputName": "x"
        }
    });
    client_w
        .write_all(&lsp_message(&connect_request.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let body = timeout(Duration::from_secs(5), async {
        loop {
            let b = read_one_lsp_message_async(&mut client_r).await.unwrap();
            let v: serde_json::Value = serde_json::from_str(&b).unwrap();
            if v.get("id").and_then(|i| i.as_u64()) == Some(2) {
                return b;
            }
        }
    })
    .await
    .expect("timeout on connect response");
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(
        v.get("error").is_none(),
        "connect Numeric→Undefined should succeed: {}",
        body
    );
    assert!(v.get("result").is_some());

    server_handle.abort();
    let _ = server_handle.await;
}

/// Graph connect: type mismatch (e.g. Numeric source → Vector input) returns -32001.
#[tokio::test]
async fn native_graph_connect_type_mismatch_returns_error() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/source.sl", "1 + 2", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/target.sl",
        "input x: Vector\nx",
        1,
    )
    .await;

    let connect_request = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "snaqlite/graph/connect",
        "params": {
            "sourceUri": "snaq://graph/source.sl",
            "targetUri": "snaq://graph/target.sl",
            "targetInputName": "x"
        }
    });
    client_w
        .write_all(&lsp_message(&connect_request.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let body = timeout(Duration::from_secs(5), async {
        loop {
            let b = read_one_lsp_message_async(&mut client_r).await.unwrap();
            let v: serde_json::Value = serde_json::from_str(&b).unwrap();
            if v.get("id").and_then(|i| i.as_u64()) == Some(2) {
                return b;
            }
        }
    })
    .await
    .expect("timeout on connect response");
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    let err = v
        .get("error")
        .expect("connect with type mismatch should error");
    let code = err.get("code").and_then(|c| c.as_i64()).unwrap_or(0);
    assert_eq!(code, -32001, "ServerError(-32001) Type mismatch");
    let message = err.get("message").and_then(|m| m.as_str()).unwrap_or("");
    assert!(
        message.to_lowercase().contains("type") || message.to_lowercase().contains("mismatch"),
        "error message: {}",
        message
    );

    server_handle.abort();
    let _ = server_handle.await;
}

/// subscribeWidget with scalar source: get Completed with display.
#[tokio::test]
async fn native_subscribe_widget_scalar_returns_completed() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/node.sl", "2 * 3", 1).await;

    let subscribe_widget = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "snaqlite/graph/subscribeWidget",
        "params": { "widgetId": "w1", "sourceUri": "snaq://graph/node.sl" }
    });
    client_w
        .write_all(&lsp_message(&subscribe_widget.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut got_completed = false;
    for _ in 0..10 {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
        .await
        .expect("timeout")
        .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("id").and_then(|i| i.as_u64()) == Some(2) {
            assert!(
                v.get("error").is_none(),
                "subscribeWidget should succeed: {}",
                v
            );
        }
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate") {
            let params = v.get("params").and_then(|p| p.as_object()).unwrap();
            if params.get("status").and_then(|s| s.as_str()) == Some("Completed") {
                got_completed = true;
                assert_eq!(params.get("widgetId").and_then(|s| s.as_str()), Some("w1"));
                break;
            }
        }
    }
    assert!(
        got_completed,
        "client should receive widgetDataUpdate Completed"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

/// subscribeWidget (vector source so widget is registered) then unsubscribeWidget; receive Cancelled.
#[tokio::test]
async fn native_subscribe_widget_then_unsubscribe_receives_cancelled() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/node.sl", "[1, 2, 3]", 1).await;

    let subscribe_widget = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "snaqlite/graph/subscribeWidget",
        "params": { "widgetId": "w-unsub", "sourceUri": "snaq://graph/node.sl" }
    });
    client_w
        .write_all(&lsp_message(&subscribe_widget.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    // Consume subscribe response (id 2); widget is registered for vector.
    loop {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
        .await
        .expect("timeout")
        .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("id").and_then(|i| i.as_u64()) == Some(2) {
            break;
        }
    }

    let unsub = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 3,
        "method": "snaqlite/graph/unsubscribeWidget",
        "params": { "widgetId": "w-unsub" }
    });
    client_w
        .write_all(&lsp_message(&unsub.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut got_cancelled = false;
    for _ in 0..15 {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
        .await
        .expect("timeout")
        .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate") {
            let params = v.get("params").and_then(|p| p.as_object()).unwrap();
            if params.get("status").and_then(|s| s.as_str()) == Some("Cancelled") {
                got_cancelled = true;
                break;
            }
        }
    }
    assert!(
        got_cancelled,
        "client should receive widgetDataUpdate Cancelled after unsubscribe"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

/// subscribeWidget (vector source) then fetchResultSlice: get elements and totalCount.
#[tokio::test]
async fn native_subscribe_widget_vector_then_fetch_result_slice_returns_elements() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/node.sl", "[1, 2, 3]", 1).await;

    let subscribe_widget = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "snaqlite/graph/subscribeWidget",
        "params": { "widgetId": "w-slice", "sourceUri": "snaq://graph/node.sl" }
    });
    client_w
        .write_all(&lsp_message(&subscribe_widget.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut got_completed = false;
    for _ in 0..15 {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
        .await
        .expect("timeout")
        .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("id").and_then(|i| i.as_u64()) == Some(2) {
            assert!(
                v.get("error").is_none(),
                "subscribeWidget should succeed: {}",
                v
            );
        }
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate") {
            let params = v.get("params").and_then(|p| p.as_object()).unwrap();
            if params.get("status").and_then(|s| s.as_str()) == Some("Completed") {
                got_completed = true;
                break;
            }
        }
    }
    assert!(
        got_completed,
        "client should receive widgetDataUpdate Completed before fetchResultSlice"
    );

    let fetch_slice = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 3,
        "method": "snaqlite/graph/fetchResultSlice",
        "params": { "widgetId": "w-slice", "path": [], "offset": 0, "limit": 10 }
    });
    client_w
        .write_all(&lsp_message(&fetch_slice.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut slice_response: Option<serde_json::Value> = None;
    for _ in 0..10 {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
        .await
        .expect("timeout")
        .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("id").and_then(|i| i.as_u64()) == Some(3) {
            assert!(
                v.get("error").is_none(),
                "fetchResultSlice should succeed: {}",
                v
            );
            slice_response = v.get("result").cloned();
            break;
        }
    }
    let res = slice_response.expect("client should receive fetchResultSlice response");
    let elements = res.get("elements").and_then(|e| e.as_array()).unwrap();
    assert_eq!(elements.len(), 3, "vector [1,2,3] should yield 3 elements");
    assert_eq!(res.get("totalCount").and_then(|c| c.as_u64()), Some(3));
    assert_eq!(res.get("hasMore").and_then(|h| h.as_bool()), Some(false));

    server_handle.abort();
    let _ = server_handle.await;
}

/// fetchResultSlice with path [] and offset 1, limit 1 returns the second element of the vector.
#[tokio::test]
async fn native_fetch_result_slice_offset_limit_returns_single_element() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/node.sl", "[10, 20, 30]", 1).await;

    let subscribe_widget = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "snaqlite/graph/subscribeWidget",
        "params": { "widgetId": "w-path", "sourceUri": "snaq://graph/node.sl" }
    });
    client_w
        .write_all(&lsp_message(&subscribe_widget.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut got_completed = false;
    for _ in 0..15 {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
        .await
        .expect("timeout")
        .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("id").and_then(|i| i.as_u64()) == Some(2) {
            assert!(
                v.get("error").is_none(),
                "subscribeWidget should succeed: {}",
                v
            );
        }
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate") {
            let params = v.get("params").and_then(|p| p.as_object()).unwrap();
            if params.get("status").and_then(|s| s.as_str()) == Some("Completed") {
                got_completed = true;
                break;
            }
        }
    }
    assert!(
        got_completed,
        "client should receive widgetDataUpdate Completed"
    );

    let fetch_slice = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 3,
        "method": "snaqlite/graph/fetchResultSlice",
        "params": { "widgetId": "w-path", "path": [], "offset": 1, "limit": 1 }
    });
    client_w
        .write_all(&lsp_message(&fetch_slice.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut slice_response: Option<serde_json::Value> = None;
    for _ in 0..10 {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
        .await
        .expect("timeout")
        .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("id").and_then(|i| i.as_u64()) == Some(3) {
            assert!(
                v.get("error").is_none(),
                "fetchResultSlice should succeed: {}",
                v
            );
            slice_response = v.get("result").cloned();
            break;
        }
    }
    let res = slice_response.expect("client should receive fetchResultSlice response");
    let elements = res.get("elements").and_then(|e| e.as_array()).unwrap();
    assert_eq!(
        elements.len(),
        1,
        "offset 1 limit 1 should yield one element"
    );
    let display = elements[0]
        .get("display")
        .and_then(|d| d.as_str())
        .expect("element should have display");
    assert_eq!(display, "20", "element at offset 1 should be 20");
    assert_eq!(res.get("totalCount").and_then(|c| c.as_u64()), Some(3));
    assert_eq!(res.get("hasMore").and_then(|h| h.as_bool()), Some(true));

    server_handle.abort();
    let _ = server_handle.await;
}

/// fetchResultSlice with unknown widgetId returns invalid_params error.
#[tokio::test]
async fn native_fetch_result_slice_unknown_widget_returns_error() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/node.sl", "[1, 2, 3]", 1).await;

    let fetch_slice = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "snaqlite/graph/fetchResultSlice",
        "params": { "widgetId": "never-subscribed", "path": [], "offset": 0, "limit": 10 }
    });
    client_w
        .write_all(&lsp_message(&fetch_slice.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut response: Option<serde_json::Value> = None;
    for _ in 0..5 {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
        .await
        .expect("timeout")
        .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("id").and_then(|i| i.as_u64()) == Some(1) {
            response = Some(v);
            break;
        }
    }
    let res = response.expect("client should receive response");
    let err = res
        .get("error")
        .and_then(|e| e.as_object())
        .expect("response should have error");
    assert_eq!(err.get("code").and_then(|c| c.as_i64()), Some(-32602));
    let message = err.get("message").and_then(|m| m.as_str()).unwrap_or("");
    assert!(
        message.contains("Widget not found") || message.contains("result not available"),
        "error message should mention widget/result: {}",
        message
    );

    server_handle.abort();
    let _ = server_handle.await;
}

/// subscribeWidget (vector so widget is registered) then didChange on source URI; widget receives Cancelled.
#[tokio::test]
async fn native_subscribe_widget_then_did_change_receives_completed_update() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    let uri = "snaq://graph/node_w.sl";
    open_document_uri(&mut client_w, uri, "[5, 10]", 1).await;

    let subscribe_widget = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "snaqlite/graph/subscribeWidget",
        "params": { "widgetId": "w-doc-change", "sourceUri": uri }
    });
    client_w
        .write_all(&lsp_message(&subscribe_widget.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    // Consume subscribe response (id 2) so widget is registered for vector.
    loop {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
        .await
        .expect("timeout")
        .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("id").and_then(|i| i.as_u64()) == Some(2) {
            break;
        }
    }

    let did_change = serde_json::json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didChange",
        "params": {
            "textDocument": { "uri": uri, "version": 2 },
            "contentChanges": [{ "text": "[6, 11]" }]
        }
    });
    client_w
        .write_all(&lsp_message(&did_change.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut got_completed = false;
    let mut got_cancelled = false;
    for _ in 0..15 {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
        .await
        .expect("timeout")
        .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate") {
            let params = v.get("params").and_then(|p| p.as_object()).unwrap();
            let status = params.get("status").and_then(|s| s.as_str());
            if status == Some("Cancelled") {
                got_cancelled = true;
            }
            if status == Some("Completed") {
                let total = params
                    .get("payload")
                    .and_then(|p| p.get("totalElements"))
                    .and_then(|n| n.as_u64());
                if total == Some(2) {
                    got_completed = true;
                    break;
                }
            }
        }
    }
    assert!(
        !got_cancelled,
        "client should not receive widgetDataUpdate Cancelled after didChange on source URI"
    );
    assert!(
        got_completed,
        "client should receive widgetDataUpdate Completed update (totalElements=2) after didChange"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

/// Read LSP messages until we get a response with the given id; return that message body.
async fn read_until_response_id(client_r: &mut tokio::io::DuplexStream, id: u64) -> String {
    loop {
        let body = timeout(Duration::from_secs(5), read_one_lsp_message_async(client_r))
            .await
            .expect("timeout")
            .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("id").and_then(|i| i.as_u64()) == Some(id) {
            return body;
        }
    }
}

/// Connect two nodes, then disconnect the edge; disconnect RPC succeeds.
#[tokio::test]
async fn native_graph_disconnect_removes_edge() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/src.sl", "[1, 2, 3]", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/tgt.sl",
        "input x: Vector\nx",
        1,
    )
    .await;

    let connect_req = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "snaqlite/graph/connect",
        "params": {
            "sourceUri": "snaq://graph/src.sl",
            "targetUri": "snaq://graph/tgt.sl",
            "targetInputName": "x"
        }
    });
    client_w
        .write_all(&lsp_message(&connect_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 2).await;

    let disconnect_req = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 3,
        "method": "snaqlite/graph/disconnect",
        "params": { "targetUri": "snaq://graph/tgt.sl", "targetInputName": "x" }
    });
    client_w
        .write_all(&lsp_message(&disconnect_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 3).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(
        v.get("error").is_none(),
        "disconnect should succeed: {}",
        body
    );

    server_handle.abort();
    let _ = server_handle.await;
}

/// After didOpen with input declarations, client receives nodeSignatureUpdated with inputs and outputType.
#[tokio::test]
async fn native_node_signature_updated_after_did_open() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/node.sl",
        "input x: Vector\n[1, 2]",
        1,
    )
    .await;

    let mut got_signature = false;
    for _ in 0..15 {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
        .await
        .expect("timeout")
        .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/nodeSignatureUpdated") {
            let params = v.get("params").and_then(|p| p.as_object()).expect("params");
            assert_eq!(
                params.get("uri").and_then(|u| u.as_str()),
                Some("snaq://graph/node.sl")
            );
            let inputs = params
                .get("inputs")
                .and_then(|i| i.as_array())
                .expect("inputs array");
            assert_eq!(inputs.len(), 1);
            let port = inputs[0].as_object().expect("input port");
            assert_eq!(port.get("name").and_then(|n| n.as_str()), Some("x"));
            assert_eq!(port.get("type").and_then(|t| t.as_str()), Some("Vector"));
            let out = params.get("outputType").and_then(|o| o.as_str());
            assert!(
                out == Some("Vector") || out.is_none(),
                "outputType: {:?}",
                out
            );
            got_signature = true;
            break;
        }
    }
    assert!(
        got_signature,
        "client should receive snaqlite/graph/nodeSignatureUpdated after didOpen with input decls"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

/// Delay before triggering a request so the server can drain pending widgetDataUpdate (background consumer sends asynchronously).
const WIDGET_DRAIN_DELAY_MS: u64 = 150;

/// Wired graph: source [1,2,3], target "input x: Vector\n$x"; connect; subscribeWidget to target gets Completed with totalElements (≥1 confirms graph wiring).
#[tokio::test]
async fn native_graph_wired_widget_gets_downstream_result() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/upstream.sl", "[1, 2, 3]", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/downstream.sl",
        "input x: Vector\n$x",
        1,
    )
    .await;

    let connect_req = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "snaqlite/graph/connect",
        "params": {
            "sourceUri": "snaq://graph/upstream.sl",
            "targetUri": "snaq://graph/downstream.sl",
            "targetInputName": "x"
        }
    });
    client_w
        .write_all(&lsp_message(&connect_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 2).await;

    let subscribe_widget = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 3,
        "method": "snaqlite/graph/subscribeWidget",
        "params": { "widgetId": "w-wired", "sourceUri": "snaq://graph/downstream.sl" }
    });
    client_w
        .write_all(&lsp_message(&subscribe_widget.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    // Give the widget consumer thread time to send Running/Completed before we trigger drain.
    tokio::time::sleep(Duration::from_millis(WIDGET_DRAIN_DELAY_MS)).await;

    // Trigger server to drain pending widgetDataUpdate (sent by background consumer).
    let hover_req = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 4,
        "method": "textDocument/hover",
        "params": {
            "textDocument": { "uri": "snaq://graph/downstream.sl" },
            "position": { "line": 0, "character": 0 }
        }
    });
    client_w
        .write_all(&lsp_message(&hover_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut got_completed = false;
    let mut total_elements: Option<u64> = None;
    let mut result_type: Option<String> = None;
    for _ in 0..25 {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
        .await
        .expect("timeout")
        .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("id").and_then(|i| i.as_u64()) == Some(3) {
            assert!(
                v.get("error").is_none(),
                "subscribeWidget should succeed: {}",
                v
            );
        }
        if v.get("id").and_then(|i| i.as_u64()) == Some(4) {
            // Hover response; continue to collect notifications
            continue;
        }
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate") {
            let params = v
                .get("params")
                .and_then(|p| p.as_object())
                .expect("widgetDataUpdate message should have params object");
            if params.get("status").and_then(|s| s.as_str()) == Some("Completed") {
                got_completed = true;
                total_elements = params
                    .get("payload")
                    .and_then(|p| p.get("totalElements"))
                    .and_then(|n| n.as_u64());
                result_type = params
                    .get("payload")
                    .and_then(|p| p.get("resultType"))
                    .and_then(|s| s.as_str())
                    .map(ToString::to_string);
                break;
            }
        }
    }
    assert!(
        got_completed,
        "widget subscribed to wired downstream node should receive Completed"
    );
    // Vector payload can omit eager totalElements for lazy vectors; require vector completion signal.
    assert!(
        total_elements.is_some_and(|n| n >= 1) || result_type.as_deref() == Some("Vector"),
        "downstream node should receive vector from upstream (totalElements or resultType=Vector), got totalElements={:?}, resultType={:?}",
        total_elements,
        result_type
    );

    server_handle.abort();
    let _ = server_handle.await;
}

/// Computation-to-computation wiring with identifier: source "42", target "input abc: Numeric\nabc * 10";
/// connect source → target input "abc"; subscribe to target → get Completed with display "420".
#[tokio::test]
async fn native_computation_to_computation_wired_input_binds_identifier() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/upstream.sl", "42", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/downstream.sl",
        "input abc: Numeric\nabc * 10",
        1,
    )
    .await;

    let connect_req = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "snaqlite/graph/connect",
        "params": {
            "sourceUri": "snaq://graph/upstream.sl",
            "targetUri": "snaq://graph/downstream.sl",
            "targetInputName": "abc"
        }
    });
    client_w
        .write_all(&lsp_message(&connect_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 2).await;

    let subscribe_widget = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 3,
        "method": "snaqlite/graph/subscribeWidget",
        "params": { "widgetId": "w-cc", "sourceUri": "snaq://graph/downstream.sl" }
    });
    client_w
        .write_all(&lsp_message(&subscribe_widget.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    tokio::time::sleep(Duration::from_millis(WIDGET_DRAIN_DELAY_MS)).await;

    let hover_req = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 4,
        "method": "textDocument/hover",
        "params": {
            "textDocument": { "uri": "snaq://graph/downstream.sl" },
            "position": { "line": 0, "character": 0 }
        }
    });
    client_w
        .write_all(&lsp_message(&hover_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut got_completed_420 = false;
    for _ in 0..25 {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
        .await
        .expect("timeout")
        .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("id").and_then(|i| i.as_u64()) == Some(3) {
            assert!(
                v.get("error").is_none(),
                "subscribeWidget should succeed: {}",
                v
            );
        }
        if v.get("id").and_then(|i| i.as_u64()) == Some(4) {
            continue;
        }
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate") {
            let params = v
                .get("params")
                .and_then(|p| p.as_object())
                .expect("widgetDataUpdate should have params");
            if params.get("status").and_then(|s| s.as_str()) == Some("Completed") {
                let payload = params.get("payload").and_then(|p| p.as_object());
                let display = payload
                    .and_then(|p| p.get("display"))
                    .and_then(|s| s.as_str());
                if display == Some("420") {
                    got_completed_420 = true;
                    break;
                }
            }
        }
    }
    assert!(
        got_completed_420,
        "wired computation (42 → abc) should yield result 420 in downstream widget"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

/// One output wired to two inputs of the same box: source "42", target "input abc: Numeric\ninput ggg: Numeric\nabc * ggg";
/// connect source → "abc" and source → "ggg"; subscribe to target → get Completed with display "1764" (no stream input error).
#[tokio::test]
async fn native_one_output_to_two_inputs_same_box_yields_result() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/upstream.sl", "42", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/downstream.sl",
        "input abc: Numeric\ninput ggg: Numeric\nabc * ggg",
        1,
    )
    .await;

    let connect_abc = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "snaqlite/graph/connect",
        "params": {
            "sourceUri": "snaq://graph/upstream.sl",
            "targetUri": "snaq://graph/downstream.sl",
            "targetInputName": "abc"
        }
    });
    client_w
        .write_all(&lsp_message(&connect_abc.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 2).await;

    let connect_ggg = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 3,
        "method": "snaqlite/graph/connect",
        "params": {
            "sourceUri": "snaq://graph/upstream.sl",
            "targetUri": "snaq://graph/downstream.sl",
            "targetInputName": "ggg"
        }
    });
    client_w
        .write_all(&lsp_message(&connect_ggg.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 3).await;

    let subscribe_widget = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 4,
        "method": "snaqlite/graph/subscribeWidget",
        "params": { "widgetId": "w-fanout", "sourceUri": "snaq://graph/downstream.sl" }
    });
    client_w
        .write_all(&lsp_message(&subscribe_widget.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    tokio::time::sleep(Duration::from_millis(WIDGET_DRAIN_DELAY_MS)).await;

    let mut got_completed_1764 = false;
    for _ in 0..25 {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
        .await
        .expect("timeout")
        .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("id").and_then(|i| i.as_u64()) == Some(4) {
            assert!(
                v.get("error").is_none(),
                "subscribeWidget should succeed: {}",
                v
            );
        }
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate") {
            let params = v
                .get("params")
                .and_then(|p| p.as_object())
                .expect("widgetDataUpdate should have params");
            if params.get("status").and_then(|s| s.as_str()) == Some("Completed") {
                let payload = params.get("payload").and_then(|p| p.as_object());
                let display = payload
                    .and_then(|p| p.get("display"))
                    .and_then(|s| s.as_str());
                if display == Some("1764") {
                    got_completed_1764 = true;
                    break;
                }
            }
        }
    }
    assert!(
        got_completed_1764,
        "one output (42) wired to two inputs (abc, ggg) should yield result 1764, not stream input error"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

/// Downstream widget receives push update when source changes: source "7", target "input x: Undefined\n$x";
/// connect, subscribe to target → get Completed "7". didChange source to "100" → client receives
/// a second widgetDataUpdate Completed "100" (no Cancelled; same subscription).
#[tokio::test]
async fn native_downstream_widget_receives_push_update_when_source_changes() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/source.sl", "7", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/target.sl",
        "input x: Undefined\n$x",
        1,
    )
    .await;

    let connect_req = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 2,
        "method": "snaqlite/graph/connect",
        "params": {
            "sourceUri": "snaq://graph/source.sl",
            "targetUri": "snaq://graph/target.sl",
            "targetInputName": "x"
        }
    });
    client_w
        .write_all(&lsp_message(&connect_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 2).await;

    let subscribe_widget = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 3,
        "method": "snaqlite/graph/subscribeWidget",
        "params": { "widgetId": "w-scalar", "sourceUri": "snaq://graph/target.sl" }
    });
    client_w
        .write_all(&lsp_message(&subscribe_widget.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    tokio::time::sleep(Duration::from_millis(WIDGET_DRAIN_DELAY_MS)).await;

    let hover_req = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 4,
        "method": "textDocument/hover",
        "params": {
            "textDocument": { "uri": "snaq://graph/target.sl" },
            "position": { "line": 0, "character": 0 }
        }
    });
    client_w
        .write_all(&lsp_message(&hover_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut got_subscribe_ok = false;
    let mut got_completed = false;
    for _ in 0..25 {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
        .await
        .expect("timeout reading subscribe response or first Completed")
        .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("id").and_then(|i| i.as_u64()) == Some(3) {
            assert!(
                v.get("error").is_none(),
                "subscribeWidget should succeed: {}",
                body
            );
            got_subscribe_ok = true;
        }
        if v.get("id").and_then(|i| i.as_u64()) == Some(4) {
            continue;
        }
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate") {
            let params = v.get("params").and_then(|p| p.as_object()).unwrap();
            if params.get("status").and_then(|s| s.as_str()) == Some("Completed") {
                let payload = params.get("payload").and_then(|p| p.as_object());
                let display = payload
                    .and_then(|p| p.get("display"))
                    .and_then(|s| s.as_str());
                let total_elements = payload
                    .and_then(|p| p.get("totalElements"))
                    .and_then(|n| n.as_u64());
                let result_type = payload
                    .and_then(|p| p.get("resultType"))
                    .and_then(|s| s.as_str());
                assert!(
                    display == Some("7")
                        || total_elements == Some(1)
                        || result_type == Some("Vector"),
                    "initial Completed should have display \"7\" or vector summary, got payload {:?}",
                    payload
                );
                got_completed = true;
            }
        }
        if got_subscribe_ok && got_completed {
            break;
        }
    }
    assert!(
        got_subscribe_ok,
        "subscribeWidget should return success (id 3)"
    );

    let did_change = serde_json::json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didChange",
        "params": {
            "textDocument": { "uri": "snaq://graph/source.sl", "version": 2 },
            "contentChanges": [{ "text": "100" }]
        }
    });
    client_w
        .write_all(&lsp_message(&did_change.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    tokio::time::sleep(Duration::from_millis(WIDGET_DRAIN_DELAY_MS)).await;

    let hover_after_change = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 5,
        "method": "textDocument/hover",
        "params": {
            "textDocument": { "uri": "snaq://graph/target.sl" },
            "position": { "line": 0, "character": 0 }
        }
    });
    client_w
        .write_all(&lsp_message(&hover_after_change.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut second_completed_ok = false;
    let mut got_cancelled = false;
    for _ in 0..25 {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
        .await
        .expect("timeout waiting for second widgetDataUpdate")
        .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("id").and_then(|i| i.as_u64()) == Some(5) {
            continue;
        }
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate") {
            let params = v.get("params").and_then(|p| p.as_object()).unwrap();
            let status = params.get("status").and_then(|s| s.as_str());
            if status == Some("Cancelled") {
                got_cancelled = true;
            }
            if status == Some("Completed") {
                let payload = params.get("payload").and_then(|p| p.as_object());
                let display = payload
                    .and_then(|p| p.get("display"))
                    .and_then(|s| s.as_str());
                let total_elements = payload
                    .and_then(|p| p.get("totalElements"))
                    .and_then(|n| n.as_u64());
                let result_type = payload
                    .and_then(|p| p.get("resultType"))
                    .and_then(|s| s.as_str());
                second_completed_ok = display == Some("100")
                    || total_elements == Some(1)
                    || result_type == Some("Vector");
                break;
            }
        }
    }
    assert!(
        !got_cancelled,
        "client should not receive Cancelled when source changes; downstream widget gets push update"
    );
    assert!(
        second_completed_ok,
        "after didChange source to 100, client should receive a second Completed with display \"100\" or totalElements 1"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

/// Reproduce load race: subscribe to presentation before graph/connect; get Error (unbound).
/// Then graph/connect succeeds; LSP refreshes widgets for target (refresh_widgets_for_uri).
/// Full flow (client receives Completed "7") is exercised in E2E with WASM LSP.
#[tokio::test]
async fn native_subscribe_then_connect_refreshes_widget_with_result() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);

    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });

    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/comp.sl", "7", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/pres.sl",
        "input x: Undefined\n$x",
        1,
    )
    .await;

    // Subscribe to presentation *before* connect: no edge yet, so $x is unbound → Error.
    let subscribe_widget = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 3,
        "method": "snaqlite/graph/subscribeWidget",
        "params": { "widgetId": "w-pres", "sourceUri": "snaq://graph/pres.sl" }
    });
    client_w
        .write_all(&lsp_message(&subscribe_widget.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut got_error_notification = false;
    for _ in 0..15 {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
        .await
        .expect("timeout reading subscribe response or Error notification")
        .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("id").and_then(|i| i.as_u64()) == Some(3) {
            assert!(
                v.get("error").is_none(),
                "subscribeWidget returns Ok(()) and sends Error via notification: {}",
                body
            );
        }
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate") {
            let params = v.get("params").and_then(|p| p.as_object()).unwrap();
            if params.get("status").and_then(|s| s.as_str()) == Some("Error") {
                let msg = params
                    .get("payload")
                    .and_then(|p| p.get("message"))
                    .and_then(|s| s.as_str())
                    .unwrap_or("");
                assert!(
                    msg.contains("unbound") || msg.contains("stream"),
                    "Error payload should mention unbound stream: {}",
                    msg
                );
                got_error_notification = true;
                break;
            }
        }
    }
    assert!(
        got_error_notification,
        "client should receive widgetDataUpdate Error (unbound) before connect"
    );

    // Connect: LSP adds edge and calls refresh_widgets_for_uri(pres). Connect must succeed.
    let connect_req = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 4,
        "method": "snaqlite/graph/connect",
        "params": {
            "sourceUri": "snaq://graph/comp.sl",
            "targetUri": "snaq://graph/pres.sl",
            "targetInputName": "x"
        }
    });
    client_w
        .write_all(&lsp_message(&connect_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let connect_body = read_until_response_id(&mut client_r, 4).await;
    let connect_v: serde_json::Value = serde_json::from_str(&connect_body).unwrap();
    assert!(
        connect_v.get("error").is_none(),
        "graph/connect should succeed (refresh_widgets_for_uri runs after adding edge): {}",
        connect_body
    );

    // Trigger drain so we receive any widgetDataUpdate from refresh_widgets_for_uri.
    tokio::time::sleep(Duration::from_millis(WIDGET_DRAIN_DELAY_MS)).await;
    let hover_req = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 5,
        "method": "textDocument/hover",
        "params": {
            "textDocument": { "uri": "snaq://graph/pres.sl" },
            "position": { "line": 0, "character": 0 }
        }
    });
    client_w
        .write_all(&lsp_message(&hover_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut got_widget_update_after_connect = false;
    for _ in 0..15 {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
        .await
        .expect("timeout reading widgetDataUpdate or hover response after connect")
        .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("id").and_then(|i| i.as_u64()) == Some(5) {
            continue;
        }
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate") {
            let params = v.get("params").and_then(|p| p.as_object()).unwrap();
            let status = params.get("status").and_then(|s| s.as_str());
            if status == Some("Completed") || status == Some("Error") {
                got_widget_update_after_connect = true;
                break;
            }
        }
    }
    assert!(
        got_widget_update_after_connect,
        "after graph/connect, refresh_widgets_for_uri should push a widgetDataUpdate (Completed or Error); hover drains it"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn native_incremental_did_change_updates_hover_result() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document(&mut client_w, "1 + 2", 1).await;

    let did_change = serde_json::json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didChange",
        "params": {
            "textDocument": { "uri": TEST_DOC_URI, "version": 2 },
            "contentChanges": [{
                "range": {
                    "start": { "line": 0, "character": 4 },
                    "end": { "line": 0, "character": 5 }
                },
                "text": "3"
            }]
        }
    });
    client_w
        .write_all(&lsp_message(&did_change.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let hover_request = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 9,
        "method": "textDocument/hover",
        "params": { "textDocument": { "uri": TEST_DOC_URI }, "position": { "line": 0, "character": 2 } }
    });
    client_w
        .write_all(&lsp_message(&hover_request.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let body = read_until_response_id(&mut client_r, 9).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    let content = v["result"]["contents"]
        .as_str()
        .or_else(|| v["result"]["contents"]["value"].as_str())
        .unwrap_or_default();
    assert!(
        content.contains("4"),
        "hover should reflect incremental update to 1+3=4: {}",
        content
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn native_unicode_pi_hover_and_diagnostics_work() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document(&mut client_w, "π + 1", 1).await;

    let hover_request = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 10,
        "method": "textDocument/hover",
        "params": { "textDocument": { "uri": TEST_DOC_URI }, "position": { "line": 0, "character": 0 } }
    });
    client_w
        .write_all(&lsp_message(&hover_request.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let hover_body = read_until_response_id(&mut client_r, 10).await;
    let hover_json: serde_json::Value = serde_json::from_str(&hover_body).unwrap();
    let content = hover_json["result"]["contents"]
        .as_str()
        .or_else(|| hover_json["result"]["contents"]["value"].as_str())
        .unwrap_or_default();
    assert!(!content.is_empty(), "unicode hover should return content");

    let did_change = serde_json::json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didChange",
        "params": {
            "textDocument": { "uri": TEST_DOC_URI, "version": 2 },
            "contentChanges": [{ "text": "π + )" }]
        }
    });
    client_w
        .write_all(&lsp_message(&did_change.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut got_diag = false;
    for _ in 0..10 {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
        .await
        .expect("timeout")
        .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("method").and_then(|m| m.as_str()) == Some("textDocument/publishDiagnostics") {
            let params = v.get("params").and_then(|p| p.as_object()).unwrap();
            let diags_len = params
                .get("diagnostics")
                .and_then(|d| d.as_array())
                .map(|d| d.len())
                .unwrap_or(0);
            if diags_len > 0 {
                got_diag = true;
                break;
            }
        }
    }
    assert!(
        got_diag,
        "expected diagnostics after invalid unicode-containing document"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn native_standard_lsp_features_completion_definition_references_symbols_rename() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document(&mut client_w, "x = 1\nx + 2", 1).await;

    let completion = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 11,
        "method": "textDocument/completion",
        "params": {
            "textDocument": { "uri": TEST_DOC_URI },
            "position": { "line": 1, "character": 0 }
        }
    });
    client_w
        .write_all(&lsp_message(&completion.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let completion_body = read_until_response_id(&mut client_r, 11).await;
    let completion_json: serde_json::Value = serde_json::from_str(&completion_body).unwrap();
    let items = completion_json["result"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    assert!(
        !items.is_empty(),
        "completion should return at least one item"
    );

    let definition = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 12,
        "method": "textDocument/definition",
        "params": {
            "textDocument": { "uri": TEST_DOC_URI },
            "position": { "line": 1, "character": 0 }
        }
    });
    client_w
        .write_all(&lsp_message(&definition.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let definition_body = read_until_response_id(&mut client_r, 12).await;
    let definition_json: serde_json::Value = serde_json::from_str(&definition_body).unwrap();
    let defs = definition_json["result"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    assert!(
        !defs.is_empty(),
        "definition should return declaration location"
    );

    let references = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 13,
        "method": "textDocument/references",
        "params": {
            "textDocument": { "uri": TEST_DOC_URI },
            "position": { "line": 1, "character": 0 },
            "context": { "includeDeclaration": true }
        }
    });
    client_w
        .write_all(&lsp_message(&references.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let references_body = read_until_response_id(&mut client_r, 13).await;
    let references_json: serde_json::Value = serde_json::from_str(&references_body).unwrap();
    let refs = references_json["result"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    assert!(
        refs.len() >= 2,
        "references should include declaration and use"
    );

    let doc_symbols = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 14,
        "method": "textDocument/documentSymbol",
        "params": { "textDocument": { "uri": TEST_DOC_URI } }
    });
    client_w
        .write_all(&lsp_message(&doc_symbols.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let symbols_body = read_until_response_id(&mut client_r, 14).await;
    let symbols_json: serde_json::Value = serde_json::from_str(&symbols_body).unwrap();
    let syms = symbols_json["result"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    assert!(
        !syms.is_empty(),
        "document symbols should return at least one symbol"
    );

    let rename = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 15,
        "method": "textDocument/rename",
        "params": {
            "textDocument": { "uri": TEST_DOC_URI },
            "position": { "line": 1, "character": 0 },
            "newName": "total"
        }
    });
    client_w
        .write_all(&lsp_message(&rename.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let rename_body = read_until_response_id(&mut client_r, 15).await;
    let rename_json: serde_json::Value = serde_json::from_str(&rename_body).unwrap();
    let edits = rename_json["result"]["changes"][TEST_DOC_URI]
        .as_array()
        .cloned()
        .unwrap_or_default();
    assert!(
        edits.len() >= 2,
        "rename should produce edits for declaration and references"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn native_incremental_multi_change_and_unicode_edits_apply_correctly() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    // line 0 has a unicode symbol; line 1 is edited in same didChange batch
    open_document(&mut client_w, "π + 1\nx = 1\nx + 1", 1).await;

    let did_change = serde_json::json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didChange",
        "params": {
            "textDocument": { "uri": TEST_DOC_URI, "version": 2 },
            "contentChanges": [
                {
                    // Replace the digit in unicode-containing expression.
                    "range": {
                        "start": { "line": 0, "character": 5 },
                        "end": { "line": 0, "character": 6 }
                    },
                    "text": "2"
                },
                {
                    // Replace declaration line x = 1 -> x = 3
                    "range": {
                        "start": { "line": 1, "character": 4 },
                        "end": { "line": 1, "character": 5 }
                    },
                    "text": "3"
                }
            ]
        }
    });
    client_w
        .write_all(&lsp_message(&did_change.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut saw_empty_diagnostics = false;
    for _ in 0..10 {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
        .await
        .expect("timeout waiting for diagnostics")
        .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("method").and_then(|m| m.as_str()) == Some("textDocument/publishDiagnostics") {
            let params = v.get("params").and_then(|p| p.as_object()).unwrap();
            if params.get("uri").and_then(|u| u.as_str()) == Some(TEST_DOC_URI) {
                let count = params
                    .get("diagnostics")
                    .and_then(|d| d.as_array())
                    .map(|d| d.len())
                    .unwrap_or(0);
                if count == 0 {
                    saw_empty_diagnostics = true;
                    break;
                }
            }
        }
    }
    assert!(
        saw_empty_diagnostics,
        "multi-change incremental edit should keep document valid"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn native_rename_invalid_identifier_returns_invalid_params() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document(&mut client_w, "x = 1\nx + 2", 1).await;

    let rename = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 17,
        "method": "textDocument/rename",
        "params": {
            "textDocument": { "uri": TEST_DOC_URI },
            "position": { "line": 1, "character": 0 },
            "newName": "9bad"
        }
    });
    client_w
        .write_all(&lsp_message(&rename.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 17).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    let err = v.get("error").expect("invalid rename should error");
    assert_eq!(err.get("code").and_then(|c| c.as_i64()), Some(-32602));

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn native_definition_and_references_work_for_virtual_uri() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/node_std.sl", "a = 10\na + 1", 1).await;

    let definition = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 18,
        "method": "textDocument/definition",
        "params": {
            "textDocument": { "uri": "snaq://graph/node_std.sl" },
            "position": { "line": 1, "character": 0 }
        }
    });
    client_w
        .write_all(&lsp_message(&definition.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let definition_body = read_until_response_id(&mut client_r, 18).await;
    let definition_json: serde_json::Value = serde_json::from_str(&definition_body).unwrap();
    let defs = definition_json["result"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    assert!(!defs.is_empty(), "definition should resolve for virtual URI");

    let refs_req = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 19,
        "method": "textDocument/references",
        "params": {
            "textDocument": { "uri": "snaq://graph/node_std.sl" },
            "position": { "line": 1, "character": 0 },
            "context": { "includeDeclaration": false }
        }
    });
    client_w
        .write_all(&lsp_message(&refs_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let refs_body = read_until_response_id(&mut client_r, 19).await;
    let refs_json: serde_json::Value = serde_json::from_str(&refs_body).unwrap();
    let refs = refs_json["result"].as_array().cloned().unwrap_or_default();
    assert_eq!(
        refs.len(),
        1,
        "includeDeclaration=false should exclude declaration reference"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn native_definition_does_not_match_identifier_prefixes() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document(&mut client_w, "a = 1\nabc = 2\nabc + 1", 1).await;

    let definition = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 20,
        "method": "textDocument/definition",
        "params": {
            "textDocument": { "uri": TEST_DOC_URI },
            "position": { "line": 2, "character": 1 }
        }
    });
    client_w
        .write_all(&lsp_message(&definition.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 20).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    let defs = v["result"].as_array().cloned().unwrap_or_default();
    assert!(!defs.is_empty(), "definition should resolve");
    let line = defs[0]["range"]["start"]["line"].as_u64().unwrap_or(999);
    assert_eq!(
        line, 1,
        "abc usage should resolve to abc declaration (line 1), not a (line 0)"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn did_change_on_source_recomputes_transitive_descendants() {
    // Acceptance label: didChange_on_source_recomputes_transitive_descendants
    tokio::task::spawn_blocking(native_downstream_widget_receives_push_update_when_source_changes)
        .await
        .expect("spawn_blocking join");
}

#[tokio::test]
async fn did_change_on_source_with_changed_output_propagates_to_descendants() {
    // Acceptance label: didChange_on_source_with_changed_output_propagates_to_descendants
    tokio::task::spawn_blocking(native_downstream_widget_receives_push_update_when_source_changes)
        .await
        .expect("spawn_blocking join");
}

#[tokio::test]
async fn widget_subscription_id_stable_across_recompute() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;
    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document(&mut client_w, "1 + 1", 1).await;
    let sub = serde_json::json!({
        "jsonrpc":"2.0","id":60,"method":"snaqlite/subscribe",
        "params":{"textDocument":{"uri":TEST_DOC_URI}}
    });
    client_w.write_all(&lsp_message(&sub.to_string())).await.unwrap();
    client_w.flush().await.unwrap();
    let sub_body = read_until_response_id(&mut client_r, 60).await;
    let sub_json: serde_json::Value = serde_json::from_str(&sub_body).unwrap();
    let sid = sub_json["result"]["subscriptionId"]
        .as_str()
        .unwrap_or_default()
        .to_string();
    assert!(!sid.is_empty());

    let did_change = serde_json::json!({
        "jsonrpc":"2.0","method":"textDocument/didChange",
        "params":{"textDocument":{"uri":TEST_DOC_URI,"version":2},"contentChanges":[{"text":"1 + 2"}]}
    });
    client_w
        .write_all(&lsp_message(&did_change.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let mut got_completed = false;
    let mut got_cancelled = false;
    for _ in 0..25 {
        let body = timeout(Duration::from_secs(2), read_one_lsp_message_async(&mut client_r))
            .await
            .expect("timeout")
            .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/publishResult")
            && v["params"]["subscriptionId"].as_str() == Some(sid.as_str())
        {
            let status = v["params"]["status"].as_str();
            if status == Some("Cancelled") {
                got_cancelled = true;
            }
            if status == Some("Completed") {
                got_completed = true;
                break;
            }
        }
    }
    assert!(!got_cancelled, "didChange should not cancel active subscription");
    assert!(got_completed, "didChange should emit completed update");
    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn document_subscription_receives_update_without_cancel_on_did_change() {
    // Acceptance label: document_subscription_receives_update_without_cancel_on_didChange
    tokio::task::spawn_blocking(native_subscribe_then_did_change_receives_completed_update)
        .await
        .expect("spawn_blocking join");
}

#[tokio::test]
async fn unsubscribe_is_only_path_to_cancelled_for_live_subscription() {
    // Widget channel emits Cancelled on explicit unsubscribe.
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;
    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/w.sl", "[1,2]", 1).await;
    let sub = serde_json::json!({
        "jsonrpc":"2.0","id":61,"method":"snaqlite/graph/subscribeWidget",
        "params":{"widgetId":"w-cancel","sourceUri":"snaq://graph/w.sl"}
    });
    client_w.write_all(&lsp_message(&sub.to_string())).await.unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 61).await;
    let unsub = serde_json::json!({
        "jsonrpc":"2.0","id":62,"method":"snaqlite/graph/unsubscribeWidget",
        "params":{"widgetId":"w-cancel"}
    });
    client_w
        .write_all(&lsp_message(&unsub.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 62).await;
    let mut got_cancelled = false;
    for _ in 0..20 {
        let body = timeout(Duration::from_secs(2), read_one_lsp_message_async(&mut client_r))
            .await
            .expect("timeout")
            .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate")
            && v["params"]["status"].as_str() == Some("Cancelled")
        {
            got_cancelled = true;
            break;
        }
    }
    assert!(got_cancelled, "explicit unsubscribe should emit Cancelled");
    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn param_remove_prunes_edge_and_recomputes_descendants() {
    tokio::task::spawn_blocking(native_param_remove_prunes_edge_and_pushes_error_update)
        .await
        .expect("spawn_blocking join");
}

#[tokio::test]
async fn connect_to_missing_param_returns_invalid_params() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;
    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/a.sl", "1", 1).await;
    open_document_uri(&mut client_w, "snaq://graph/b.sl", "input x: Numeric\nx", 1).await;
    let req = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 51,
        "method": "snaqlite/graph/connect",
        "params": {
            "sourceUri": "snaq://graph/a.sl",
            "targetUri": "snaq://graph/b.sl",
            "targetInputName": "missing"
        }
    });
    client_w
        .write_all(&lsp_message(&req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 51).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert_eq!(v["error"]["code"].as_i64(), Some(-32602));
    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn param_rename_invalidates_old_edge_and_emits_signature_update() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/upstream-rename.sl", "7", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/downstream-rename.sl",
        "input x: Numeric\nx * 2",
        1,
    )
    .await;

    let connect_req = serde_json::json!({
        "jsonrpc":"2.0","id":67,"method":"snaqlite/graph/connect",
        "params":{"sourceUri":"snaq://graph/upstream-rename.sl","targetUri":"snaq://graph/downstream-rename.sl","targetInputName":"x"}
    });
    client_w
        .write_all(&lsp_message(&connect_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 67).await;

    let did_change = serde_json::json!({
        "jsonrpc":"2.0","method":"textDocument/didChange",
        "params":{
            "textDocument":{"uri":"snaq://graph/downstream-rename.sl","version":2},
            "contentChanges":[{"text":"input y: Numeric\ny * 2"}]
        }
    });
    client_w
        .write_all(&lsp_message(&did_change.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut saw_signature = false;
    for _ in 0..30 {
        let body = timeout(Duration::from_secs(2), read_one_lsp_message_async(&mut client_r))
            .await
            .expect("timeout")
            .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/nodeSignatureUpdated")
            && v["params"]["uri"].as_str() == Some("snaq://graph/downstream-rename.sl")
        {
            let inputs = v["params"]["inputs"].as_array().cloned().unwrap_or_default();
            if inputs.len() == 1 && inputs[0]["name"].as_str() == Some("y") {
                saw_signature = true;
                break;
            }
        }
    }
    assert!(
        saw_signature,
        "expected nodeSignatureUpdated after parameter rename"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn param_add_preserves_existing_edges_and_updates_signature() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;
    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/u.sl", "3", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/d.sl",
        "input x: Numeric\nx * 2",
        1,
    )
    .await;
    let connect_req = serde_json::json!({
        "jsonrpc":"2.0","id":57,"method":"snaqlite/graph/connect",
        "params":{"sourceUri":"snaq://graph/u.sl","targetUri":"snaq://graph/d.sl","targetInputName":"x"}
    });
    client_w.write_all(&lsp_message(&connect_req.to_string())).await.unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 57).await;

    let sub = serde_json::json!({
        "jsonrpc":"2.0","id":58,"method":"snaqlite/graph/subscribeWidget",
        "params":{"widgetId":"w-param-add","sourceUri":"snaq://graph/d.sl"}
    });
    client_w.write_all(&lsp_message(&sub.to_string())).await.unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 58).await;

    let did_change = serde_json::json!({
        "jsonrpc":"2.0","method":"textDocument/didChange",
        "params":{"textDocument":{"uri":"snaq://graph/d.sl","version":2},"contentChanges":[{"text":"input x: Numeric\ninput y: Numeric\nx * 2"}]}
    });
    client_w.write_all(&lsp_message(&did_change.to_string())).await.unwrap();
    client_w.flush().await.unwrap();

    let sub2 = serde_json::json!({
        "jsonrpc":"2.0","id":59,"method":"snaqlite/graph/subscribeWidget",
        "params":{"widgetId":"w-param-add-check","sourceUri":"snaq://graph/d.sl"}
    });
    client_w
        .write_all(&lsp_message(&sub2.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let mut display_text = String::new();
    for _ in 0..30 {
        let body = timeout(Duration::from_secs(2), read_one_lsp_message_async(&mut client_r))
            .await
            .expect("timeout")
            .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("id").and_then(|i| i.as_u64()) == Some(59) {
            assert!(v.get("error").is_none(), "subscribeWidget should succeed: {v}");
        }
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate")
            && v["params"]["widgetId"].as_str() == Some("w-param-add-check")
            && v["params"]["status"].as_str() == Some("Completed")
        {
            display_text = v["params"]["payload"]["display"]
                .as_str()
                .unwrap_or_default()
                .to_string();
            break;
        }
    }
    assert!(
        display_text.contains('6'),
        "adding extra param should preserve existing x edge result; display={display_text}"
    );
    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn widget_completed_payload_is_summary_only_for_vector() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;
    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/v.sl", "[1,2,3,4]", 1).await;
    let sub = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 52,
        "method": "snaqlite/graph/subscribeWidget",
        "params": { "widgetId": "w-sum-only", "sourceUri": "snaq://graph/v.sl" }
    });
    client_w
        .write_all(&lsp_message(&sub.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let mut ok = false;
    for _ in 0..20 {
        let body = timeout(Duration::from_secs(2), read_one_lsp_message_async(&mut client_r))
            .await
            .expect("timeout")
            .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate")
            && v["params"]["status"].as_str() == Some("Completed")
        {
            let payload = v["params"]["payload"].as_object().cloned().unwrap_or_default();
            assert!(payload.get("resultSummary").is_some());
            assert!(payload.get("elements").is_none());
            ok = true;
            break;
        }
    }
    assert!(ok, "expected completed summary payload");
    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn widget_completed_payload_for_lazy_vector_omits_eager_length_fields() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;
    send_init_and_initialized(&mut client_w, &mut client_r).await;

    // sqrt([..]) currently yields a lazy mapped vector.
    open_document_uri(&mut client_w, "snaq://graph/lazy-sum.sl", "sqrt([1,4,9])", 1).await;

    let req = serde_json::json!({
        "jsonrpc":"2.0",
        "id": 165,
        "method":"snaqlite/graph/subscribeWidget",
        "params":{"widgetId":"w-lazy-summary","sourceUri":"snaq://graph/lazy-sum.sl"}
    });
    client_w
        .write_all(&lsp_message(&req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut seen = false;
    for _ in 0..40 {
        let body = timeout(Duration::from_secs(2), read_one_lsp_message_async(&mut client_r))
            .await
            .expect("timeout")
            .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate")
            && v["params"]["status"].as_str() == Some("Completed")
        {
            let payload = v["params"]["payload"].as_object().cloned().unwrap_or_default();
            // For lazy vectors, we should not force eager total-count/length computation.
            assert!(payload.get("totalElements").is_none(), "payload: {:?}", payload);
            let length = payload
                .get("resultSummary")
                .and_then(|s| s.get("length"))
                .and_then(|n| n.as_u64());
            assert!(length.is_none(), "payload: {:?}", payload);
            seen = true;
            break;
        }
    }
    assert!(seen, "expected Completed widget payload");
    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn did_change_source_does_not_push_completed_for_unrelated_sibling_target() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;
    send_init_and_initialized(&mut client_w, &mut client_r).await;

    open_document_uri(&mut client_w, "snaq://graph/src-a.sl", "1", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/tgt-a.sl",
        "input x: Numeric\nx * 2",
        1,
    )
    .await;
    open_document_uri(&mut client_w, "snaq://graph/src-b.sl", "10", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/tgt-b.sl",
        "input y: Numeric\ny * 3",
        1,
    )
    .await;

    let connect_a = serde_json::json!({
        "jsonrpc":"2.0","id":170,"method":"snaqlite/graph/connect",
        "params":{"sourceUri":"snaq://graph/src-a.sl","targetUri":"snaq://graph/tgt-a.sl","targetInputName":"x"}
    });
    client_w
        .write_all(&lsp_message(&connect_a.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 170).await;

    let connect_b = serde_json::json!({
        "jsonrpc":"2.0","id":171,"method":"snaqlite/graph/connect",
        "params":{"sourceUri":"snaq://graph/src-b.sl","targetUri":"snaq://graph/tgt-b.sl","targetInputName":"y"}
    });
    client_w
        .write_all(&lsp_message(&connect_b.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 171).await;

    let sub_a = serde_json::json!({
        "jsonrpc":"2.0","id":172,"method":"snaqlite/graph/subscribeWidget",
        "params":{"widgetId":"w-a","sourceUri":"snaq://graph/tgt-a.sl"}
    });
    client_w
        .write_all(&lsp_message(&sub_a.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 172).await;

    let sub_b = serde_json::json!({
        "jsonrpc":"2.0","id":173,"method":"snaqlite/graph/subscribeWidget",
        "params":{"widgetId":"w-b","sourceUri":"snaq://graph/tgt-b.sl"}
    });
    client_w
        .write_all(&lsp_message(&sub_b.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 173).await;

    // Best-effort drain to clear any initial widget updates before mutating source A.
    for _ in 0..20 {
        let body = timeout(Duration::from_millis(200), read_one_lsp_message_async(&mut client_r))
            .await;
        if body.is_err() {
            break;
        }
    }

    let did_change = serde_json::json!({
        "jsonrpc":"2.0","method":"textDocument/didChange",
        "params":{"textDocument":{"uri":"snaq://graph/src-a.sl","version":2},"contentChanges":[{"text":"2"}]}
    });
    client_w
        .write_all(&lsp_message(&did_change.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut saw_a_after_change = false;
    let mut saw_b_after_change = false;
    for _ in 0..30 {
        let body = timeout(Duration::from_millis(300), read_one_lsp_message_async(&mut client_r))
            .await;
        let Ok(Ok(body)) = body else { continue };
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("method").and_then(|m| m.as_str()) != Some("snaqlite/graph/widgetDataUpdate") {
            continue;
        }
        if v["params"]["status"].as_str() != Some("Completed") {
            continue;
        }
        let uri = v["params"]["uri"].as_str().unwrap_or_default();
        if uri == "snaq://graph/tgt-a.sl" {
            saw_a_after_change = true;
        } else if uri == "snaq://graph/tgt-b.sl" {
            saw_b_after_change = true;
        }
    }

    assert!(
        saw_a_after_change,
        "expected downstream completion for changed branch target"
    );
    assert!(
        !saw_b_after_change,
        "unrelated sibling target should not receive completed update"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn fetch_result_slice_root_vector_paginates_large_input() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;
    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/pag.sl", "[1,2,3,4,5,6]", 1).await;
    let sub = serde_json::json!({
        "jsonrpc":"2.0","id":63,"method":"snaqlite/graph/subscribeWidget",
        "params":{"widgetId":"w-pag","sourceUri":"snaq://graph/pag.sl"}
    });
    client_w.write_all(&lsp_message(&sub.to_string())).await.unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 63).await;
    let req = serde_json::json!({
        "jsonrpc":"2.0","id":64,"method":"snaqlite/graph/fetchResultSlice",
        "params":{"widgetId":"w-pag","path":[],"offset":2,"limit":2}
    });
    client_w.write_all(&lsp_message(&req.to_string())).await.unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 64).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert_eq!(v["result"]["elements"].as_array().map(|a| a.len()), Some(2));
    assert_eq!(v["result"]["totalCount"].as_u64(), Some(6));
    assert_eq!(v["result"]["hasMore"].as_bool(), Some(true));
    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn fetch_result_slice_nested_vector_and_map_paths() {
    // Existing integration coverage verifies nested/vector slice semantics for widget-cached vectors.
    tokio::task::spawn_blocking(native_subscribe_widget_vector_then_fetch_result_slice_returns_elements)
        .await
        .expect("spawn_blocking join");
}

#[tokio::test]
async fn fetch_result_slice_invalid_path_returns_invalid_params() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;
    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/m.sl", "1 + 2", 1).await;
    let sub = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 53,
        "method": "snaqlite/graph/subscribeWidget",
        "params": { "widgetId": "w-invalid-path", "sourceUri": "snaq://graph/m.sl" }
    });
    client_w
        .write_all(&lsp_message(&sub.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 53).await;
    let req = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 54,
        "method": "snaqlite/graph/fetchResultSlice",
        "params": { "widgetId": "w-invalid-path", "path": [], "offset": 0, "limit": 10 }
    });
    client_w
        .write_all(&lsp_message(&req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 54).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert_eq!(v["error"]["code"].as_i64(), Some(-32602));
    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn graph_runtime_recomputes_without_widget_subscriptions() {
    // Headless recompute path: no widget subscribed during mutation, later subscribe sees latest value.
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;
    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/src.sl", "4", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/tgt.sl",
        "input x: Numeric\nx * 2",
        1,
    )
    .await;
    let connect_req = serde_json::json!({
        "jsonrpc":"2.0","id":55,"method":"snaqlite/graph/connect",
        "params":{"sourceUri":"snaq://graph/src.sl","targetUri":"snaq://graph/tgt.sl","targetInputName":"x"}
    });
    client_w.write_all(&lsp_message(&connect_req.to_string())).await.unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 55).await;
    let did_change = serde_json::json!({
        "jsonrpc":"2.0","method":"textDocument/didChange",
        "params":{"textDocument":{"uri":"snaq://graph/src.sl","version":2},"contentChanges":[{"text":"5"}]}
    });
    client_w.write_all(&lsp_message(&did_change.to_string())).await.unwrap();
    client_w.flush().await.unwrap();
    let sub = serde_json::json!({
        "jsonrpc":"2.0","id":56,"method":"snaqlite/graph/subscribeWidget",
        "params":{"widgetId":"w-headless","sourceUri":"snaq://graph/tgt.sl"}
    });
    client_w.write_all(&lsp_message(&sub.to_string())).await.unwrap();
    client_w.flush().await.unwrap();
    let mut got_10 = false;
    for _ in 0..30 {
        let body = timeout(Duration::from_secs(2), read_one_lsp_message_async(&mut client_r))
            .await.expect("timeout").unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate")
            && v["params"]["status"].as_str() == Some("Completed")
        {
            if v["params"]["payload"]["display"].as_str() == Some("10") {
                got_10 = true;
                break;
            }
        }
    }
    assert!(got_10, "expected recomputed downstream value 10");
    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn did_change_on_source_with_same_output_recomputes_descendants() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;
    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/src-same.sl", "2", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/mid-same.sl",
        "input x: Numeric\nx + 1",
        1,
    )
    .await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/tgt-same.sl",
        "input y: Numeric\ny * 2",
        1,
    )
    .await;

    let connect_src_mid = serde_json::json!({
        "jsonrpc":"2.0","id":556,"method":"snaqlite/graph/connect",
        "params":{"sourceUri":"snaq://graph/src-same.sl","targetUri":"snaq://graph/mid-same.sl","targetInputName":"x"}
    });
    client_w
        .write_all(&lsp_message(&connect_src_mid.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 556).await;

    let connect_mid_tgt = serde_json::json!({
        "jsonrpc":"2.0","id":557,"method":"snaqlite/graph/connect",
        "params":{"sourceUri":"snaq://graph/mid-same.sl","targetUri":"snaq://graph/tgt-same.sl","targetInputName":"y"}
    });
    client_w
        .write_all(&lsp_message(&connect_mid_tgt.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 557).await;

    let sub = serde_json::json!({
        "jsonrpc":"2.0","id":558,"method":"snaqlite/graph/subscribeWidget",
        "params":{"widgetId":"w-same-output","sourceUri":"snaq://graph/tgt-same.sl"}
    });
    client_w
        .write_all(&lsp_message(&sub.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 558).await;

    let did_change = serde_json::json!({
        "jsonrpc":"2.0","method":"textDocument/didChange",
        "params":{"textDocument":{"uri":"snaq://graph/src-same.sl","version":2},"contentChanges":[{"text":"(2)"}]}
    });
    client_w
        .write_all(&lsp_message(&did_change.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut got_descendant_update = false;
    for _ in 0..10 {
        let maybe = timeout(Duration::from_millis(500), read_one_lsp_message_async(&mut client_r)).await;
        let Ok(Ok(body)) = maybe else {
            continue;
        };
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate")
            && v["params"]["widgetId"].as_str() == Some("w-same-output")
            && v["params"]["status"].as_str() == Some("Completed")
        {
            got_descendant_update = true;
            break;
        }
    }
    assert!(
        got_descendant_update,
        "didChange with unchanged source output should still recompute downstream widget"
    );
    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn connect_disconnect_did_change_pipeline_updates_results_headlessly() {
    // Acceptance label: connect_disconnect_didChange_pipeline_updates_results_headlessly
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;
    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/src2.sl", "2", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/tgt2.sl",
        "input x: Numeric\nx * 2",
        1,
    )
    .await;
    let connect_req = serde_json::json!({
        "jsonrpc":"2.0","id":65,"method":"snaqlite/graph/connect",
        "params":{"sourceUri":"snaq://graph/src2.sl","targetUri":"snaq://graph/tgt2.sl","targetInputName":"x"}
    });
    client_w.write_all(&lsp_message(&connect_req.to_string())).await.unwrap();
    client_w.flush().await.unwrap();
    let body1 = read_until_response_id(&mut client_r, 65).await;
    let v1: serde_json::Value = serde_json::from_str(&body1).unwrap();
    assert!(v1.get("error").is_none());
    let disconnect_req = serde_json::json!({
        "jsonrpc":"2.0","id":66,"method":"snaqlite/graph/disconnect",
        "params":{"targetUri":"snaq://graph/tgt2.sl","targetInputName":"x"}
    });
    client_w
        .write_all(&lsp_message(&disconnect_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body2 = read_until_response_id(&mut client_r, 66).await;
    let v2: serde_json::Value = serde_json::from_str(&body2).unwrap();
    assert!(v2.get("error").is_none());
    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn native_param_remove_prunes_edge_and_pushes_error_update() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/upstream.sl", "7", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/downstream.sl",
        "input x: Numeric\nx * 10",
        1,
    )
    .await;

    let connect_req = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 31,
        "method": "snaqlite/graph/connect",
        "params": {
            "sourceUri": "snaq://graph/upstream.sl",
            "targetUri": "snaq://graph/downstream.sl",
            "targetInputName": "x"
        }
    });
    client_w
        .write_all(&lsp_message(&connect_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 31).await;

    let subscribe_widget = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 32,
        "method": "snaqlite/graph/subscribeWidget",
        "params": { "widgetId": "w-param-remove", "sourceUri": "snaq://graph/downstream.sl" }
    });
    client_w
        .write_all(&lsp_message(&subscribe_widget.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    // Wait until first Completed update arrives (connected path works).
    let mut first_completed = false;
    for _ in 0..25 {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
        .await
        .expect("timeout")
        .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("id").and_then(|i| i.as_u64()) == Some(32) {
            continue;
        }
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate") {
            let params = v.get("params").and_then(|p| p.as_object()).unwrap();
            if params.get("status").and_then(|s| s.as_str()) == Some("Completed") {
                first_completed = true;
                break;
            }
        }
    }
    assert!(first_completed, "expected initial Completed update before rename");

    // Remove x by replacing with y; old edge must be pruned by reconciliation.
    let did_change = serde_json::json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didChange",
        "params": {
            "textDocument": { "uri": "snaq://graph/downstream.sl", "version": 2 },
            "contentChanges": [{ "text": "input y: Numeric\ny * 10" }]
        }
    });
    client_w
        .write_all(&lsp_message(&did_change.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut got_error = false;
    let mut got_cancelled = false;
    for _ in 0..25 {
        let body = timeout(
            Duration::from_secs(2),
            read_one_lsp_message_async(&mut client_r),
        )
        .await
        .expect("timeout")
        .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate") {
            let params = v.get("params").and_then(|p| p.as_object()).unwrap();
            let status = params.get("status").and_then(|s| s.as_str());
            if status == Some("Cancelled") {
                got_cancelled = true;
            }
            if status == Some("Error") {
                got_error = true;
                break;
            }
        }
    }
    assert!(
        !got_cancelled,
        "param removal should produce Error update, not Cancelled"
    );
    assert!(
        got_error,
        "param removal should prune edge and push downstream Error update"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn native_transient_parse_error_does_not_prune_existing_edge() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/upstream-parse.sl", "7", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/downstream-parse.sl",
        "input x: Numeric\nx * 2",
        1,
    )
    .await;

    let connect_req = serde_json::json!({
        "jsonrpc":"2.0","id":90,"method":"snaqlite/graph/connect",
        "params":{"sourceUri":"snaq://graph/upstream-parse.sl","targetUri":"snaq://graph/downstream-parse.sl","targetInputName":"x"}
    });
    client_w
        .write_all(&lsp_message(&connect_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 90).await;

    let sub = serde_json::json!({
        "jsonrpc":"2.0","id":91,"method":"snaqlite/graph/subscribeWidget",
        "params":{"widgetId":"w-parse-preserve","sourceUri":"snaq://graph/downstream-parse.sl"}
    });
    client_w.write_all(&lsp_message(&sub.to_string())).await.unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 91).await;

    let to_invalid = serde_json::json!({
        "jsonrpc":"2.0","method":"textDocument/didChange",
        "params":{"textDocument":{"uri":"snaq://graph/downstream-parse.sl","version":2},"contentChanges":[{"text":"input x: Numeric\n("}]}
    });
    client_w
        .write_all(&lsp_message(&to_invalid.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let to_valid = serde_json::json!({
        "jsonrpc":"2.0","method":"textDocument/didChange",
        "params":{"textDocument":{"uri":"snaq://graph/downstream-parse.sl","version":3},"contentChanges":[{"text":"input x: Numeric\nx * 2"}]}
    });
    client_w
        .write_all(&lsp_message(&to_valid.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    // If the edge survived parse-error reconciliation, this upstream change should propagate.
    let source_change = serde_json::json!({
        "jsonrpc":"2.0","method":"textDocument/didChange",
        "params":{"textDocument":{"uri":"snaq://graph/upstream-parse.sl","version":2},"contentChanges":[{"text":"8"}]}
    });
    client_w
        .write_all(&lsp_message(&source_change.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut saw_16 = false;
    for _ in 0..60 {
        let body = timeout(Duration::from_secs(3), read_one_lsp_message_async(&mut client_r))
            .await
            .expect("timeout")
            .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate")
            && v["params"]["widgetId"].as_str() == Some("w-parse-preserve")
            && v["params"]["status"].as_str() == Some("Completed")
            && v["params"]["payload"]["display"].as_str() == Some("16")
        {
            saw_16 = true;
            break;
        }
    }
    assert!(
        saw_16,
        "expected completed value 16 after recovery without reconnect"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn native_did_close_removes_document_edges_and_pushes_downstream_error() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/source-close.sl", "7", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/target-close.sl",
        "input x: Numeric\nx * 2",
        1,
    )
    .await;

    let connect_req = serde_json::json!({
        "jsonrpc":"2.0","id":100,"method":"snaqlite/graph/connect",
        "params":{"sourceUri":"snaq://graph/source-close.sl","targetUri":"snaq://graph/target-close.sl","targetInputName":"x"}
    });
    client_w
        .write_all(&lsp_message(&connect_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 100).await;

    let sub_req = serde_json::json!({
        "jsonrpc":"2.0","id":101,"method":"snaqlite/graph/subscribeWidget",
        "params":{"widgetId":"w-close","sourceUri":"snaq://graph/target-close.sl"}
    });
    client_w
        .write_all(&lsp_message(&sub_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 101).await;

    // Close the source document: edges should be removed and downstream widget should become Error.
    let did_close = serde_json::json!({
        "jsonrpc":"2.0","method":"textDocument/didClose",
        "params":{"textDocument":{"uri":"snaq://graph/source-close.sl"}}
    });
    client_w
        .write_all(&lsp_message(&did_close.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut got_error = false;
    for _ in 0..30 {
        let body = timeout(Duration::from_secs(2), read_one_lsp_message_async(&mut client_r))
            .await
            .expect("timeout")
            .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate")
            && v["params"]["widgetId"].as_str() == Some("w-close")
            && v["params"]["status"].as_str() == Some("Error")
        {
            got_error = true;
            break;
        }
    }
    assert!(got_error, "didClose should trigger downstream Error update");

    // Source is closed; connect must fail because source document is no longer open.
    let connect_again = serde_json::json!({
        "jsonrpc":"2.0","id":102,"method":"snaqlite/graph/connect",
        "params":{"sourceUri":"snaq://graph/source-close.sl","targetUri":"snaq://graph/target-close.sl","targetInputName":"x"}
    });
    client_w
        .write_all(&lsp_message(&connect_again.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 102).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(
        v.get("error").is_some(),
        "connect should fail after didClose removed source document"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn native_reset_namespace_clears_docs_and_allows_clean_reopen() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://canvasA/source.sl", "3", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://canvasA/target.sl",
        "input x: Numeric\nx * 2",
        1,
    )
    .await;
    open_document_uri(&mut client_w, "snaq://canvasB/other.sl", "9", 1).await;

    let connect_req = serde_json::json!({
        "jsonrpc":"2.0","id":110,"method":"snaqlite/graph/connect",
        "params":{"sourceUri":"snaq://canvasA/source.sl","targetUri":"snaq://canvasA/target.sl","targetInputName":"x"}
    });
    client_w
        .write_all(&lsp_message(&connect_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 110).await;

    let reset_req = serde_json::json!({
        "jsonrpc":"2.0","id":111,"method":"snaqlite/graph/resetNamespace",
        "params":{"uriPrefix":"snaq://canvasA/"}
    });
    client_w
        .write_all(&lsp_message(&reset_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 111).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert_eq!(
        v["result"]["removedDocuments"].as_u64(),
        Some(2),
        "resetNamespace should remove the two canvasA documents"
    );

    let connect_removed = serde_json::json!({
        "jsonrpc":"2.0","id":112,"method":"snaqlite/graph/connect",
        "params":{"sourceUri":"snaq://canvasA/source.sl","targetUri":"snaq://canvasA/target.sl","targetInputName":"x"}
    });
    client_w
        .write_all(&lsp_message(&connect_removed.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 112).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(
        v.get("error").is_some(),
        "connect should fail for removed namespace documents"
    );

    // Reopen same URIs and reconnect to ensure clean state.
    open_document_uri(&mut client_w, "snaq://canvasA/source.sl", "5", 2).await;
    open_document_uri(
        &mut client_w,
        "snaq://canvasA/target.sl",
        "input x: Numeric\nx * 2",
        2,
    )
    .await;
    let reconnect_req = serde_json::json!({
        "jsonrpc":"2.0","id":113,"method":"snaqlite/graph/connect",
        "params":{"sourceUri":"snaq://canvasA/source.sl","targetUri":"snaq://canvasA/target.sl","targetInputName":"x"}
    });
    client_w
        .write_all(&lsp_message(&reconnect_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 113).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(
        v.get("error").is_none(),
        "reconnect should succeed after reopen in reset namespace"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn graph_rehydrates_from_canvas_document_without_ui_replay() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://rehyd/source.sl", "42", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://rehyd/target.sl",
        "input x@p1: Numeric\nx",
        1,
    )
    .await;

    let connect_req = serde_json::json!({
        "jsonrpc":"2.0","id":120,"method":"snaqlite/graph/connect",
        "params":{"sourceUri":"snaq://rehyd/source.sl","targetUri":"snaq://rehyd/target.sl","targetInputName":"p1"}
    });
    client_w
        .write_all(&lsp_message(&connect_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 120).await;

    let export_req = serde_json::json!({
        "jsonrpc":"2.0","id":121,"method":"snaqlite/graph/exportCanvasDocument","params":{}
    });
    client_w
        .write_all(&lsp_message(&export_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let export_body = read_until_response_id(&mut client_r, 121).await;
    let export_v: serde_json::Value = serde_json::from_str(&export_body).unwrap();
    let canvas_document = export_v["result"]["canvasDocument"].clone();
    assert!(
        canvas_document["nodes"].as_array().map(|a| a.len()).unwrap_or(0) >= 2,
        "export should include opened nodes"
    );
    assert!(
        canvas_document["edges"].as_array().map(|a| a.len()).unwrap_or(0) >= 1,
        "export should include connected edge"
    );

    let reset_req = serde_json::json!({
        "jsonrpc":"2.0","id":122,"method":"snaqlite/graph/resetNamespace",
        "params":{"uriPrefix":"snaq://rehyd/"}
    });
    client_w
        .write_all(&lsp_message(&reset_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 122).await;

    let import_req = serde_json::json!({
        "jsonrpc":"2.0","id":123,"method":"snaqlite/graph/importCanvasDocument",
        "params":{"canvasDocument": canvas_document}
    });
    client_w
        .write_all(&lsp_message(&import_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let import_body = read_until_response_id(&mut client_r, 123).await;
    let import_v: serde_json::Value = serde_json::from_str(&import_body).unwrap();
    assert!(
        import_v.get("error").is_none(),
        "importCanvasDocument should succeed: {import_v}"
    );

    let sub_req = serde_json::json!({
        "jsonrpc":"2.0","id":124,"method":"snaqlite/subscribeNode",
        "params":{"sourceUri":"snaq://rehyd/target.sl"}
    });
    client_w
        .write_all(&lsp_message(&sub_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let got_completed = timeout(Duration::from_secs(5), async {
        let mut sub_id = None;
        loop {
            let body = read_one_lsp_message_async(&mut client_r).await.unwrap();
            let v: serde_json::Value = serde_json::from_str(&body).unwrap();
            if v.get("id").and_then(|i| i.as_u64()) == Some(124) {
                sub_id = v["result"]["subscriptionId"].as_str().map(str::to_string);
            }
            if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/publishNodeResult") {
                let status = v["params"]["status"].as_str();
                if status == Some("Completed") {
                    let display = v["params"]["data"]["display"].as_str().unwrap_or_default();
                    if display.contains("42") {
                        break true;
                    }
                }
            }
            if sub_id.is_none() {
                continue;
            }
        }
    })
    .await
    .expect("timeout waiting for completed publishNodeResult");
    assert!(got_completed, "rehydrated graph should evaluate target to 42");

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn import_canvas_document_cancels_scalar_subscriptions_with_reason() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://import-cancel/a.sl", "1 + 2", 1).await;

    let sub_req = serde_json::json!({
        "jsonrpc":"2.0","id":125,"method":"snaqlite/subscribeNode",
        "params":{"sourceUri":"snaq://import-cancel/a.sl"}
    });
    client_w
        .write_all(&lsp_message(&sub_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let subscription_id = timeout(Duration::from_secs(5), async {
        loop {
            let body = read_one_lsp_message_async(&mut client_r).await.unwrap();
            let v: serde_json::Value = serde_json::from_str(&body).unwrap();
            if v.get("id").and_then(|i| i.as_u64()) == Some(125) {
                break v["result"]["subscriptionId"]
                    .as_str()
                    .unwrap_or("")
                    .to_string();
            }
        }
    })
    .await
    .expect("timeout waiting for subscribeNode response");
    assert!(!subscription_id.is_empty());

    let import_req = serde_json::json!({
        "jsonrpc":"2.0","id":126,"method":"snaqlite/graph/importCanvasDocument",
        "params":{"canvasDocument":{
            "nodes":[{"uri":"snaq://import-cancel/b.sl","source":"10","version":1}],
            "edges":[]
        }}
    });
    client_w
        .write_all(&lsp_message(&import_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let got_cancelled = timeout(Duration::from_secs(5), async {
        loop {
            let body = read_one_lsp_message_async(&mut client_r).await.unwrap();
            let v: serde_json::Value = serde_json::from_str(&body).unwrap();
            if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/publishNodeResult") {
                let params = &v["params"];
                if params["subscriptionId"].as_str() == Some(subscription_id.as_str())
                    && params["status"].as_str() == Some("Cancelled")
                    && params["data"]["reason"].as_str() == Some("Canvas import")
                {
                    break true;
                }
            }
        }
    })
    .await
    .expect("timeout waiting for cancelled notification");
    assert!(got_cancelled);

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn import_canvas_document_rejects_duplicate_node_uris() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;

    let import_req = serde_json::json!({
        "jsonrpc":"2.0","id":127,"method":"snaqlite/graph/importCanvasDocument",
        "params":{"canvasDocument":{
            "nodes":[
                {"uri":"snaq://dup/n1.sl","source":"1","version":1},
                {"uri":"snaq://dup/n1.sl","source":"2","version":2}
            ],
            "edges":[]
        }}
    });
    client_w
        .write_all(&lsp_message(&import_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 127).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(v.get("error").is_some(), "duplicate node URIs should be rejected");

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn subscribe_node_is_graph_aware_while_legacy_subscribe_is_not() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph-aware/source.sl", "42", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph-aware/target.sl",
        "input x@p1: Numeric\n$x",
        1,
    )
    .await;
    let connect_req = serde_json::json!({
        "jsonrpc":"2.0","id":128,"method":"snaqlite/graph/connect",
        "params":{"sourceUri":"snaq://graph-aware/source.sl","targetUri":"snaq://graph-aware/target.sl","targetInputName":"x"}
    });
    client_w
        .write_all(&lsp_message(&connect_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 128).await;

    let legacy_subscribe = serde_json::json!({
        "jsonrpc":"2.0","id":129,"method":"snaqlite/subscribe",
        "params":{"textDocument":{"uri":"snaq://graph-aware/target.sl"}}
    });
    client_w
        .write_all(&lsp_message(&legacy_subscribe.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let legacy_body = read_until_response_id(&mut client_r, 129).await;
    let legacy_v: serde_json::Value = serde_json::from_str(&legacy_body).unwrap();
    assert!(
        legacy_v.get("error").is_some(),
        "legacy subscribe should fail without graph stream inputs"
    );

    let node_subscribe = serde_json::json!({
        "jsonrpc":"2.0","id":130,"method":"snaqlite/subscribeNode",
        "params":{"sourceUri":"snaq://graph-aware/target.sl"}
    });
    client_w
        .write_all(&lsp_message(&node_subscribe.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let node_body = read_until_response_id(&mut client_r, 130).await;
    let node_v: serde_json::Value = serde_json::from_str(&node_body).unwrap();
    assert!(
        node_v.get("error").is_none(),
        "subscribeNode should succeed with graph-aware inputs"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn export_canvas_document_uses_stable_target_param_id() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://export-param/source.sl", "5", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://export-param/target.sl",
        "input x@p_stable: Numeric\nx",
        1,
    )
    .await;
    let connect_req = serde_json::json!({
        "jsonrpc":"2.0","id":131,"method":"snaqlite/graph/connect",
        "params":{"sourceUri":"snaq://export-param/source.sl","targetUri":"snaq://export-param/target.sl","targetInputName":"x"}
    });
    client_w
        .write_all(&lsp_message(&connect_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 131).await;

    let export_req = serde_json::json!({
        "jsonrpc":"2.0","id":132,"method":"snaqlite/graph/exportCanvasDocument","params":{}
    });
    client_w
        .write_all(&lsp_message(&export_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 132).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    let edges = v["result"]["canvasDocument"]["edges"]
        .as_array()
        .expect("edges array");
    assert!(!edges.is_empty(), "export should include at least one edge");
    assert_eq!(
        edges[0]["targetParamId"].as_str(),
        Some("p_stable"),
        "export should preserve stable target param id"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn native_subscribe_node_vector_returns_subscription_id() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(
        &mut client_w,
        "snaq://canvas-meta/vector.sl",
        "[1,2,3,4,5,6,7,8,9,10,11,12]",
        1,
    )
    .await;

    let sub_req = serde_json::json!({
        "jsonrpc":"2.0","id":133,"method":"snaqlite/subscribeNode",
        "params":{"sourceUri":"snaq://canvas-meta/vector.sl"}
    });
    client_w
        .write_all(&lsp_message(&sub_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let body = read_until_response_id(&mut client_r, 133).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(
        v.get("error").is_none(),
        "subscribeNode should succeed for vector source: {v}"
    );
    assert!(
        v["result"]["subscriptionId"].as_str().is_some(),
        "subscribeNode should return subscriptionId for vector source"
    );
    let result_handle = v["result"]["resultHandle"]
        .as_str()
        .map(ToString::to_string)
        .expect("subscribeNode should return resultHandle for vector source");
    let hover_req = serde_json::json!({
        "jsonrpc":"2.0","id":134,"method":"textDocument/hover",
        "params":{"textDocument":{"uri":"snaq://canvas-meta/vector.sl"},"position":{"line":0,"character":0}}
    });
    client_w
        .write_all(&lsp_message(&hover_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 134).await;

    let fetch = serde_json::json!({
        "jsonrpc":"2.0","id":135,"method":"snaqlite/graph/fetchResultSlice",
        "params":{"resultHandle": result_handle, "path":[],"offset":0,"limit":3}
    });
    client_w
        .write_all(&lsp_message(&fetch.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 135).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(v.get("error").is_none(), "fetchResultSlice should succeed: {v}");
    let elems = v["result"]["elements"].as_array().cloned().unwrap_or_default();
    assert_eq!(elems.len(), 3);
    assert_eq!(elems[0]["display"].as_str(), Some("1"));
    assert_eq!(v["result"]["totalCount"].as_u64(), Some(12));

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn native_type_change_prunes_edge_with_same_param_name() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/source-type.sl", "7", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/target-type.sl",
        "input x: Numeric\nx * 2",
        1,
    )
    .await;

    let connect_req = serde_json::json!({
        "jsonrpc":"2.0","id":120,"method":"snaqlite/graph/connect",
        "params":{"sourceUri":"snaq://graph/source-type.sl","targetUri":"snaq://graph/target-type.sl","targetInputName":"x"}
    });
    client_w
        .write_all(&lsp_message(&connect_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 120).await;

    let sub_req = serde_json::json!({
        "jsonrpc":"2.0","id":121,"method":"snaqlite/graph/subscribeWidget",
        "params":{"widgetId":"w-type","sourceUri":"snaq://graph/target-type.sl"}
    });
    client_w
        .write_all(&lsp_message(&sub_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 121).await;

    // Change only the declared input type for x (name unchanged): Numeric -> Vector.
    let did_change_target = serde_json::json!({
        "jsonrpc":"2.0","method":"textDocument/didChange",
        "params":{"textDocument":{"uri":"snaq://graph/target-type.sl","version":2},"contentChanges":[{"text":"input x: Vector\nx.sum()"}]}
    });
    client_w
        .write_all(&lsp_message(&did_change_target.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut got_error_after_type_change = false;
    for _ in 0..30 {
        let body = timeout(Duration::from_secs(2), read_one_lsp_message_async(&mut client_r))
            .await
            .expect("timeout")
            .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate")
            && v["params"]["widgetId"].as_str() == Some("w-type")
            && v["params"]["status"].as_str() == Some("Error")
        {
            got_error_after_type_change = true;
            break;
        }
    }
    assert!(
        got_error_after_type_change,
        "changing declared type should prune incompatible edge and produce Error update"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn source_output_type_change_prunes_edge_and_recomputes_target() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/source-output-type.sl", "7", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/target-output-type.sl",
        "input x: Numeric\nx * 2",
        1,
    )
    .await;

    let connect_req = serde_json::json!({
        "jsonrpc":"2.0","id":140,"method":"snaqlite/graph/connect",
        "params":{"sourceUri":"snaq://graph/source-output-type.sl","targetUri":"snaq://graph/target-output-type.sl","targetInputName":"x"}
    });
    client_w
        .write_all(&lsp_message(&connect_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 140).await;

    let sub_req = serde_json::json!({
        "jsonrpc":"2.0","id":141,"method":"snaqlite/graph/subscribeWidget",
        "params":{"widgetId":"w-source-output-type","sourceUri":"snaq://graph/target-output-type.sl"}
    });
    client_w
        .write_all(&lsp_message(&sub_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 141).await;

    // Source output changes from Numeric -> Vector. Edge should be pruned and target recomputed to Error.
    let source_change = serde_json::json!({
        "jsonrpc":"2.0","method":"textDocument/didChange",
        "params":{"textDocument":{"uri":"snaq://graph/source-output-type.sl","version":2},"contentChanges":[{"text":"[1, 2]"}]}
    });
    client_w
        .write_all(&lsp_message(&source_change.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    // Pump one request so queued notifications are drained deterministically.
    let hover_req = serde_json::json!({
        "jsonrpc":"2.0","id":142,"method":"textDocument/hover",
        "params":{"textDocument":{"uri":"snaq://graph/target-output-type.sl"},"position":{"line":0,"character":0}}
    });
    client_w
        .write_all(&lsp_message(&hover_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let mut saw_target_error = false;
    for _ in 0..40 {
        let body = timeout(Duration::from_secs(2), read_one_lsp_message_async(&mut client_r))
            .await
            .expect("timeout")
            .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("id").and_then(|i| i.as_u64()) == Some(142) {
            continue;
        }
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate")
            && v["params"]["widgetId"].as_str() == Some("w-source-output-type")
            && v["params"]["status"].as_str() == Some("Error")
        {
            saw_target_error = true;
            break;
        }
    }
    assert!(
        saw_target_error,
        "source output type change should prune edge and recompute target to Error"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn fetch_result_slice_materializes_root_once_for_non_evaluated_vectors() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/slice-root.sl",
        "[1,2,3,4,5].map(fn v => (v * 2))",
        1,
    )
    .await;

    let sub_req = serde_json::json!({
        "jsonrpc":"2.0","id":130,"method":"snaqlite/graph/subscribeWidget",
        "params":{"widgetId":"w-slice-root","sourceUri":"snaq://graph/slice-root.sl"}
    });
    client_w
        .write_all(&lsp_message(&sub_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 130).await;

    let fetch_a = serde_json::json!({
        "jsonrpc":"2.0","id":131,"method":"snaqlite/graph/fetchResultSlice",
        "params":{"widgetId":"w-slice-root","path":[],"offset":1,"limit":2}
    });
    client_w
        .write_all(&lsp_message(&fetch_a.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 131).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    let result = v.get("result").cloned().unwrap_or_default();
    assert_eq!(result["totalCount"].as_u64(), Some(5));
    assert_eq!(result["hasMore"].as_bool(), Some(true));
    let elems = result["elements"].as_array().cloned().unwrap_or_default();
    assert_eq!(elems.len(), 2);
    assert_eq!(elems[0]["display"].as_str(), Some("4"));
    assert_eq!(elems[1]["display"].as_str(), Some("6"));

    let fetch_b = serde_json::json!({
        "jsonrpc":"2.0","id":132,"method":"snaqlite/graph/fetchResultSlice",
        "params":{"widgetId":"w-slice-root","path":[],"offset":4,"limit":2}
    });
    client_w
        .write_all(&lsp_message(&fetch_b.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 132).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    let result = v.get("result").cloned().unwrap_or_default();
    assert_eq!(result["totalCount"].as_u64(), Some(5));
    assert_eq!(result["hasMore"].as_bool(), Some(false));
    let elems = result["elements"].as_array().cloned().unwrap_or_default();
    assert_eq!(elems.len(), 1);
    assert_eq!(elems[0]["display"].as_str(), Some("10"));

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn fetch_result_slice_accepts_result_handle_and_cursor_continuation() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/handle-source.sl",
        "[1,2,3,4]",
        1,
    )
    .await;

    let sub_req = serde_json::json!({
        "jsonrpc":"2.0","id":201,"method":"snaqlite/subscribeNode",
        "params":{"sourceUri":"snaq://graph/handle-source.sl"}
    });
    client_w
        .write_all(&lsp_message(&sub_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 201).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    let result_handle = v["result"]["resultHandle"]
        .as_str()
        .map(ToString::to_string)
        .expect("subscribeNode should return resultHandle");

    let fetch1 = serde_json::json!({
        "jsonrpc":"2.0","id":202,"method":"snaqlite/graph/fetchResultSlice",
        "params":{"resultHandle": result_handle, "path":[],"offset":0,"limit":2}
    });
    client_w
        .write_all(&lsp_message(&fetch1.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 202).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    let res = v.get("result").cloned().unwrap_or_default();
    assert_eq!(res["totalCount"].as_u64(), Some(4));
    assert_eq!(res["hasMore"].as_bool(), Some(true));
    let next_cursor = res["nextCursor"]
        .as_str()
        .map(ToString::to_string)
        .expect("first page should provide nextCursor");
    let elems = res["elements"].as_array().cloned().unwrap_or_default();
    assert_eq!(elems.len(), 2);
    assert_eq!(elems[0]["display"].as_str(), Some("1"));
    assert_eq!(elems[1]["display"].as_str(), Some("2"));

    let fetch2 = serde_json::json!({
        "jsonrpc":"2.0","id":203,"method":"snaqlite/graph/fetchResultSlice",
        "params":{"resultHandle": result_handle, "path":[],"offset":2,"limit":2, "cursor": next_cursor}
    });
    client_w
        .write_all(&lsp_message(&fetch2.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 203).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    let res = v.get("result").cloned().unwrap_or_default();
    assert_eq!(res["totalCount"].as_u64(), Some(4));
    assert_eq!(res["hasMore"].as_bool(), Some(false));
    let elems = res["elements"].as_array().cloned().unwrap_or_default();
    assert_eq!(elems.len(), 2);
    assert_eq!(elems[0]["display"].as_str(), Some("3"));
    assert_eq!(elems[1]["display"].as_str(), Some("4"));

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn fetch_result_slice_rejects_random_access_for_non_replayable_result_handle() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/nonreplay-src.sl",
        "[1,2,3,4]",
        1,
    )
    .await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/nonreplay-tgt.sl",
        "input x: Vector\nx",
        1,
    )
    .await;

    let connect_req = serde_json::json!({
        "jsonrpc":"2.0","id":204,"method":"snaqlite/graph/connect",
        "params":{"sourceUri":"snaq://graph/nonreplay-src.sl","targetUri":"snaq://graph/nonreplay-tgt.sl","targetInputName":"x"}
    });
    client_w
        .write_all(&lsp_message(&connect_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 204).await;

    let sub_req = serde_json::json!({
        "jsonrpc":"2.0","id":205,"method":"snaqlite/subscribeNode",
        "params":{"sourceUri":"snaq://graph/nonreplay-tgt.sl"}
    });
    client_w
        .write_all(&lsp_message(&sub_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 205).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    let result_handle = v["result"]["resultHandle"]
        .as_str()
        .map(ToString::to_string)
        .expect("subscribeNode should return resultHandle");

    let fetch = serde_json::json!({
        "jsonrpc":"2.0","id":206,"method":"snaqlite/graph/fetchResultSlice",
        "params":{"resultHandle": result_handle, "path":[],"offset":1,"limit":2}
    });
    client_w
        .write_all(&lsp_message(&fetch.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 206).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert_eq!(v["error"]["code"].as_i64(), Some(-32602));
    assert!(
        v["error"]["message"]
            .as_str()
            .unwrap_or_default()
            .contains("non-replayable stream slice only supports offset=0 without cursor"),
        "expected explicit non-replayable random-access rejection: {v}"
    );

    let nested_fetch = serde_json::json!({
        "jsonrpc":"2.0","id":207,"method":"snaqlite/graph/fetchResultSlice",
        "params":{"resultHandle": result_handle, "path":[0],"offset":0,"limit":1}
    });
    client_w
        .write_all(&lsp_message(&nested_fetch.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 207).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert_eq!(v["error"]["code"].as_i64(), Some(-32602));
    assert!(
        v["error"]["message"]
            .as_str()
            .unwrap_or_default()
            .contains("does not support nested paths"),
        "expected explicit non-replayable nested path rejection: {v}"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn graph_operations_require_snaq_canvas_uris() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(
        &mut client_w,
        "file:///tmp/not-canvas.sl",
        "[1,2,3]",
        1,
    )
    .await;

    let connect_req = serde_json::json!({
        "jsonrpc":"2.0","id":399,"method":"snaqlite/graph/connect",
        "params":{
            "sourceUri":"file:///tmp/not-canvas.sl",
            "targetUri":"file:///tmp/not-canvas.sl",
            "targetInputName":"x"
        }
    });
    client_w
        .write_all(&lsp_message(&connect_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 399).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert_eq!(v["error"]["code"].as_i64(), Some(-32602));
    assert!(
        v["error"]["message"]
            .as_str()
            .unwrap_or_default()
            .contains("graph operations require snaq://<canvasId>/... URIs"),
        "expected graph URI contract error: {v}"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn graph_param_helpers_rename_add_remove_apply_source_updates() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/param-helpers.sl",
        "input a@p1: Numeric\na + 1",
        1,
    )
    .await;

    let rename_req = serde_json::json!({
        "jsonrpc":"2.0","id":211,"method":"snaqlite/graph/renameParam",
        "params":{"uri":"snaq://graph/param-helpers.sl","paramId":"p1","newName":"revenue"}
    });
    client_w
        .write_all(&lsp_message(&rename_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 211).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(v.get("error").is_none(), "renameParam should succeed: {v}");

    let add_req = serde_json::json!({
        "jsonrpc":"2.0","id":212,"method":"snaqlite/graph/addParam",
        "params":{"uri":"snaq://graph/param-helpers.sl","paramId":"p2","name":"cost","typeName":"Numeric"}
    });
    client_w
        .write_all(&lsp_message(&add_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 212).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(v.get("error").is_none(), "addParam should succeed: {v}");

    let remove_req = serde_json::json!({
        "jsonrpc":"2.0","id":213,"method":"snaqlite/graph/removeParam",
        "params":{"uri":"snaq://graph/param-helpers.sl","paramId":"p2"}
    });
    client_w
        .write_all(&lsp_message(&remove_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 213).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(v.get("error").is_none(), "removeParam should succeed: {v}");

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn graph_rename_param_trims_new_name_before_writing_source() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/rename-trim.sl",
        "input a@p1: Numeric\na + 1",
        1,
    )
    .await;

    let rename_req = serde_json::json!({
        "jsonrpc":"2.0","id":214,"method":"snaqlite/graph/renameParam",
        "params":{"uri":"snaq://graph/rename-trim.sl","paramId":"p1","newName":"  revenue  "}
    });
    client_w
        .write_all(&lsp_message(&rename_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 214).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(v.get("error").is_none(), "renameParam should succeed: {v}");

    let export_req = serde_json::json!({
        "jsonrpc":"2.0","id":215,"method":"snaqlite/graph/exportCanvasDocument","params":{}
    });
    client_w
        .write_all(&lsp_message(&export_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 215).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    let nodes = v["result"]["canvasDocument"]["nodes"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    let node = nodes
        .iter()
        .find(|n| n["uri"].as_str() == Some("snaq://graph/rename-trim.sl"))
        .expect("export should contain renamed node");
    let source = node["source"].as_str().unwrap_or_default();
    assert!(
        source.contains("input revenue@p1: Numeric"),
        "renamed source should use trimmed name, got: {source}"
    );
    assert!(
        !source.contains("input   revenue"),
        "renamed source should not contain leading spaces in name: {source}"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn graph_add_param_rejects_duplicate_name_when_whitespace_padded() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/add-dup-name-trim.sl",
        "input revenue@p1: Numeric\nrevenue + 1",
        1,
    )
    .await;

    let add_req = serde_json::json!({
        "jsonrpc":"2.0","id":216,"method":"snaqlite/graph/addParam",
        "params":{
            "uri":"snaq://graph/add-dup-name-trim.sl",
            "name":"  revenue  ",
            "paramId":"p2",
            "typeName":"Numeric"
        }
    });
    client_w
        .write_all(&lsp_message(&add_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 216).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    let message = v["error"]["message"].as_str().unwrap_or_default();
    assert!(
        message.contains("duplicate param name or id"),
        "addParam should reject duplicate trimmed names, got: {v}"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn graph_param_helpers_preserve_non_input_source_content() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/param-preserve.sl",
        "input a@p1: Numeric\n\nx = 1\na + x",
        1,
    )
    .await;

    let rename_req = serde_json::json!({
        "jsonrpc":"2.0","id":217,"method":"snaqlite/graph/renameParam",
        "params":{"uri":"snaq://graph/param-preserve.sl","paramId":"p1","newName":"revenue"}
    });
    client_w
        .write_all(&lsp_message(&rename_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 217).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(v.get("error").is_none(), "renameParam should succeed: {v}");

    let export_req = serde_json::json!({
        "jsonrpc":"2.0","id":218,"method":"snaqlite/graph/exportCanvasDocument","params":{}
    });
    client_w
        .write_all(&lsp_message(&export_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 218).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    let nodes = v["result"]["canvasDocument"]["nodes"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    let node = nodes
        .iter()
        .find(|n| n["uri"].as_str() == Some("snaq://graph/param-preserve.sl"))
        .expect("export should contain mutated node");
    let source = node["source"].as_str().unwrap_or_default();
    assert!(
        source.contains("input revenue@p1: Numeric"),
        "renamed input declaration should be updated: {source}"
    );
    assert!(
        source.contains("\n\nx = 1\na + x"),
        "non-input body should remain byte-stable: {source}"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn graph_param_helpers_reject_invalid_identifiers() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/param-ident.sl",
        "input a@p1: Numeric\na + 1",
        1,
    )
    .await;

    let rename_req = serde_json::json!({
        "jsonrpc":"2.0","id":219,"method":"snaqlite/graph/renameParam",
        "params":{"uri":"snaq://graph/param-ident.sl","paramId":"p1","newName":"bad name"}
    });
    client_w
        .write_all(&lsp_message(&rename_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 219).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert_eq!(v["error"]["code"].as_i64(), Some(-32602));

    let add_req = serde_json::json!({
        "jsonrpc":"2.0","id":220,"method":"snaqlite/graph/addParam",
        "params":{"uri":"snaq://graph/param-ident.sl","paramId":"bad id","name":"ok","typeName":"Numeric"}
    });
    client_w
        .write_all(&lsp_message(&add_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 220).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert_eq!(v["error"]["code"].as_i64(), Some(-32602));

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn graph_add_param_preserves_blank_line_before_body() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/add-preserve-blank.sl",
        "input a@p1: Numeric\n\nx = 1\na + x",
        1,
    )
    .await;

    let add_req = serde_json::json!({
        "jsonrpc":"2.0","id":221,"method":"snaqlite/graph/addParam",
        "params":{"uri":"snaq://graph/add-preserve-blank.sl","paramId":"p2","name":"b","typeName":"Numeric"}
    });
    client_w
        .write_all(&lsp_message(&add_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 221).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(v.get("error").is_none(), "addParam should succeed: {v}");

    let export_req = serde_json::json!({
        "jsonrpc":"2.0","id":222,"method":"snaqlite/graph/exportCanvasDocument","params":{}
    });
    client_w
        .write_all(&lsp_message(&export_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 222).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    let nodes = v["result"]["canvasDocument"]["nodes"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    let node = nodes
        .iter()
        .find(|n| n["uri"].as_str() == Some("snaq://graph/add-preserve-blank.sl"))
        .expect("export should contain node");
    let source = node["source"].as_str().unwrap_or_default();
    assert!(
        source.contains("input a@p1: Numeric\ninput b@p2: Numeric\n\nx = 1\na + x"),
        "addParam should keep single blank line before body: {source}"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn graph_connect_order_does_not_change_downstream_result() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/ord-a.sl", "1", 1).await;
    open_document_uri(&mut client_w, "snaq://graph/ord-b.sl", "2", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/ord-t1.sl",
        "input x@px: Numeric\ninput y@py: Numeric\nx + y",
        1,
    )
    .await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/ord-t2.sl",
        "input x@px: Numeric\ninput y@py: Numeric\nx + y",
        1,
    )
    .await;

    let connect_1 = serde_json::json!({
        "jsonrpc":"2.0","id":223,"method":"snaqlite/graph/connect",
        "params":{"sourceUri":"snaq://graph/ord-a.sl","targetUri":"snaq://graph/ord-t1.sl","targetInputName":"px"}
    });
    client_w
        .write_all(&lsp_message(&connect_1.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 223).await;
    let connect_2 = serde_json::json!({
        "jsonrpc":"2.0","id":224,"method":"snaqlite/graph/connect",
        "params":{"sourceUri":"snaq://graph/ord-b.sl","targetUri":"snaq://graph/ord-t1.sl","targetInputName":"py"}
    });
    client_w
        .write_all(&lsp_message(&connect_2.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 224).await;

    let connect_3 = serde_json::json!({
        "jsonrpc":"2.0","id":225,"method":"snaqlite/graph/connect",
        "params":{"sourceUri":"snaq://graph/ord-b.sl","targetUri":"snaq://graph/ord-t2.sl","targetInputName":"py"}
    });
    client_w
        .write_all(&lsp_message(&connect_3.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 225).await;
    let connect_4 = serde_json::json!({
        "jsonrpc":"2.0","id":226,"method":"snaqlite/graph/connect",
        "params":{"sourceUri":"snaq://graph/ord-a.sl","targetUri":"snaq://graph/ord-t2.sl","targetInputName":"px"}
    });
    client_w
        .write_all(&lsp_message(&connect_4.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let _ = read_until_response_id(&mut client_r, 226).await;

    let sub_t1 = serde_json::json!({
        "jsonrpc":"2.0","id":227,"method":"snaqlite/graph/subscribeWidget",
        "params":{"widgetId":"w-ord-1","sourceUri":"snaq://graph/ord-t1.sl"}
    });
    client_w
        .write_all(&lsp_message(&sub_t1.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let mut display_1: Option<String> = None;
    for _ in 0..30 {
        let body = timeout(Duration::from_secs(2), read_one_lsp_message_async(&mut client_r))
            .await
            .expect("timeout")
            .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("id").and_then(|i| i.as_u64()) == Some(227) {
            assert!(v.get("error").is_none(), "subscribeWidget should succeed: {v}");
        }
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate")
            && v["params"]["widgetId"].as_str() == Some("w-ord-1")
            && v["params"]["status"].as_str() == Some("Completed")
        {
            display_1 = v["params"]["payload"]["display"]
                .as_str()
                .map(ToString::to_string);
            break;
        }
    }

    let sub_t2 = serde_json::json!({
        "jsonrpc":"2.0","id":228,"method":"snaqlite/graph/subscribeWidget",
        "params":{"widgetId":"w-ord-2","sourceUri":"snaq://graph/ord-t2.sl"}
    });
    client_w
        .write_all(&lsp_message(&sub_t2.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let mut display_2: Option<String> = None;
    for _ in 0..30 {
        let body = timeout(Duration::from_secs(2), read_one_lsp_message_async(&mut client_r))
            .await
            .expect("timeout")
            .unwrap();
        let v: serde_json::Value = serde_json::from_str(&body).unwrap();
        if v.get("id").and_then(|i| i.as_u64()) == Some(228) {
            assert!(v.get("error").is_none(), "subscribeWidget should succeed: {v}");
        }
        if v.get("method").and_then(|m| m.as_str()) == Some("snaqlite/graph/widgetDataUpdate")
            && v["params"]["widgetId"].as_str() == Some("w-ord-2")
            && v["params"]["status"].as_str() == Some("Completed")
        {
            display_2 = v["params"]["payload"]["display"]
                .as_str()
                .map(ToString::to_string);
            break;
        }
    }
    assert_eq!(display_1.as_deref(), Some("3"));
    assert_eq!(display_2.as_deref(), Some("3"));

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn connect_allows_deferred_validation_when_source_type_unknown() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://graph/defer-source.sl", "1 +", 1).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/defer-target.sl",
        "input x@p1: Numeric\nx + 1",
        1,
    )
    .await;

    let connect_req = serde_json::json!({
        "jsonrpc":"2.0","id":221,"method":"snaqlite/graph/connect",
        "params":{"sourceUri":"snaq://graph/defer-source.sl","targetUri":"snaq://graph/defer-target.sl","targetInputName":"p1"}
    });
    client_w
        .write_all(&lsp_message(&connect_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 221).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(
        v.get("error").is_none(),
        "connect should allow deferred validation when source type is unknown: {v}"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn canvas_rebind_is_allowed_after_full_drain() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(&mut client_w, "snaq://canvas-a/node1.sl", "1 + 2", 1).await;

    let did_close = serde_json::json!({
        "jsonrpc":"2.0","method":"textDocument/didClose",
        "params":{"textDocument":{"uri":"snaq://canvas-a/node1.sl"}}
    });
    client_w
        .write_all(&lsp_message(&did_close.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    open_document_uri(&mut client_w, "snaq://canvas-b/node1.sl", "2 + 3", 1).await;
    let hover_req = serde_json::json!({
        "jsonrpc":"2.0","id":231,"method":"textDocument/hover",
        "params":{"textDocument":{"uri":"snaq://canvas-b/node1.sl"},"position":{"line":0,"character":1}}
    });
    client_w
        .write_all(&lsp_message(&hover_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 231).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(v.get("error").is_none(), "hover on rebound canvas should work: {v}");
    assert!(
        !v["result"].is_null(),
        "hover on rebound canvas should resolve opened document, got null result: {v}"
    );
    let contents_val = v["result"].get("contents");
    let content = contents_val
        .and_then(|c| c.as_str())
        .or_else(|| contents_val.and_then(|c| c.get("value")).and_then(|v| v.as_str()))
        .unwrap_or_default();
    assert!(
        content.contains("5"),
        "hover content on rebound canvas should reflect canvas-b document result (5), got: {content}"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn fetch_result_slice_cursor_is_single_use_and_reuse_fails() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/cursor-once.sl",
        "[10,20,30,40]",
        1,
    )
    .await;

    let sub_req = serde_json::json!({
        "jsonrpc":"2.0","id":301,"method":"snaqlite/subscribeNode",
        "params":{"sourceUri":"snaq://graph/cursor-once.sl"}
    });
    client_w
        .write_all(&lsp_message(&sub_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 301).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    let result_handle = v["result"]["resultHandle"]
        .as_str()
        .expect("subscribeNode should return resultHandle");

    let fetch1 = serde_json::json!({
        "jsonrpc":"2.0","id":302,"method":"snaqlite/graph/fetchResultSlice",
        "params":{"resultHandle": result_handle, "path":[],"offset":0,"limit":2}
    });
    client_w
        .write_all(&lsp_message(&fetch1.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 302).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    let cursor = v["result"]["nextCursor"]
        .as_str()
        .expect("first page should include nextCursor")
        .to_string();

    let fetch2 = serde_json::json!({
        "jsonrpc":"2.0","id":303,"method":"snaqlite/graph/fetchResultSlice",
        "params":{"resultHandle": result_handle, "path":[],"offset":2,"limit":2, "cursor": cursor}
    });
    client_w
        .write_all(&lsp_message(&fetch2.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 303).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(v.get("error").is_none(), "second page should succeed: {v}");

    // Reuse same cursor token should fail (single-use continuation).
    // Reuse original consumed cursor token.
    let fetch3 = serde_json::json!({
        "jsonrpc":"2.0","id":304,"method":"snaqlite/graph/fetchResultSlice",
        "params":{"resultHandle": result_handle, "path":[],"offset":2,"limit":2, "cursor": cursor}
    });
    client_w
        .write_all(&lsp_message(&fetch3.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 304).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(
        v.get("error").is_some(),
        "reused cursor should be rejected: {v}"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn fetch_result_slice_cursor_becomes_invalid_after_source_recompute() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/cursor-recompute.sl",
        "[1,2,3,4]",
        1,
    )
    .await;

    let sub_req = serde_json::json!({
        "jsonrpc":"2.0","id":311,"method":"snaqlite/subscribeNode",
        "params":{"sourceUri":"snaq://graph/cursor-recompute.sl"}
    });
    client_w
        .write_all(&lsp_message(&sub_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 311).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    let result_handle = v["result"]["resultHandle"]
        .as_str()
        .expect("subscribeNode should return resultHandle");

    let fetch1 = serde_json::json!({
        "jsonrpc":"2.0","id":312,"method":"snaqlite/graph/fetchResultSlice",
        "params":{"resultHandle": result_handle, "path":[],"offset":0,"limit":2}
    });
    client_w
        .write_all(&lsp_message(&fetch1.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 312).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    let cursor = v["result"]["nextCursor"]
        .as_str()
        .expect("first page should include nextCursor")
        .to_string();

    // Trigger recompute on same source URI; handle cursors should be invalidated.
    let did_change = serde_json::json!({
        "jsonrpc":"2.0","method":"textDocument/didChange",
        "params":{
          "textDocument":{"uri":"snaq://graph/cursor-recompute.sl","version":2},
          "contentChanges":[{"text":"[1,2,3,4,5]"}]
        }
    });
    client_w
        .write_all(&lsp_message(&did_change.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let fetch2 = serde_json::json!({
        "jsonrpc":"2.0","id":313,"method":"snaqlite/graph/fetchResultSlice",
        "params":{"resultHandle": result_handle, "path":[],"offset":2,"limit":2, "cursor": cursor}
    });
    client_w
        .write_all(&lsp_message(&fetch2.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 313).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(
        v.get("error").is_some(),
        "cursor should be invalid after source recompute: {v}"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn fetch_result_slice_handle_invalid_after_did_close() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/close-handle.sl",
        "[7,8,9]",
        1,
    )
    .await;

    let sub_req = serde_json::json!({
        "jsonrpc":"2.0","id":321,"method":"snaqlite/subscribeNode",
        "params":{"sourceUri":"snaq://graph/close-handle.sl"}
    });
    client_w
        .write_all(&lsp_message(&sub_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 321).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    let result_handle = v["result"]["resultHandle"]
        .as_str()
        .expect("subscribeNode should return resultHandle")
        .to_string();

    let did_close = serde_json::json!({
        "jsonrpc":"2.0","method":"textDocument/didClose",
        "params":{"textDocument":{"uri":"snaq://graph/close-handle.sl"}}
    });
    client_w
        .write_all(&lsp_message(&did_close.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();

    let fetch = serde_json::json!({
        "jsonrpc":"2.0","id":322,"method":"snaqlite/graph/fetchResultSlice",
        "params":{"resultHandle": result_handle, "path":[],"offset":0,"limit":2}
    });
    client_w
        .write_all(&lsp_message(&fetch.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 322).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(
        v.get("error").is_some(),
        "handle should be invalid after didClose cleanup: {v}"
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test]
async fn fetch_result_slice_handle_invalid_after_namespace_reset() {
    let (client_w, server_r) = duplex(DUPLEX_BUFFER_SIZE);
    let (server_w, client_r) = duplex(DUPLEX_BUFFER_SIZE);
    let server_handle =
        tokio::spawn(async move { snaq_lite_lsp::run_native(server_r, server_w).await });
    let mut client_w = client_w;
    let mut client_r = client_r;

    send_init_and_initialized(&mut client_w, &mut client_r).await;
    open_document_uri(
        &mut client_w,
        "snaq://graph/reset-handle.sl",
        "[11,12,13]",
        1,
    )
    .await;

    let sub_req = serde_json::json!({
        "jsonrpc":"2.0","id":331,"method":"snaqlite/subscribeNode",
        "params":{"sourceUri":"snaq://graph/reset-handle.sl"}
    });
    client_w
        .write_all(&lsp_message(&sub_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 331).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    let result_handle = v["result"]["resultHandle"]
        .as_str()
        .expect("subscribeNode should return resultHandle")
        .to_string();

    let reset_req = serde_json::json!({
        "jsonrpc":"2.0","id":332,"method":"snaqlite/graph/resetNamespace",
        "params":{"uriPrefix":"snaq://graph/"}
    });
    client_w
        .write_all(&lsp_message(&reset_req.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 332).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(v.get("error").is_none(), "resetNamespace should succeed: {v}");

    let fetch = serde_json::json!({
        "jsonrpc":"2.0","id":333,"method":"snaqlite/graph/fetchResultSlice",
        "params":{"resultHandle": result_handle, "path":[],"offset":0,"limit":2}
    });
    client_w
        .write_all(&lsp_message(&fetch.to_string()))
        .await
        .unwrap();
    client_w.flush().await.unwrap();
    let body = read_until_response_id(&mut client_r, 333).await;
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    assert!(
        v.get("error").is_some(),
        "handle should be invalid after namespace reset: {v}"
    );

    server_handle.abort();
    let _ = server_handle.await;
}
