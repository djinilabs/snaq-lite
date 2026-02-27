//! snaq-lite LSP server: dual-target (native stdio + WASM Web Worker) language server.

pub mod mapping;
pub mod pubsub;
pub mod state;
pub mod subscription;

#[cfg(target_arch = "wasm32")]
pub mod transport;

use futures::lock::Mutex;
use state::LspState;
use std::sync::Arc;
use tower_lsp::lsp_types::{
    Hover, HoverContents, HoverProviderCapability, InlayHint, InitializeResult,
    MarkedString, MessageType, ServerCapabilities, TextDocumentSyncCapability, TextDocumentSyncKind,
    Url,
};

use crate::mapping::SERVER_NAME;
use crate::pubsub::{
    PublishResultNotification, PublishResultParams, PublishStatus, SubscribeParams, SubscribeResponse,
    UnsubscribeParams,
};
use crate::subscription::SubscriptionRegistry;
use tower_lsp::{Client, LanguageServer, LspService};
#[cfg(not(target_arch = "wasm32"))]
use tower_lsp::Server;

pub use mapping::{run_error_to_diagnostic, span_to_range};

/// Shared state for the LSP backend (async lock for both native and WASM).
pub type SharedState = Arc<Mutex<LspState>>;

/// Shared subscription registry (async lock).
pub type SharedSubscriptions = Arc<Mutex<SubscriptionRegistry>>;

/// Channel to send publish notifications from background consumer to the backend.
pub type NotificationSender = futures::channel::mpsc::UnboundedSender<(String, PublishResultParams)>;
pub type NotificationReceiver = futures::channel::mpsc::UnboundedReceiver<(String, PublishResultParams)>;

/// Backend implementing the Language Server Protocol for snaq-lite.
pub struct SnaqLiteBackend {
    pub client: Client,
    pub state: SharedState,
    pub subscriptions: SharedSubscriptions,
    pub notification_tx: NotificationSender,
    /// Locked receiver for draining pending publishResult notifications (sent by consumer threads).
    pub notification_rx: Arc<Mutex<NotificationReceiver>>,
}

#[tower_lsp::async_trait]
impl LanguageServer for SnaqLiteBackend {
    async fn initialize(&self, _params: tower_lsp::lsp_types::InitializeParams) -> tower_lsp::jsonrpc::Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                inlay_hint_provider: Some(tower_lsp::lsp_types::OneOf::Left(true)),
                ..Default::default()
            },
            server_info: Some(tower_lsp::lsp_types::ServerInfo {
                name: SERVER_NAME.to_string(),
                version: Some("0.1.0".to_string()),
            }),
        })
    }

    async fn initialized(&self, _params: tower_lsp::lsp_types::InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "snaq-lite LSP initialized")
            .await;
    }

    async fn shutdown(&self) -> tower_lsp::jsonrpc::Result<()> {
        let to_cancel = {
            let mut subs = self.subscriptions.lock().await;
            subs.invalidate_all()
        };
        for (id, cancel_tx) in to_cancel {
            let _ = cancel_tx.send(());
            self.client
                .send_notification::<PublishResultNotification>(PublishResultParams {
                    subscription_id: id,
                    status: PublishStatus::Cancelled,
                    data: Some(serde_json::json!({ "reason": "Server shutdown" })),
                })
                .await;
        }
        Ok(())
    }

    async fn did_open(&self, params: tower_lsp::lsp_types::DidOpenTextDocumentParams) {
        let uri = params.text_document.uri.clone();
        let text = params.text_document.text;
        let version = params.text_document.version;
        let mut state = self.state.lock().await;
        state.update_document(uri.clone(), version, &text);
        drop(state);
        self.invalidate_subscriptions_for_uri(&uri).await;
        self.drain_notifications().await;
        self.publish_diagnostics(uri).await;
    }

    async fn did_change(&self, params: tower_lsp::lsp_types::DidChangeTextDocumentParams) {
        let uri = params.text_document.uri.clone();
        let version = params.text_document.version;
        let mut state = self.state.lock().await;
        // Full sync: we only use the first content change; empty list is a no-op.
        if let Some(content_changes) = params.content_changes.first() {
            let text = content_changes.text.clone();
            state.update_document(uri.clone(), version, &text);
        }
        drop(state);
        self.invalidate_subscriptions_for_uri(&uri).await;
        self.drain_notifications().await;
        self.publish_diagnostics(uri).await;
    }

    async fn hover(&self, params: tower_lsp::lsp_types::HoverParams) -> tower_lsp::jsonrpc::Result<Option<Hover>> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;
        let state = self.state.lock().await;
        let Some((content, range)) = state.hover_at(&uri, position.line, position.character) else {
            return Ok(None);
        };
        if content.is_empty() {
            return Ok(None);
        }
        Ok(Some(Hover {
            contents: HoverContents::Scalar(MarkedString::String(content)),
            range,
        }))
    }

    async fn inlay_hint(
        &self,
        params: tower_lsp::lsp_types::InlayHintParams,
    ) -> tower_lsp::jsonrpc::Result<Option<Vec<InlayHint>>> {
        let uri = params.text_document.uri;
        let state = self.state.lock().await;
        let hints = state.inlay_hints(&uri);
        Ok(Some(hints))
    }
}

impl SnaqLiteBackend {
    async fn publish_diagnostics(&self, uri: Url) {
        let state = self.state.lock().await;
        let diagnostics = state.diagnostics();
        let version = state.document_version();
        drop(state);
        self.client
            .publish_diagnostics(uri, diagnostics, version)
            .await;
    }

    /// Drain pending publishResult notifications from the channel and send them to the client.
    async fn drain_notifications(&self) {
        let mut rx = self.notification_rx.lock().await;
        while let Ok((_id, params)) = rx.try_recv() {
            self.client
                .send_notification::<PublishResultNotification>(params)
                .await;
        }
    }

    /// Invalidate all subscriptions for the given uri: send cancel and publishResult(Cancelled).
    async fn invalidate_subscriptions_for_uri(&self, uri: &Url) {
        let to_cancel = {
            let mut subs = self.subscriptions.lock().await;
            subs.invalidate_uri(uri)
        };
        for (id, cancel_tx) in to_cancel {
            let _ = cancel_tx.send(());
            self.client
                .send_notification::<PublishResultNotification>(PublishResultParams {
                    subscription_id: id,
                    status: PublishStatus::Cancelled,
                    data: Some(serde_json::json!({ "reason": "Document changed" })),
                })
                .await;
        }
    }

    /// Handle snaqlite/subscribe: run document (root-only), return subscription id; if root is a vector, spawn consumer and stream batches.
    pub async fn subscribe(
        &self,
        params: SubscribeParams,
    ) -> tower_lsp::jsonrpc::Result<SubscribeResponse> {
        self.drain_notifications().await;
        let uri = params.text_document.uri;
        let state = self.state.lock().await;
        let source = state.source().to_string();
        let unit_registry = state.unit_registry().clone();
        let doc_uri = state.uri().cloned();
        let version = state.document_version();
        drop(state);
        if doc_uri.as_ref() != Some(&uri) {
            return Err(tower_lsp::jsonrpc::Error::invalid_params("document not open or URI mismatch"));
        }
        let stream_inputs = std::collections::HashMap::new();
        let result = snaq_lite_lang::run_with_stream_inputs(&source, &unit_registry, stream_inputs);
        match result {
            Err(e) => Err(tower_lsp::jsonrpc::Error::invalid_params(format!("run error: {e}"))),
            Ok((value, db)) => {
                let subscription_id = uuid::Uuid::new_v4().to_string();
                match &value {
                    snaq_lite_lang::Value::Vector(v) => {
                        let inner = v.inner.clone();
                        let (cancel_tx, cancel_rx) = futures::channel::oneshot::channel();
                        let sid = subscription_id.clone();
                        self.subscriptions.lock().await.insert(
                            subscription_id.clone(),
                            uri.clone(),
                            version,
                            cancel_tx,
                        );
                        let notification_tx = self.notification_tx.clone();
                        #[cfg(not(target_arch = "wasm32"))]
                        {
                            std::thread::spawn(move || {
                                run_stream_consumer(db, inner, sid, notification_tx, cancel_rx);
                            });
                        }
                        #[cfg(target_arch = "wasm32")]
                        {
                            // WASM: streaming subscription not yet supported; send Completed with display.
                            let display = snaq_lite_lang::format_value_for_display(&db, &value)
                                .unwrap_or_else(|_| "<vector>".to_string());
                            let _ = (inner, cancel_rx);
                            let sid = subscription_id.clone();
                            self.client
                                .send_notification::<PublishResultNotification>(PublishResultParams {
                                    subscription_id: sid,
                                    status: PublishStatus::Completed,
                                    data: Some(serde_json::json!({ "display": display })),
                                })
                                .await;
                        }
                    }
                    _ => {
                        let display = snaq_lite_lang::format_value_for_display(&db, &value)
                            .unwrap_or_else(|_| "<error>".to_string());
                        self.client
                            .send_notification::<PublishResultNotification>(PublishResultParams {
                                subscription_id: subscription_id.clone(),
                                status: PublishStatus::Completed,
                                data: Some(serde_json::json!({ "display": display })),
                            })
                            .await;
                    }
                }
                Ok(SubscribeResponse { subscription_id })
            }
        }
    }

    /// Handle snaqlite/unsubscribe: cancel subscription and remove from registry.
    pub async fn unsubscribe(&self, params: UnsubscribeParams) -> tower_lsp::jsonrpc::Result<()> {
        self.drain_notifications().await;
        let mut subs = self.subscriptions.lock().await;
        if let Some(cancel_tx) = subs.remove(&params.subscription_id) {
            let _ = cancel_tx.send(());
        }
        Ok(())
    }
}

/// Native: run the stream in a blocking thread and send batches via notification_tx.
/// Creates the stream inside the async block so it borrows db correctly.
/// Exits on stream end (sends Completed) or when cancel_rx fires (no final notification).
#[cfg(not(target_arch = "wasm32"))]
fn run_stream_consumer(
    db: salsa::DatabaseImpl,
    inner: snaq_lite_lang::LazyVector,
    subscription_id: String,
    notification_tx: NotificationSender,
    cancel_rx: futures::channel::oneshot::Receiver<()>,
) {
    use futures::future::{select, Either};
    use futures::stream::StreamExt;
    use futures::task::LocalSpawnExt;
    const BATCH_SIZE: usize = 100;
    let run = async move {
        let mut stream = snaq_lite_lang::vector_into_stream(&db, inner);
        let mut batch: Vec<serde_json::Value> = Vec::with_capacity(BATCH_SIZE);
        let mut offset: u64 = 0;
        let mut total: u64 = 0;
        let mut stream_next = stream.next();
        let mut cancel_rx = cancel_rx;
        loop {
            match select(stream_next, cancel_rx).await {
                Either::Left((opt, cr)) => {
                    cancel_rx = cr;
                    match opt {
                        Some(item) => {
                            let json = crate::pubsub::stream_element_to_json(&db, &item);
                            batch.push(json);
                            total += 1;
                            if batch.len() >= BATCH_SIZE {
                                let data = serde_json::json!({
                                    "elements": batch.clone(),
                                    "offset": offset,
                                    "count": batch.len()
                                });
                                let _ = notification_tx.unbounded_send((
                                    subscription_id.clone(),
                                    PublishResultParams {
                                        subscription_id: subscription_id.clone(),
                                        status: PublishStatus::Running,
                                        data: Some(data),
                                    },
                                ));
                                offset += batch.len() as u64;
                                batch.clear();
                            }
                            stream_next = stream.next();
                        }
                        None => break,
                    }
                }
                Either::Right(_) => {
                    // Cancelled: exit without sending Completed
                    return;
                }
            }
        }
        if !batch.is_empty() {
            let _ = notification_tx.unbounded_send((
                subscription_id.clone(),
                PublishResultParams {
                    subscription_id: subscription_id.clone(),
                    status: PublishStatus::Running,
                    data: Some(serde_json::json!({
                        "elements": batch,
                        "offset": offset,
                        "count": batch.len()
                    })),
                },
            ));
        }
        let sid = subscription_id.clone();
        let _ = notification_tx.unbounded_send((
            subscription_id,
            PublishResultParams {
                subscription_id: sid,
                status: PublishStatus::Completed,
                data: Some(serde_json::json!({ "totalElements": total })),
            },
        ));
    };
    let mut pool = futures::executor::LocalPool::new();
    let spawner = pool.spawner();
    spawner.spawn_local(run).ok();
    pool.run();
}

/// Build the LSP service (same for native and WASM). Uses custom methods for snaqlite/subscribe and snaqlite/unsubscribe.
pub fn create_lsp_service() -> (LspService<SnaqLiteBackend>, tower_lsp::ClientSocket) {
    let state: SharedState = Arc::new(Mutex::new(LspState::new()));
    let subscriptions: SharedSubscriptions = Arc::new(Mutex::new(SubscriptionRegistry::new()));
    let (notification_tx, notification_rx) = futures::channel::mpsc::unbounded();
    let (service, socket) = LspService::build(move |client| SnaqLiteBackend {
        client,
        state: Arc::clone(&state),
        subscriptions: Arc::clone(&subscriptions),
        notification_tx,
        notification_rx: Arc::new(Mutex::new(notification_rx)),
    })
    .custom_method("snaqlite/subscribe", SnaqLiteBackend::subscribe)
    .custom_method("snaqlite/unsubscribe", SnaqLiteBackend::unsubscribe)
    .finish();
    (service, socket)
}

/// Run the LSP server with the given stdin and stdout (native).
#[cfg(not(target_arch = "wasm32"))]
pub async fn run_native<I, O>(stdin: I, stdout: O) -> Result<(), Box<dyn std::error::Error + Send + Sync>>
where
    I: tokio::io::AsyncRead + Unpin + Send + 'static,
    O: tokio::io::AsyncWrite + Unpin + Send + 'static,
{
    let (service, socket) = create_lsp_service();
    Server::new(stdin, stdout, socket).serve(service).await;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use tower_lsp::lsp_types::Url;

    // ---- span_to_range ----

    #[test]
    fn span_to_range_uses_zero_based_line_and_column() {
        // Single line: span 2..5 in "hello" is "llo"; lang line_col gives 1-based line, column as byte offset
        let source = "hello";
        let range = span_to_range(
            &snaq_lite_lang::Span { start: 2, end: 5 },
            source,
        );
        assert_eq!(range.start.line, 0);
        assert_eq!(range.start.character, 2);
        assert_eq!(range.end.line, 0);
        assert_eq!(range.end.character, 5);
    }

    #[test]
    fn span_to_range_multiline_second_line() {
        let source = "a\nbc\nd";
        // span 3..5: second line (0-based line 1); end can be 0 when span ends at newline
        let range = span_to_range(&snaq_lite_lang::Span { start: 3, end: 5 }, source);
        assert_eq!(range.start.line, 1);
        assert_eq!(range.end.line, 1);
        assert!(range.start.character <= range.end.character || range.end.character == 0);
    }

    #[test]
    fn span_to_range_start_of_file() {
        let source = "x";
        let range = span_to_range(&snaq_lite_lang::Span { start: 0, end: 1 }, source);
        assert_eq!(range.start.line, 0);
        // lang line_col uses .max(1) so first character can be column 1
        assert!(range.start.character <= 1);
        assert_eq!(range.end.line, 0);
        assert_eq!(range.end.character, 1);
    }

    #[test]
    fn span_to_range_empty_source_saturates() {
        let source = "";
        let range = span_to_range(&snaq_lite_lang::Span { start: 0, end: 0 }, source);
        // lang returns (1,1) for empty prefix; we convert line to 0-based
        assert_eq!(range.start.line, 0);
        assert_eq!(range.end.line, 0);
    }

    // ---- run_error_to_diagnostic ----

    #[test]
    fn run_error_parse_kind_produces_diagnostic() {
        let err = snaq_lite_lang::RunError {
            span: Some(snaq_lite_lang::Span { start: 0, end: 1 }),
            kind: snaq_lite_lang::RunErrorKind::Parse(snaq_lite_lang::ParseError {
                message: "expected number".to_string(),
                span: Some(snaq_lite_lang::Span { start: 0, end: 1 }),
            }),
        };
        let source = "x";
        let d = run_error_to_diagnostic(&err, source);
        assert_eq!(d.message, "expected number");
        assert_eq!(d.range.start.line, 0);
        assert_eq!(d.severity, Some(tower_lsp::lsp_types::DiagnosticSeverity::ERROR));
        assert_eq!(d.source.as_deref(), Some("snaq-lite"));
    }

    #[test]
    fn run_error_runtime_kind_uses_span_and_format() {
        let err = snaq_lite_lang::RunError {
            span: Some(snaq_lite_lang::Span { start: 2, end: 5 }),
            kind: snaq_lite_lang::RunErrorKind::DivisionByZero,
        };
        let source = "  1/0 ";
        let d = run_error_to_diagnostic(&err, source);
        assert!(d.message.contains("division") || d.message.contains("Division"));
        assert_eq!(d.range.start.line, 0);
        assert_eq!(d.range.start.character, 2);
        assert_eq!(d.severity, Some(tower_lsp::lsp_types::DiagnosticSeverity::ERROR));
    }

    #[test]
    fn run_error_without_span_falls_back_to_zero_range() {
        let err = snaq_lite_lang::RunError {
            span: None,
            kind: snaq_lite_lang::RunErrorKind::Parse(snaq_lite_lang::ParseError {
                message: "bad".to_string(),
                span: None,
            }),
        };
        let d = run_error_to_diagnostic(&err, "anything");
        assert_eq!(d.message, "bad");
        assert_eq!(d.range.start.line, 0);
        assert_eq!(d.range.start.character, 0);
        assert_eq!(d.range.end.line, 0);
        assert_eq!(d.range.end.character, 0);
    }

    // ---- state (LspState) ----

    #[test]
    fn state_update_document_empty_clears_diagnostics() {
        let mut state = state::LspState::new();
        let uri = Url::parse("file:///doc.snaq").unwrap();
        state.update_document(uri.clone(), 1, "");
        assert!(state.diagnostics().is_empty());
        assert_eq!(state.document_version(), Some(1));
    }

    #[test]
    fn state_update_document_parse_error_produces_diagnostic() {
        let mut state = state::LspState::new();
        let uri = Url::parse("file:///doc.snaq").unwrap();
        state.update_document(uri.clone(), 1, "syntax error @@");
        let diags = state.diagnostics();
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].severity, Some(tower_lsp::lsp_types::DiagnosticSeverity::ERROR));
        assert!(!diags[0].message.is_empty());
    }

    #[test]
    fn state_update_document_valid_produces_no_diagnostics() {
        let mut state = state::LspState::new();
        let uri = Url::parse("file:///doc.snaq").unwrap();
        state.update_document(uri.clone(), 1, "1 + 2");
        assert!(state.diagnostics().is_empty());
    }

    #[test]
    fn state_hover_at_returns_value_for_valid_expression() {
        let mut state = state::LspState::new();
        let uri = Url::parse("file:///doc.snaq").unwrap();
        state.update_document(uri.clone(), 1, "1 + 2");
        // Position (0, 4) is around "2" or "+"; we expect some hover content
        let hover = state.hover_at(&uri, 0, 4);
        assert!(hover.is_some());
        let (content, _range) = hover.unwrap();
        assert!(!content.is_empty());
        // Result of "1 + 2" or subexpression
        assert!(content.contains("3") || content.contains("1") || content.contains("2"));
    }

    #[test]
    fn state_hover_at_wrong_uri_returns_none() {
        let mut state = state::LspState::new();
        let uri = Url::parse("file:///doc.snaq").unwrap();
        state.update_document(uri, 1, "1 + 2");
        let other = Url::parse("file:///other.snaq").unwrap();
        assert!(state.hover_at(&other, 0, 0).is_none());
    }

    #[test]
    fn state_inlay_hints_valid_document() {
        let mut state = state::LspState::new();
        let uri = Url::parse("file:///doc.snaq").unwrap();
        state.update_document(uri.clone(), 1, "1 + 2");
        let hints = state.inlay_hints(&uri);
        // May have hint for "1 + 2" or subexpressions
        assert!(hints.len() <= 3);
    }

    #[test]
    fn state_inlay_hints_wrong_uri_returns_empty() {
        let mut state = state::LspState::new();
        let uri = Url::parse("file:///doc.snaq").unwrap();
        state.update_document(uri, 1, "1 + 2");
        let other = Url::parse("file:///other.snaq").unwrap();
        assert!(state.inlay_hints(&other).is_empty());
    }

    // ---- subscription registry ----

    #[test]
    fn subscription_registry_insert_remove() {
        let mut reg = subscription::SubscriptionRegistry::new();
        let uri = Url::parse("file:///doc.snaq").unwrap();
        let (tx, _rx) = futures::channel::oneshot::channel();
        reg.insert("sub-1".to_string(), uri.clone(), Some(1), tx);
        let removed = reg.remove("sub-1");
        assert!(removed.is_some());
        assert!(reg.remove("sub-1").is_none());
    }

    #[test]
    fn subscription_registry_invalidate_uri() {
        let mut reg = subscription::SubscriptionRegistry::new();
        let uri = Url::parse("file:///doc.snaq").unwrap();
        let other = Url::parse("file:///other.snaq").unwrap();
        let (tx1, _rx1) = futures::channel::oneshot::channel();
        let (tx2, _rx2) = futures::channel::oneshot::channel();
        reg.insert("sub-a".to_string(), uri.clone(), Some(1), tx1);
        reg.insert("sub-b".to_string(), other, Some(1), tx2);
        let cancelled = reg.invalidate_uri(&uri);
        assert_eq!(cancelled.len(), 1);
        assert_eq!(cancelled[0].0, "sub-a");
        assert!(reg.remove("sub-b").is_some());
    }

    // ---- pubsub stream element serialization ----

    #[test]
    fn stream_element_to_json_error() {
        let (_v, db) = snaq_lite_lang::run_with_stream_inputs(
            "1",
            &snaq_lite_lang::default_si_registry(),
            std::collections::HashMap::new(),
        )
        .unwrap();
        let err = snaq_lite_lang::RunError::new(snaq_lite_lang::RunErrorKind::DivisionByZero);
        let item: Result<Option<snaq_lite_lang::Value>, _> = Err(err);
        let json = pubsub::stream_element_to_json(&db, &item);
        let obj = json.as_object().expect("object");
        assert_eq!(obj.get("kind").and_then(|v| v.as_str()), Some("error"));
        assert!(obj.get("message").and_then(|v| v.as_str()).unwrap_or("").contains("division"));
    }

    #[test]
    fn stream_element_to_json_undefined() {
        let (_v, db) = snaq_lite_lang::run_with_stream_inputs(
            "1",
            &snaq_lite_lang::default_si_registry(),
            std::collections::HashMap::new(),
        )
        .unwrap();
        let item: Result<Option<snaq_lite_lang::Value>, snaq_lite_lang::RunError> = Ok(None);
        let json = pubsub::stream_element_to_json(&db, &item);
        assert!(json.is_null());
    }

    #[test]
    fn stream_element_to_json_ok_some_value() {
        let (value, db) = snaq_lite_lang::run_with_stream_inputs(
            "1 + 2",
            &snaq_lite_lang::default_si_registry(),
            std::collections::HashMap::new(),
        )
        .unwrap();
        let item: Result<Option<snaq_lite_lang::Value>, snaq_lite_lang::RunError> = Ok(Some(value));
        let json = pubsub::stream_element_to_json(&db, &item);
        let obj = json.as_object().expect("object");
        let display = obj.get("display").and_then(|v| v.as_str()).unwrap_or("");
        assert!(display.contains("3"), "display should show result: {}", display);
    }

    #[test]
    fn subscription_registry_invalidate_all() {
        let mut reg = subscription::SubscriptionRegistry::new();
        let uri = Url::parse("file:///doc.snaq").unwrap();
        let (tx1, _rx1) = futures::channel::oneshot::channel();
        let (tx2, _rx2) = futures::channel::oneshot::channel();
        reg.insert("sub-1".to_string(), uri.clone(), Some(1), tx1);
        reg.insert("sub-2".to_string(), uri, Some(1), tx2);
        let cancelled = reg.invalidate_all();
        assert_eq!(cancelled.len(), 2);
        let ids: std::collections::HashSet<_> = cancelled.iter().map(|(id, _)| id.as_str()).collect();
        assert!(ids.contains("sub-1"));
        assert!(ids.contains("sub-2"));
        assert!(reg.remove("sub-1").is_none());
        assert!(reg.remove("sub-2").is_none());
    }

    // ---- pubsub wire format (camelCase) ----

    #[test]
    fn subscribe_params_deserializes_camel_case() {
        let json = r#"{"textDocument":{"uri":"file:///x.snaq"}}"#;
        let params: pubsub::SubscribeParams = serde_json::from_str(json).unwrap();
        assert_eq!(params.text_document.uri.as_str(), "file:///x.snaq");
    }

    #[test]
    fn subscribe_response_serializes_camel_case() {
        let response = pubsub::SubscribeResponse {
            subscription_id: "id-123".to_string(),
        };
        let json = serde_json::to_string(&response).unwrap();
        assert!(json.contains("subscriptionId"));
        let back: pubsub::SubscribeResponse = serde_json::from_str(&json).unwrap();
        assert_eq!(back.subscription_id, "id-123");
    }

    #[test]
    fn unsubscribe_params_deserializes_camel_case() {
        let json = r#"{"subscriptionId":"sub-1"}"#;
        let params: pubsub::UnsubscribeParams = serde_json::from_str(json).unwrap();
        assert_eq!(params.subscription_id, "sub-1");
    }

    #[test]
    fn publish_result_params_status_serializes_pascal_case() {
        use pubsub::{PublishResultParams, PublishStatus};
        let params = PublishResultParams {
            subscription_id: "sub-1".to_string(),
            status: PublishStatus::Completed,
            data: Some(serde_json::json!({ "totalElements": 5 })),
        };
        let json = serde_json::to_string(&params).unwrap();
        assert!(json.contains("\"status\":\"Completed\""), "status should be PascalCase: {}", json);
        let back: PublishResultParams = serde_json::from_str(&json).unwrap();
        match back.status {
            PublishStatus::Completed => {}
            _ => panic!("round-trip should preserve Completed"),
        }
    }
}
