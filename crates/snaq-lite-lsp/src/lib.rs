//! snaq-lite LSP server: dual-target (native stdio + WASM Web Worker) language server.

pub mod graph;
pub mod mapping;
pub mod widget_registry;
pub mod pubsub;
pub mod state;
pub mod subscription;

#[cfg(target_arch = "wasm32")]
pub mod stream_host;
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
    ConnectParams, DisconnectParams, NodeInputPort, NodeSignatureUpdatedNotification,
    NodeSignatureUpdatedParams, PublishResultNotification, PublishResultParams, PublishStatus,
    SubscribeParams, SubscribeResponse, UnsubscribeParams, SubscribeWidgetParams,
    UnsubscribeWidgetParams, WidgetDataStatus, WidgetDataUpdateNotification, WidgetDataUpdateParams,
};
use crate::subscription::SubscriptionRegistry;
use crate::widget_registry::WidgetRegistry;
use tower_lsp::{Client, LanguageServer, LspService};
#[cfg(not(target_arch = "wasm32"))]
use tower_lsp::Server;

pub use mapping::{run_error_to_diagnostic, span_to_range};

/// Shared state for the LSP backend (async lock for both native and WASM).
pub type SharedState = Arc<Mutex<LspState>>;

/// Shared subscription registry (async lock).
pub type SharedSubscriptions = Arc<Mutex<SubscriptionRegistry>>;

/// Shared graph state (edges for connect).
pub type SharedGraphState = Arc<Mutex<graph::GraphState>>;

/// Shared widget registry (subscribeWidget / unsubscribeWidget).
pub type SharedWidgetRegistry = Arc<Mutex<WidgetRegistry>>;

/// Channel to send publish notifications from background consumer to the backend.
pub type NotificationSender = futures::channel::mpsc::UnboundedSender<(String, PublishResultParams)>;
pub type NotificationReceiver = futures::channel::mpsc::UnboundedReceiver<(String, PublishResultParams)>;

/// Channel to send widget data updates from background consumer to the backend.
pub type WidgetNotificationSender = futures::channel::mpsc::UnboundedSender<WidgetDataUpdateParams>;
pub type WidgetNotificationReceiver = futures::channel::mpsc::UnboundedReceiver<WidgetDataUpdateParams>;

/// Backend implementing the Language Server Protocol for snaq-lite.
pub struct SnaqLiteBackend {
    pub client: Client,
    pub state: SharedState,
    pub subscriptions: SharedSubscriptions,
    pub graph_state: SharedGraphState,
    pub widgets: SharedWidgetRegistry,
    pub notification_tx: NotificationSender,
    /// Locked receiver for draining pending publishResult notifications (sent by consumer threads).
    pub notification_rx: Arc<Mutex<NotificationReceiver>>,
    pub widget_notification_tx: WidgetNotificationSender,
    pub widget_notification_rx: Arc<Mutex<WidgetNotificationReceiver>>,
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
        let widget_cancel = {
            let mut w = self.widgets.lock().await;
            w.invalidate_all()
        };
        for (widget_id, cancel_tx) in widget_cancel {
            let _ = cancel_tx.send(());
            self.client
                .send_notification::<WidgetDataUpdateNotification>(WidgetDataUpdateParams {
                    widget_id,
                    status: WidgetDataStatus::Cancelled,
                    payload: Some(serde_json::json!({ "reason": "Server shutdown" })),
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
        self.invalidate_widgets_for_uri(&uri).await;
        self.refresh_downstream_widgets(&uri).await;
        self.drain_notifications().await;
        self.drain_widget_notifications().await;
        self.publish_diagnostics(uri.clone()).await;
        self.send_node_signature_updated(&uri).await;
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
        self.invalidate_widgets_for_uri(&uri).await;
        self.refresh_downstream_widgets(&uri).await;
        self.drain_notifications().await;
        self.drain_widget_notifications().await;
        self.publish_diagnostics(uri.clone()).await;
        self.send_node_signature_updated(&uri).await;
    }

    async fn hover(&self, params: tower_lsp::lsp_types::HoverParams) -> tower_lsp::jsonrpc::Result<Option<Hover>> {
        self.drain_widget_notifications().await;
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
        self.drain_widget_notifications().await;
        let uri = params.text_document.uri;
        let state = self.state.lock().await;
        let hints = state.inlay_hints(&uri);
        Ok(Some(hints))
    }
}

impl SnaqLiteBackend {
    async fn publish_diagnostics(&self, uri: Url) {
        let state = self.state.lock().await;
        let diagnostics = state.diagnostics(&uri);
        let version = state.document_version(&uri);
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

    /// Drain pending widgetDataUpdate notifications and send them to the client.
    async fn drain_widget_notifications(&self) {
        let mut rx = self.widget_notification_rx.lock().await;
        while let Ok(params) = rx.try_recv() {
            self.client
                .send_notification::<WidgetDataUpdateNotification>(params)
                .await;
        }
    }

    /// Invalidate all widget subscriptions for the given uri: send cancel and widgetDataUpdate(Cancelled).
    async fn invalidate_widgets_for_uri(&self, uri: &Url) {
        let to_cancel = {
            let mut w = self.widgets.lock().await;
            w.invalidate_uri(uri)
        };
        for (widget_id, cancel_tx) in to_cancel {
            let _ = cancel_tx.send(());
            self.client
                .send_notification::<WidgetDataUpdateNotification>(WidgetDataUpdateParams {
                    widget_id,
                    status: WidgetDataStatus::Cancelled,
                    payload: Some(serde_json::json!({ "reason": "Document changed" })),
                })
                .await;
        }
    }

    /// Refresh all widgets subscribed to this URI: re-run the node with current graph and push result.
    /// Used when an edge is added (graph/connect) so a presentation that already subscribed gets the bound stream.
    /// On WASM the client receives the updated value immediately. On native, scalar-fed streams are consumed
    /// in a background thread (receiver is thread-local), so this path is most reliable in the browser.
    async fn refresh_widgets_for_uri(&self, uri: &Url) {
        let entries = {
            let mut w = self.widgets.lock().await;
            w.take_entries_for_uri(uri)
        };
        for (widget_id, cancel_tx) in entries {
            if let Some(tx) = cancel_tx {
                let _ = tx.send(());
            }
            match self.run_node_with_graph_inputs(uri, None).await {
                Err(e) => {
                    self.client
                        .send_notification::<WidgetDataUpdateNotification>(WidgetDataUpdateParams {
                            widget_id: widget_id.clone(),
                            status: WidgetDataStatus::Error,
                            payload: Some(serde_json::json!({ "message": e.to_string() })),
                        })
                        .await;
                    self.widgets
                        .lock()
                        .await
                        .insert_scalar(widget_id, uri.clone());
                }
                Ok((value, db)) => {
                    match &value {
                        snaq_lite_lang::Value::Vector(v) => {
                            let inner = v.inner.clone();
                            let (cancel_tx, cancel_rx) = futures::channel::oneshot::channel();
                            self.widgets.lock().await.insert(
                                widget_id.clone(),
                                uri.clone(),
                                cancel_tx,
                            );
                            #[cfg(not(target_arch = "wasm32"))]
                            {
                                let widget_tx = self.widget_notification_tx.clone();
                                std::thread::spawn(move || {
                                    run_stream_consumer_for_widget(db, inner, widget_id, widget_tx, cancel_rx);
                                });
                            }
                            #[cfg(target_arch = "wasm32")]
                            {
                                let display = snaq_lite_lang::format_vector_for_widget_display(&db, v)
                                    .unwrap_or_else(|_| "<vector>".to_string());
                                let _ = (inner, cancel_rx);
                                self.client
                                    .send_notification::<WidgetDataUpdateNotification>(WidgetDataUpdateParams {
                                        widget_id: widget_id.clone(),
                                        status: WidgetDataStatus::Completed,
                                        payload: Some(serde_json::json!({ "display": display })),
                                    })
                                    .await;
                                self.widgets
                                    .lock()
                                    .await
                                    .insert_scalar(widget_id, uri.clone());
                            }
                        }
                        _ => {
                            let display = snaq_lite_lang::format_value_for_display(&db, &value)
                                .unwrap_or_else(|_| "<error>".to_string());
                            self.client
                                .send_notification::<WidgetDataUpdateNotification>(WidgetDataUpdateParams {
                                    widget_id: widget_id.clone(),
                                    status: WidgetDataStatus::Completed,
                                    payload: Some(serde_json::json!({ "display": display })),
                                })
                                .await;
                            self.widgets
                                .lock()
                                .await
                                .insert_scalar(widget_id, uri.clone());
                        }
                    }
                }
            }
        }
    }

    /// Refresh downstream widgets: re-run each target document and push new result to subscribed widgets.
    /// No Cancelled is sent; the client keeps the same subscription and receives the updated result.
    async fn refresh_downstream_widgets(&self, source_uri: &Url) {
        let downstream: Vec<Url> = {
            let graph = self.graph_state.lock().await;
            graph.targets_from_source(source_uri)
        };
        for target_uri in downstream {
            self.refresh_widgets_for_uri(&target_uri).await;
        }
    }

    /// Send snaqlite/graph/nodeSignatureUpdated for the given URI so the frontend can render ports.
    async fn send_node_signature_updated(&self, uri: &Url) {
        let (_source, root_def, _unit_registry) = {
            let state = self.state.lock().await;
            let doc = match state.get_document(uri) {
                Some(d) => d,
                None => return,
            };
            (
                doc.source.clone(),
                doc.root_def.clone(),
                state.unit_registry().clone(),
            )
        };
        let inputs: Vec<NodeInputPort> = root_def
            .as_ref()
            .map(|root| {
                snaq_lite_lang::extract_input_decls_from_block(root)
                    .into_iter()
                    .map(|(name, type_name)| NodeInputPort {
                        name,
                        r#type: type_name,
                    })
                    .collect()
            })
            .unwrap_or_default();
        let output_type = self
            .run_node_with_graph_inputs(uri, None)
            .await
            .ok()
            .and_then(|(value, _)| snaq_lite_lang::value_type_name(&value));
        let params = NodeSignatureUpdatedParams {
            uri: uri.to_string(),
            inputs,
            output_type,
        };
        self.client
            .send_notification::<NodeSignatureUpdatedNotification>(params)
            .await;
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
        if !state.has_document(&uri) {
            drop(state);
            return Err(tower_lsp::jsonrpc::Error::invalid_params("document not open or URI mismatch"));
        }
        let source = state.source(&uri);
        let unit_registry = state.unit_registry().clone();
        let version = state.document_version(&uri);
        drop(state);
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
                        self.subscriptions.lock().await.insert(
                            subscription_id.clone(),
                            uri.clone(),
                            version,
                            cancel_tx,
                        );
                        #[cfg(not(target_arch = "wasm32"))]
                        {
                            let sid = subscription_id.clone();
                            let notification_tx = self.notification_tx.clone();
                            std::thread::spawn(move || {
                                run_stream_consumer(db, inner, sid, notification_tx, cancel_rx);
                            });
                        }
                        #[cfg(target_arch = "wasm32")]
                        {
                            // WASM: streaming subscription not yet supported; send Completed with display.
                            let display = snaq_lite_lang::format_vector_for_widget_display(&db, v)
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

    /// Handle snaqlite/graph/connect: type-check and add edge.
    pub async fn graph_connect(
        &self,
        params: ConnectParams,
    ) -> tower_lsp::jsonrpc::Result<()> {
        let source_uri = Url::parse(&params.source_uri)
            .map_err(|_| tower_lsp::jsonrpc::Error::invalid_params("invalid sourceUri"))?;
        let target_uri = Url::parse(&params.target_uri)
            .map_err(|_| tower_lsp::jsonrpc::Error::invalid_params("invalid targetUri"))?;
        let (source_source, target_input_type, unit_registry) = {
            let state = self.state.lock().await;
            let source_doc = state
                .get_document(&source_uri)
                .ok_or_else(|| tower_lsp::jsonrpc::Error::invalid_params("source document not open"))?;
            let target_doc = state
                .get_document(&target_uri)
                .ok_or_else(|| tower_lsp::jsonrpc::Error::invalid_params("target document not open"))?;
            let target_input_type = target_doc
                .root_def
                .as_ref()
                .map(snaq_lite_lang::extract_input_decls_from_block)
                .unwrap_or_default()
                .into_iter()
                .find(|(name, _)| name == &params.target_input_name)
                .map(|(_, t)| t);
            let target_input_type = target_input_type
                .ok_or_else(|| tower_lsp::jsonrpc::Error::invalid_params(format!("target has no input named '{}'", params.target_input_name)))?;
            (
                source_doc.source.clone(),
                target_input_type,
                state.unit_registry().clone(),
            )
        };
        let source_output_type = snaq_lite_lang::run_with_stream_inputs(
            &source_source,
            &unit_registry,
            std::collections::HashMap::new(),
        )
        .ok()
        .and_then(|(value, _)| snaq_lite_lang::value_type_name(&value))
        .unwrap_or_else(|| "Unknown".to_string());
        // Target input type "Undefined" means accept any (e.g. presentation boxes).
        if target_input_type != "Undefined" && source_output_type != target_input_type {
            return Err(tower_lsp::jsonrpc::Error {
                code: tower_lsp::jsonrpc::ErrorCode::ServerError(-32001),
                message: format!(
                    "Type mismatch: source output type '{}' does not match target input '{}' type '{}'",
                    source_output_type, params.target_input_name, target_input_type
                )
                .into(),
                data: None,
            });
        }
        {
            let mut graph = self.graph_state.lock().await;
            graph.connect(source_uri, target_uri.clone(), params.target_input_name);
        }
        self.refresh_widgets_for_uri(&target_uri).await;
        self.drain_widget_notifications().await;
        Ok(())
    }

    /// Handle snaqlite/graph/disconnect: remove edge and invalidate widgets for the target node.
    pub async fn graph_disconnect(
        &self,
        params: DisconnectParams,
    ) -> tower_lsp::jsonrpc::Result<()> {
        let target_uri = Url::parse(&params.target_uri)
            .map_err(|_| tower_lsp::jsonrpc::Error::invalid_params("invalid targetUri"))?;
        {
            let mut graph = self.graph_state.lock().await;
            graph.disconnect(&target_uri, &params.target_input_name);
        }
        self.invalidate_widgets_for_uri(&target_uri).await;
        self.drain_widget_notifications().await;
        Ok(())
    }

    /// Handle snaqlite/graph/subscribeWidget: run source node (with graph inputs when wired), stream or one-shot to widget.
    pub async fn subscribe_widget(
        &self,
        params: SubscribeWidgetParams,
    ) -> tower_lsp::jsonrpc::Result<()> {
        self.drain_notifications().await;
        self.drain_widget_notifications().await;
        let source_uri = Url::parse(&params.source_uri)
            .map_err(|_| tower_lsp::jsonrpc::Error::invalid_params("invalid sourceUri"))?;
        {
            let state = self.state.lock().await;
            if !state.has_document(&source_uri) {
                return Err(tower_lsp::jsonrpc::Error::invalid_params("source document not open"));
            }
        }
        let external_streams = resolve_external_streams(params.external_streams.as_ref());
        let result = self
            .run_node_with_graph_inputs(&source_uri, external_streams)
            .await;
        match result {
            Err(e) => {
                self.client
                    .send_notification::<WidgetDataUpdateNotification>(WidgetDataUpdateParams {
                        widget_id: params.widget_id.clone(),
                        status: WidgetDataStatus::Error,
                        payload: Some(serde_json::json!({ "message": e.to_string() })),
                    })
                    .await;
                self.widgets
                    .lock()
                    .await
                    .insert_scalar(params.widget_id.clone(), source_uri.clone());
                Ok(())
            }
            Ok((value, db)) => {
                match &value {
                    snaq_lite_lang::Value::Vector(v) => {
                        let inner = v.inner.clone();
                        let (cancel_tx, cancel_rx) = futures::channel::oneshot::channel();
                        self.widgets.lock().await.insert(
                            params.widget_id.clone(),
                            source_uri.clone(),
                            cancel_tx,
                        );
                        #[cfg(not(target_arch = "wasm32"))]
                        {
                            let widget_id = params.widget_id.clone();
                            let widget_tx = self.widget_notification_tx.clone();
                            std::thread::spawn(move || {
                                run_stream_consumer_for_widget(db, inner, widget_id, widget_tx, cancel_rx);
                            });
                        }
                        #[cfg(target_arch = "wasm32")]
                        {
                            let display = snaq_lite_lang::format_vector_for_widget_display(&db, v)
                                .unwrap_or_else(|_| "<vector>".to_string());
                            let _ = (inner, cancel_rx);
                            self.widgets
                                .lock()
                                .await
                                .insert_scalar(params.widget_id.clone(), source_uri.clone());
                            self.client
                                .send_notification::<WidgetDataUpdateNotification>(WidgetDataUpdateParams {
                                    widget_id: params.widget_id,
                                    status: WidgetDataStatus::Completed,
                                    payload: Some(serde_json::json!({ "display": display })),
                                })
                                .await;
                        }
                    }
                    _ => {
                        let display = snaq_lite_lang::format_value_for_display(&db, &value)
                            .unwrap_or_else(|_| "<error>".to_string());
                        self.widgets
                            .lock()
                            .await
                            .insert_scalar(params.widget_id.clone(), source_uri.clone());
                        self.client
                            .send_notification::<WidgetDataUpdateNotification>(WidgetDataUpdateParams {
                                widget_id: params.widget_id,
                                status: WidgetDataStatus::Completed,
                                payload: Some(serde_json::json!({ "display": display })),
                            })
                            .await;
                    }
                }
                Ok(())
            }
        }
    }

    /// Handle snaqlite/graph/unsubscribeWidget: cancel (if consumer) and send Cancelled.
    pub async fn unsubscribe_widget(
        &self,
        params: UnsubscribeWidgetParams,
    ) -> tower_lsp::jsonrpc::Result<()> {
        self.drain_widget_notifications().await;
        let mut w = self.widgets.lock().await;
        if let Some(maybe_tx) = w.remove(&params.widget_id) {
            if let Some(cancel_tx) = maybe_tx {
                let _ = cancel_tx.send(());
            }
            drop(w);
            self.client
                .send_notification::<WidgetDataUpdateNotification>(WidgetDataUpdateParams {
                    widget_id: params.widget_id,
                    status: WidgetDataStatus::Cancelled,
                    payload: Some(serde_json::json!({ "reason": "Unsubscribed" })),
                })
                .await;
        }
        Ok(())
    }

    /// Run the graph up to sink_uri (topological order), filling stream inputs from upstream outputs.
    /// Returns (Value, Database) for the sink node. On cycle or missing docs returns Err.
    /// When `external_streams` is `Some`, those handles are used as the sink's stream inputs (e.g. from file blocks); graph edges fill the rest.
    async fn run_node_with_graph_inputs(
        &self,
        sink_uri: &Url,
        external_streams: Option<std::collections::HashMap<String, snaq_lite_lang::StreamHandleId>>,
    ) -> Result<
        (snaq_lite_lang::Value, salsa::DatabaseImpl),
        snaq_lite_lang::RunError,
    > {
        let (order, sources, unit_registry, incoming_map) = {
            let state = self.state.lock().await;
            let graph = self.graph_state.lock().await;
            let docs = state.document_uris();
            let order = match graph.topological_order(sink_uri, &docs) {
                Some(o) => o,
                None => {
                    return Err(snaq_lite_lang::RunError::new(
                        snaq_lite_lang::RunErrorKind::InvalidArgument(
                            "graph cycle or node not in documents".to_string(),
                        ),
                    ));
                }
            };
            let sources: Vec<(Url, String)> =
                order.iter().map(|u| (u.clone(), state.source(u))).collect();
            let incoming_map: std::collections::HashMap<Url, Vec<(String, Url)>> = order
                .iter()
                .map(|u| (u.clone(), graph.incoming(u)))
                .collect();
            (
                order,
                sources,
                state.unit_registry().clone(),
                incoming_map,
            )
        };
        run_node_with_graph_inputs_impl(
            &order,
            &sources,
            &unit_registry,
            &incoming_map,
            sink_uri,
            external_streams.as_ref(),
        )
    }
}

/// Resolve external_streams (input name → stream index) to (input name → StreamHandleId).
/// On WASM the host exposes get_stream_handle_id(index); on native returns None (no file-block streams).
fn resolve_external_streams(
    name_to_index: Option<&std::collections::HashMap<String, u32>>,
) -> Option<std::collections::HashMap<String, snaq_lite_lang::StreamHandleId>> {
    let name_to_index = name_to_index?;
    if name_to_index.is_empty() {
        return Some(std::collections::HashMap::new());
    }
    #[cfg(target_arch = "wasm32")]
    {
        crate::stream_host::resolve_external_streams(name_to_index)
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        let _ = name_to_index;
        None
    }
}

/// Shared implementation of graph run: one handle per edge, feed upstream value to each.
/// When `external_streams` is `Some`, it is used only for the sink node to prefill stream_inputs
/// (e.g. file-block–fed inputs); graph edges then fill any remaining inputs.
fn run_node_with_graph_inputs_impl(
    order: &[Url],
    sources: &[(Url, String)],
    unit_registry: &snaq_lite_lang::UnitRegistry,
    incoming_map: &std::collections::HashMap<Url, Vec<(String, Url)>>,
    sink_uri: &Url,
    external_streams: Option<&std::collections::HashMap<String, snaq_lite_lang::StreamHandleId>>,
) -> Result<
    (snaq_lite_lang::Value, salsa::DatabaseImpl),
    snaq_lite_lang::RunError,
> {
    let mut output_values: std::collections::HashMap<
        Url,
        (snaq_lite_lang::Value, salsa::DatabaseImpl),
    > = std::collections::HashMap::new();
    let mut last_value = None;
    let mut last_db = None;
    for (uri, source_entry) in order.iter().zip(sources.iter()) {
        let source = &source_entry.1;
        let incoming = incoming_map.get(uri).map(|i| i.as_slice()).unwrap_or(&[]);
        let is_sink = uri == sink_uri;
        let mut stream_inputs: std::collections::HashMap<String, snaq_lite_lang::StreamHandleId> =
            if is_sink {
                external_streams.cloned().unwrap_or_default()
            } else {
                std::collections::HashMap::new()
            };
        let mut senders_by_source: std::collections::HashMap<
            Url,
            Vec<futures::channel::mpsc::UnboundedSender<snaq_lite_lang::Chunk>>,
        > = std::collections::HashMap::new();
        for (name, source_uri) in incoming {
            if stream_inputs.contains_key(name) {
                continue;
            }
            if !output_values.contains_key(source_uri) {
                continue;
            }
            let (handle_id, sender) = snaq_lite_lang::create_stream_input();
            stream_inputs.insert(name.clone(), handle_id);
            senders_by_source
                .entry(source_uri.clone())
                .or_default()
                .push(sender);
        }
        for (source_uri, senders) in senders_by_source {
            let Some((value, db)) = output_values.get(&source_uri) else {
                continue;
            };
            feed_value_to_senders(value, db, senders);
        }
        let (value, db) =
            snaq_lite_lang::run_with_stream_inputs(source, unit_registry, stream_inputs)?;
        if uri == sink_uri {
            last_value = Some(value.clone());
            last_db = Some(db.clone());
        }
        if uri != sink_uri {
            output_values.insert(uri.clone(), (value, db));
        }
    }
    Ok((
        last_value.expect("sink in order"),
        last_db.expect("sink in order"),
    ))
}

/// Feed one upstream value to multiple Chunk senders (one handle per edge when one source feeds multiple inputs).
fn feed_value_to_senders(
    value: &snaq_lite_lang::Value,
    db: &salsa::DatabaseImpl,
    senders: Vec<futures::channel::mpsc::UnboundedSender<snaq_lite_lang::Chunk>>,
) {
    match value {
        snaq_lite_lang::Value::Vector(v) => {
            let collected = snaq_lite_lang::collect_vector_stream(db, v.inner.clone());
            for sender in senders {
                let _ = sender.unbounded_send(collected.clone());
                drop(sender);
            }
        }
        _ => {
            let chunk = vec![Ok(Some(value.clone()))];
            for sender in senders {
                let _ = sender.unbounded_send(chunk.clone());
                drop(sender);
            }
        }
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

/// Native: run the stream for a widget and send WidgetDataUpdate notifications.
#[cfg(not(target_arch = "wasm32"))]
fn run_stream_consumer_for_widget(
    db: salsa::DatabaseImpl,
    inner: snaq_lite_lang::LazyVector,
    widget_id: String,
    widget_tx: WidgetNotificationSender,
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
        let mut single_display: Option<String> = None;
        let mut stream_next = stream.next();
        let mut cancel_rx = cancel_rx;
        loop {
            match select(stream_next, cancel_rx).await {
                Either::Left((opt, cr)) => {
                    cancel_rx = cr;
                    match opt {
                        Some(item) => {
                            let json = crate::pubsub::stream_element_to_json(&db, &item);
                            if total == 0 {
                                single_display = json.get("display").and_then(|v| v.as_str()).map(String::from);
                            }
                            batch.push(json);
                            total += 1;
                            if batch.len() >= BATCH_SIZE {
                                let _ = widget_tx.unbounded_send(WidgetDataUpdateParams {
                                    widget_id: widget_id.clone(),
                                    status: WidgetDataStatus::Running,
                                    payload: Some(serde_json::json!({
                                        "elements": batch.clone(),
                                        "offset": offset,
                                        "count": batch.len()
                                    })),
                                });
                                offset += batch.len() as u64;
                                batch.clear();
                            }
                            stream_next = stream.next();
                        }
                        None => break,
                    }
                }
                Either::Right(_) => return,
            }
        }
        if !batch.is_empty() {
            let _ = widget_tx.unbounded_send(WidgetDataUpdateParams {
                widget_id: widget_id.clone(),
                status: WidgetDataStatus::Running,
                payload: Some(serde_json::json!({
                    "elements": batch,
                    "offset": offset,
                    "count": batch.len()
                })),
            });
        }
        let completed_payload = if total == 1 {
            single_display
                .map(|d| serde_json::json!({ "display": d, "totalElements": 1 }))
                .unwrap_or_else(|| serde_json::json!({ "totalElements": 1 }))
        } else {
            serde_json::json!({ "totalElements": total })
        };
        let _ = widget_tx.unbounded_send(WidgetDataUpdateParams {
            widget_id,
            status: WidgetDataStatus::Completed,
            payload: Some(completed_payload),
        });
    };
    let mut pool = futures::executor::LocalPool::new();
    let spawner = pool.spawner();
    spawner.spawn_local(run).ok();
    pool.run();
}

/// Build the LSP service (same for native and WASM). Uses custom methods for snaqlite/subscribe, unsubscribe, snaqlite/graph/connect, subscribeWidget, unsubscribeWidget.
pub fn create_lsp_service() -> (LspService<SnaqLiteBackend>, tower_lsp::ClientSocket) {
    let state: SharedState = Arc::new(Mutex::new(LspState::new()));
    let subscriptions: SharedSubscriptions = Arc::new(Mutex::new(SubscriptionRegistry::new()));
    let graph_state: SharedGraphState = Arc::new(Mutex::new(graph::GraphState::new()));
    let widgets: SharedWidgetRegistry = Arc::new(Mutex::new(WidgetRegistry::new()));
    let (notification_tx, notification_rx) = futures::channel::mpsc::unbounded();
    let (widget_notification_tx, widget_notification_rx) = futures::channel::mpsc::unbounded();
    let (service, socket) = LspService::build(move |client| SnaqLiteBackend {
        client,
        state: Arc::clone(&state),
        subscriptions: Arc::clone(&subscriptions),
        graph_state: Arc::clone(&graph_state),
        widgets: Arc::clone(&widgets),
        notification_tx,
        notification_rx: Arc::new(Mutex::new(notification_rx)),
        widget_notification_tx,
        widget_notification_rx: Arc::new(Mutex::new(widget_notification_rx)),
    })
    .custom_method("snaqlite/subscribe", SnaqLiteBackend::subscribe)
    .custom_method("snaqlite/unsubscribe", SnaqLiteBackend::unsubscribe)
    .custom_method("snaqlite/graph/connect", SnaqLiteBackend::graph_connect)
    .custom_method("snaqlite/graph/disconnect", SnaqLiteBackend::graph_disconnect)
    .custom_method("snaqlite/graph/subscribeWidget", SnaqLiteBackend::subscribe_widget)
    .custom_method("snaqlite/graph/unsubscribeWidget", SnaqLiteBackend::unsubscribe_widget)
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
        assert!(state.diagnostics(&uri).is_empty());
        assert_eq!(state.document_version(&uri), Some(1));
    }

    #[test]
    fn state_update_document_parse_error_produces_diagnostic() {
        let mut state = state::LspState::new();
        let uri = Url::parse("file:///doc.snaq").unwrap();
        state.update_document(uri.clone(), 1, "syntax error @@");
        let diags = state.diagnostics(&uri);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].severity, Some(tower_lsp::lsp_types::DiagnosticSeverity::ERROR));
        assert!(!diags[0].message.is_empty());
    }

    #[test]
    fn state_update_document_valid_produces_no_diagnostics() {
        let mut state = state::LspState::new();
        let uri = Url::parse("file:///doc.snaq").unwrap();
        state.update_document(uri.clone(), 1, "1 + 2");
        assert!(state.diagnostics(&uri).is_empty());
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

    #[test]
    fn state_document_uris_returns_open_uris() {
        let mut state = state::LspState::new();
        let u1 = Url::parse("file:///a.snaq").unwrap();
        let u2 = Url::parse("snaq://graph/b.sl").unwrap();
        state.update_document(u1.clone(), 1, "1");
        state.update_document(u2.clone(), 1, "2");
        let uris = state.document_uris();
        assert_eq!(uris.len(), 2);
        assert!(uris.contains(&u1));
        assert!(uris.contains(&u2));
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

    // ---- graph state ----

    #[test]
    fn graph_connect_and_incoming() {
        let mut graph = graph::GraphState::new();
        let a = Url::parse("snaq://graph/a.sl").unwrap();
        let b = Url::parse("snaq://graph/b.sl").unwrap();
        graph.connect(a.clone(), b.clone(), "x".to_string());
        let incoming = graph.incoming(&b);
        assert_eq!(incoming.len(), 1);
        assert_eq!(incoming[0].0, "x");
        assert_eq!(incoming[0].1, a);
    }

    #[test]
    fn graph_connect_replaces_same_target_input() {
        let mut graph = graph::GraphState::new();
        let a = Url::parse("snaq://graph/a.sl").unwrap();
        let b = Url::parse("snaq://graph/b.sl").unwrap();
        let c = Url::parse("snaq://graph/c.sl").unwrap();
        graph.connect(a.clone(), b.clone(), "x".to_string());
        graph.connect(c.clone(), b.clone(), "x".to_string());
        let incoming = graph.incoming(&b);
        assert_eq!(incoming.len(), 1);
        assert_eq!(incoming[0].1, c);
    }

    #[test]
    fn graph_disconnect_removes_edge() {
        let mut graph = graph::GraphState::new();
        let a = Url::parse("snaq://graph/a.sl").unwrap();
        let b = Url::parse("snaq://graph/b.sl").unwrap();
        graph.connect(a, b.clone(), "x".to_string());
        graph.disconnect(&b, "x");
        assert!(graph.incoming(&b).is_empty());
    }

    #[test]
    fn graph_targets_from_source() {
        let mut graph = graph::GraphState::new();
        let a = Url::parse("snaq://graph/a.sl").unwrap();
        let b = Url::parse("snaq://graph/b.sl").unwrap();
        let c = Url::parse("snaq://graph/c.sl").unwrap();
        graph.connect(a.clone(), b.clone(), "x".to_string());
        graph.connect(a.clone(), c.clone(), "y".to_string());
        let targets = graph.targets_from_source(&a);
        assert_eq!(targets.len(), 2);
        assert!(targets.contains(&b));
        assert!(targets.contains(&c));
        assert!(graph.targets_from_source(&b).is_empty());
    }

    #[test]
    fn graph_topological_order_linear() {
        let mut graph = graph::GraphState::new();
        let a = Url::parse("snaq://graph/a.sl").unwrap();
        let b = Url::parse("snaq://graph/b.sl").unwrap();
        let c = Url::parse("snaq://graph/c.sl").unwrap();
        graph.connect(a.clone(), b.clone(), "x".to_string());
        graph.connect(b.clone(), c.clone(), "y".to_string());
        let docs: std::collections::HashSet<_> = [a.clone(), b.clone(), c.clone()].into_iter().collect();
        let order = graph.topological_order(&c, &docs).expect("no cycle");
        assert_eq!(order.len(), 3);
        assert_eq!(order[0], a);
        assert_eq!(order[1], b);
        assert_eq!(order[2], c);
    }

    #[test]
    fn graph_topological_order_single_node() {
        let graph = graph::GraphState::new();
        let a = Url::parse("snaq://graph/a.sl").unwrap();
        let docs: std::collections::HashSet<_> = [a.clone()].into_iter().collect();
        let order = graph.topological_order(&a, &docs).expect("no cycle");
        assert_eq!(order, vec![a]);
    }

    #[test]
    fn graph_topological_order_cycle_returns_none() {
        let mut graph = graph::GraphState::new();
        let a = Url::parse("snaq://graph/a.sl").unwrap();
        let b = Url::parse("snaq://graph/b.sl").unwrap();
        graph.connect(a.clone(), b.clone(), "x".to_string());
        graph.connect(b.clone(), a.clone(), "y".to_string());
        let docs: std::collections::HashSet<_> = [a.clone(), b.clone()].into_iter().collect();
        let order = graph.topological_order(&a, &docs);
        assert!(order.is_none(), "cycle a->b->a should yield None");
    }

    // ---- widget registry ----

    #[test]
    fn widget_registry_insert_remove() {
        let mut reg = widget_registry::WidgetRegistry::new();
        let uri = Url::parse("file:///doc.snaq").unwrap();
        let (tx, _rx) = futures::channel::oneshot::channel();
        reg.insert("w1".to_string(), uri.clone(), tx);
        let removed = reg.remove("w1");
        assert!(removed.as_ref().and_then(|x| x.as_ref()).is_some());
        assert!(reg.remove("w1").is_none());
        reg.insert_scalar("w2".to_string(), uri);
        let removed2 = reg.remove("w2");
        assert!(removed2.is_some());
        assert!(removed2.unwrap().is_none());
    }

    #[test]
    fn widget_registry_invalidate_uri() {
        let mut reg = widget_registry::WidgetRegistry::new();
        let u1 = Url::parse("file:///a.snaq").unwrap();
        let u2 = Url::parse("file:///b.snaq").unwrap();
        let (tx1, _rx1) = futures::channel::oneshot::channel();
        let (tx2, _rx2) = futures::channel::oneshot::channel();
        reg.insert("w1".to_string(), u1.clone(), tx1);
        reg.insert("w2".to_string(), u2, tx2);
        let cancelled = reg.invalidate_uri(&u1);
        assert_eq!(cancelled.len(), 1);
        assert_eq!(cancelled[0].0, "w1");
        assert!(reg.remove("w2").is_some());
    }

    #[test]
    fn widget_registry_invalidate_all() {
        let mut reg = widget_registry::WidgetRegistry::new();
        let u1 = Url::parse("file:///a.snaq").unwrap();
        let u2 = Url::parse("file:///b.snaq").unwrap();
        let (tx1, _rx1) = futures::channel::oneshot::channel();
        let (tx2, _rx2) = futures::channel::oneshot::channel();
        reg.insert("w1".to_string(), u1, tx1);
        reg.insert("w2".to_string(), u2, tx2);
        let cancelled = reg.invalidate_all();
        assert_eq!(cancelled.len(), 2);
        let ids: std::collections::HashSet<_> = cancelled.iter().map(|(id, _)| id.as_str()).collect();
        assert!(ids.contains("w1"));
        assert!(ids.contains("w2"));
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
    fn disconnect_params_deserializes_camel_case() {
        let json = r#"{"targetUri":"file:///t.snaq","targetInputName":"x"}"#;
        let params: pubsub::DisconnectParams = serde_json::from_str(json).unwrap();
        assert_eq!(params.target_uri, "file:///t.snaq");
        assert_eq!(params.target_input_name, "x");
    }

    #[test]
    fn subscribe_widget_params_deserializes_camel_case() {
        let json = r#"{"widgetId":"w1","sourceUri":"file:///n.snaq"}"#;
        let params: pubsub::SubscribeWidgetParams = serde_json::from_str(json).unwrap();
        assert_eq!(params.widget_id, "w1");
        assert_eq!(params.source_uri, "file:///n.snaq");
        assert!(params.external_streams.is_none());
    }

    #[test]
    fn subscribe_widget_params_deserializes_with_optional_external_streams() {
        let json = r#"{"widgetId":"w2","sourceUri":"file:///p.snaq","externalStreams":{"x":0,"y":1}}"#;
        let params: pubsub::SubscribeWidgetParams = serde_json::from_str(json).unwrap();
        assert_eq!(params.widget_id, "w2");
        assert_eq!(params.source_uri, "file:///p.snaq");
        let ext = params.external_streams.as_ref().unwrap();
        assert_eq!(ext.get("x"), Some(&0));
        assert_eq!(ext.get("y"), Some(&1));
    }

    #[test]
    fn widget_data_status_serializes_pascal_case() {
        use pubsub::{WidgetDataStatus, WidgetDataUpdateParams};
        let params = WidgetDataUpdateParams {
            widget_id: "w1".to_string(),
            status: WidgetDataStatus::Cancelled,
            payload: None,
        };
        let json = serde_json::to_string(&params).unwrap();
        assert!(
            json.contains("\"status\":\"Cancelled\""),
            "status should be PascalCase: {}",
            json
        );
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
