//! snaq-lite LSP server: dual-target (native stdio + WASM Web Worker) language server.

pub mod graph;
pub mod mapping;
pub mod node_result_registry;
pub mod position;
pub mod pubsub;
pub mod result_handle_registry;
pub mod state;
pub mod subscription;
pub mod widget_registry;

#[cfg(target_arch = "wasm32")]
pub mod stream_host;
#[cfg(target_arch = "wasm32")]
pub mod transport;

use futures::lock::Mutex;
use state::LspState;
use std::sync::Arc;
use tower_lsp::lsp_types::{
    CompletionItem, CompletionItemKind, CompletionOptions, CompletionParams, CompletionResponse,
    DocumentSymbolParams, DocumentSymbolResponse, GotoDefinitionParams, GotoDefinitionResponse,
    Hover, HoverContents, HoverProviderCapability, InitializeResult, InlayHint, MarkedString,
    MessageType, OneOf, ReferenceParams, RenameOptions, RenameParams, ServerCapabilities,
    TextDocumentSyncCapability, TextDocumentSyncKind, Url, WorkspaceEdit,
};

use crate::mapping::SERVER_NAME;
use crate::pubsub::{
    AddParamParams, ApplyGraphPatchParams, ApplyGraphPatchResponse, BootstrapSessionParams,
    BootstrapSessionResponse, ConnectParams, DisconnectParams, ExportCanvasDocumentParams,
    ExportCanvasDocumentResponse, FetchResultSliceParams, FetchResultSliceResponse,
    GraphPatchOperation, ImportCanvasDocumentParams, ImportCanvasDocumentResponse, NodeInputPort,
    NodeSignatureUpdatedNotification, NodeSignatureUpdatedParams, PathSegment,
    PublishNodeResultNotification, PublishResultNotification, PublishResultParams, PublishStatus,
    RemoveParamParams, RenameParamParams, ResetNamespaceParams, ResetNamespaceResponse, ResultType,
    SubscribeNodeParams, SubscribeNodeResponse, SubscribeParams, SubscribeResponse,
    SubscribeWidgetParams, UnsubscribeNodeParams, UnsubscribeParams, UnsubscribeWidgetParams,
    WidgetDataStatus, WidgetDataUpdateNotification, WidgetDataUpdateParams,
};
use crate::subscription::SubscriptionRegistry;
use crate::widget_registry::WidgetRegistry;
use crate::node_result_registry::NodeResultRegistry;
use crate::result_handle_registry::ResultHandleRegistry;
#[cfg(not(target_arch = "wasm32"))]
use tower_lsp::Server;
use tower_lsp::{Client, LanguageServer, LspService};

pub use mapping::{run_error_to_diagnostic, span_to_range};

/// Shared state for the LSP backend (async lock for both native and WASM).
pub type SharedState = Arc<Mutex<LspState>>;

/// Shared subscription registry (async lock).
pub type SharedSubscriptions = Arc<Mutex<SubscriptionRegistry>>;

/// Shared graph state (edges for connect).
pub type SharedGraphState = Arc<Mutex<graph::GraphState>>;

/// Shared widget registry (subscribeWidget / unsubscribeWidget).
pub type SharedWidgetRegistry = Arc<Mutex<WidgetRegistry>>;
pub type SharedNodeResults = Arc<Mutex<NodeResultRegistry>>;
type RunCache = std::collections::HashMap<Url, (snaq_lite_lang::Value, salsa::DatabaseImpl)>;
type SharedRunCache = Arc<Mutex<RunCache>>;
type SharedResultHandles = Arc<Mutex<ResultHandleRegistry>>;

#[derive(Clone, Debug, PartialEq, Eq)]
struct WiredNodeProjection {
    uri: Url,
    source: String,
    incoming_by_param_id: Vec<(String, Url)>,
    input_name_by_param_id: std::collections::HashMap<String, String>,
}

/// Channel to send publish notifications from background consumer to the backend.
pub type NotificationSender =
    futures::channel::mpsc::UnboundedSender<(String, PublishResultParams)>;
pub type NotificationReceiver =
    futures::channel::mpsc::UnboundedReceiver<(String, PublishResultParams)>;

/// Channel to send widget data updates from background consumer to the backend.
pub type WidgetNotificationSender = futures::channel::mpsc::UnboundedSender<WidgetDataUpdateParams>;
pub type WidgetNotificationReceiver =
    futures::channel::mpsc::UnboundedReceiver<WidgetDataUpdateParams>;

/// Backend implementing the Language Server Protocol for snaq-lite.
pub struct SnaqLiteBackend {
    pub client: Client,
    pub state: SharedState,
    pub subscriptions: SharedSubscriptions,
    pub graph_state: SharedGraphState,
    pub widgets: SharedWidgetRegistry,
    pub node_results: SharedNodeResults,
    pub notification_tx: NotificationSender,
    /// Locked receiver for draining pending publishResult notifications (sent by consumer threads).
    pub notification_rx: Arc<Mutex<NotificationReceiver>>,
    pub widget_notification_tx: WidgetNotificationSender,
    pub widget_notification_rx: Arc<Mutex<WidgetNotificationReceiver>>,
    pub run_cache: SharedRunCache,
    pub result_handles: SharedResultHandles,
}

#[tower_lsp::async_trait]
impl LanguageServer for SnaqLiteBackend {
    async fn initialize(
        &self,
        _params: tower_lsp::lsp_types::InitializeParams,
    ) -> tower_lsp::jsonrpc::Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::INCREMENTAL,
                )),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                inlay_hint_provider: Some(tower_lsp::lsp_types::OneOf::Left(true)),
                completion_provider: Some(CompletionOptions::default()),
                definition_provider: Some(OneOf::Left(true)),
                references_provider: Some(OneOf::Left(true)),
                document_symbol_provider: Some(OneOf::Left(true)),
                rename_provider: Some(OneOf::Right(RenameOptions {
                    prepare_provider: Some(false),
                    work_done_progress_options: Default::default(),
                })),
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
        let canvas_id = self.current_canvas_id().await;
        let to_cancel = {
            let mut subs = self.subscriptions.lock().await;
            subs.drain_all_entries()
        };
        for (id, maybe_cancel_tx) in to_cancel {
            if let Some(cancel_tx) = maybe_cancel_tx {
                let _ = cancel_tx.send(());
            }
            self.send_publish_result_notifications(PublishResultParams {
                subscription_id: id,
                status: PublishStatus::Cancelled,
                revision: None,
                canvas_id: canvas_id.clone(),
                uri: None,
                data: Some(serde_json::json!({ "reason": "Server shutdown" })),
            })
            .await;
        }
        let widget_cancel = {
            let mut w = self.widgets.lock().await;
            w.drain_all_entries()
        };
        for (widget_id, maybe_cancel_tx) in widget_cancel {
            if let Some(cancel_tx) = maybe_cancel_tx {
                let _ = cancel_tx.send(());
            }
            self.client
                .send_notification::<WidgetDataUpdateNotification>(WidgetDataUpdateParams {
                    widget_id,
                    status: WidgetDataStatus::Cancelled,
                    revision: None,
                    canvas_id: canvas_id.clone(),
                    uri: None,
                    payload: Some(serde_json::json!({ "reason": "Server shutdown" })),
                })
                .await;
        }
        self.result_handles.lock().await.clear();
        Ok(())
    }

    async fn did_open(&self, params: tower_lsp::lsp_types::DidOpenTextDocumentParams) {
        let uri = params.text_document.uri.clone();
        let text = params.text_document.text;
        let version = params.text_document.version;
        if let Err(err) = self.ensure_canvas_uri_request(&uri).await {
            self.client
                .log_message(
                    MessageType::ERROR,
                    format!(
                        "didOpen rejected due to canvas isolation: {}",
                        err.message
                    ),
                )
                .await;
            return;
        }
        let mut state = self.state.lock().await;
        state.update_document(uri.clone(), version, &text);
        drop(state);
        self.reconcile_graph_for_uri(&uri).await;
        let revalidated_targets = self.revalidate_related_edge_types(&uri).await;
        let force_downstream = !revalidated_targets.is_empty();
        let changed_roots = Self::recompute_roots_for_change(&uri, revalidated_targets);
        self.recompute_and_push(&changed_roots, force_downstream).await;
        self.drain_notifications().await;
        self.drain_widget_notifications().await;
        self.publish_diagnostics(uri.clone()).await;
        self.send_node_signature_updated(&uri).await;
    }

    async fn did_change(&self, params: tower_lsp::lsp_types::DidChangeTextDocumentParams) {
        let uri = params.text_document.uri.clone();
        let version = params.text_document.version;
        if let Err(err) = self.ensure_canvas_uri_request(&uri).await {
            self.client
                .log_message(
                    MessageType::ERROR,
                    format!(
                        "didChange rejected due to canvas isolation: {}",
                        err.message
                    ),
                )
                .await;
            return;
        }
        let mut state = self.state.lock().await;
        if !params.content_changes.is_empty() {
            state.apply_document_changes(uri.clone(), version, &params.content_changes);
        }
        drop(state);
        self.reconcile_graph_for_uri(&uri).await;
        let revalidated_targets = self.revalidate_related_edge_types(&uri).await;
        let force_downstream = !revalidated_targets.is_empty();
        let changed_roots = Self::recompute_roots_for_change(&uri, revalidated_targets);
        self.recompute_and_push(&changed_roots, force_downstream).await;
        self.drain_notifications().await;
        self.drain_widget_notifications().await;
        self.publish_diagnostics(uri.clone()).await;
        self.send_node_signature_updated(&uri).await;
    }

    async fn did_close(&self, params: tower_lsp::lsp_types::DidCloseTextDocumentParams) {
        let uri = params.text_document.uri.clone();
        {
            let mut state = self.state.lock().await;
            if let Err(msg) = state.ensure_canvas_uri(&uri) {
                drop(state);
                self.client
                    .log_message(
                        MessageType::ERROR,
                        format!("didClose rejected due to canvas isolation: {msg}"),
                    )
                    .await;
                return;
            }
        }
        let changed_roots = self.cleanup_for_closed_uri(&uri).await;
        self.client.publish_diagnostics(uri.clone(), Vec::new(), None).await;
        if !changed_roots.is_empty() {
            self.recompute_and_push(&changed_roots, true).await;
        }
        self.drain_notifications().await;
        self.drain_widget_notifications().await;
    }

    async fn hover(
        &self,
        params: tower_lsp::lsp_types::HoverParams,
    ) -> tower_lsp::jsonrpc::Result<Option<Hover>> {
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

    async fn completion(
        &self,
        params: CompletionParams,
    ) -> tower_lsp::jsonrpc::Result<Option<CompletionResponse>> {
        let uri = params.text_document_position.text_document.uri;
        let state = self.state.lock().await;
        let mut labels: std::collections::BTreeSet<String> =
            ["if", "then", "else", "fn", "input", "as", "per"]
                .into_iter()
                .map(String::from)
                .collect();
        for symbol in state.document_symbols(&uri) {
            labels.insert(symbol.name);
        }
        let items: Vec<CompletionItem> = labels
            .into_iter()
            .map(|label| CompletionItem {
                label,
                kind: Some(CompletionItemKind::VARIABLE),
                ..Default::default()
            })
            .collect();
        Ok(Some(CompletionResponse::Array(items)))
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> tower_lsp::jsonrpc::Result<Option<GotoDefinitionResponse>> {
        let uri = params.text_document_position_params.text_document.uri;
        let pos = params.text_document_position_params.position;
        let state = self.state.lock().await;
        let Some(ident) = state.identifier_at(&uri, pos.line, pos.character) else {
            return Ok(None);
        };
        let locations = state.definition_locations(&uri, &ident);
        if locations.is_empty() {
            return Ok(None);
        }
        Ok(Some(GotoDefinitionResponse::Array(locations)))
    }

    async fn references(
        &self,
        params: ReferenceParams,
    ) -> tower_lsp::jsonrpc::Result<Option<Vec<tower_lsp::lsp_types::Location>>> {
        let uri = params.text_document_position.text_document.uri;
        let pos = params.text_document_position.position;
        let state = self.state.lock().await;
        let Some(ident) = state.identifier_at(&uri, pos.line, pos.character) else {
            return Ok(Some(Vec::new()));
        };
        let mut refs: Vec<tower_lsp::lsp_types::Location> = state
            .reference_ranges(&uri, &ident)
            .into_iter()
            .map(|range| tower_lsp::lsp_types::Location {
                uri: uri.clone(),
                range,
            })
            .collect();
        if !params.context.include_declaration {
            let defs = state.definition_locations(&uri, &ident);
            refs.retain(|r| !defs.iter().any(|d| d.uri == r.uri && d.range == r.range));
        }
        Ok(Some(refs))
    }

    async fn document_symbol(
        &self,
        params: DocumentSymbolParams,
    ) -> tower_lsp::jsonrpc::Result<Option<DocumentSymbolResponse>> {
        let uri = params.text_document.uri;
        let state = self.state.lock().await;
        let symbols = state.document_symbols(&uri);
        Ok(Some(DocumentSymbolResponse::Nested(symbols)))
    }

    async fn rename(
        &self,
        params: RenameParams,
    ) -> tower_lsp::jsonrpc::Result<Option<WorkspaceEdit>> {
        let new_name = params.new_name;
        let valid = !new_name.is_empty()
            && new_name
                .bytes()
                .next()
                .map(|b| b.is_ascii_alphabetic() || b == b'_')
                .unwrap_or(false)
            && new_name
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b == b'_');
        if !valid {
            return Err(tower_lsp::jsonrpc::Error::invalid_params(
                "newName must be a valid identifier",
            ));
        }
        let uri = params.text_document_position.text_document.uri;
        let pos = params.text_document_position.position;
        let state = self.state.lock().await;
        let Some(ident) = state.identifier_at(&uri, pos.line, pos.character) else {
            return Ok(None);
        };
        let ranges = state.reference_ranges(&uri, &ident);
        let edits: Vec<tower_lsp::lsp_types::TextEdit> = ranges
            .into_iter()
            .map(|range| tower_lsp::lsp_types::TextEdit {
                range,
                new_text: new_name.clone(),
            })
            .collect();
        let mut changes = std::collections::HashMap::new();
        changes.insert(uri, edits);
        Ok(Some(WorkspaceEdit {
            changes: Some(changes),
            document_changes: None,
            change_annotations: None,
        }))
    }
}

impl SnaqLiteBackend {
    fn recompute_roots_for_change(changed_uri: &Url, revalidated_targets: Vec<Url>) -> Vec<Url> {
        let mut changed_roots = Vec::with_capacity(1 + revalidated_targets.len());
        let mut seen = std::collections::HashSet::with_capacity(1 + revalidated_targets.len());
        if seen.insert(changed_uri.clone()) {
            changed_roots.push(changed_uri.clone());
        }
        for target in revalidated_targets {
            if seen.insert(target.clone()) {
                changed_roots.push(target);
            }
        }
        changed_roots
    }

    fn uri_matches_prefix(uri: &str, prefix: &str) -> bool {
        if !uri.starts_with(prefix) {
            return false;
        }
        if uri.len() == prefix.len() || prefix.ends_with('/') {
            return true;
        }
        matches!(
            uri.as_bytes().get(prefix.len()).copied(),
            Some(b'/') | Some(b'?') | Some(b'#')
        )
    }

    #[cfg_attr(not(target_arch = "wasm32"), allow(dead_code))]
    fn should_stream_wasm_vector_progress(inner: &snaq_lite_lang::LazyVector) -> bool {
        !matches!(inner, snaq_lite_lang::LazyVector::FromInput(_))
    }

    fn resolve_target_input_param_id(
        input_decls: &[snaq_lite_lang::GraphInputDecl],
        target_input_name: &str,
    ) -> Option<String> {
        // Prefer stable id matches first, then fall back to display name.
        // This avoids ambiguous cases where one input's name equals another input's param_id.
        input_decls
            .iter()
            .find(|decl| decl.param_id == target_input_name)
            .or_else(|| input_decls.iter().find(|decl| decl.name == target_input_name))
            .map(|decl| decl.param_id.clone())
    }

    fn are_graph_types_compatible(source_type: &str, target_type: &str) -> bool {
        if target_type == "Undefined" {
            return true;
        }
        if source_type == target_type {
            return true;
        }
        matches!(
            (source_type, target_type),
            ("Numeric", "Symbolic") | ("FuzzyBool", "Symbolic")
        )
    }

    async fn ensure_canvas_uri_request(&self, uri: &Url) -> tower_lsp::jsonrpc::Result<()> {
        {
            let mut state = self.state.lock().await;
            if state.ensure_canvas_uri(uri).is_ok() {
                return Ok(());
            }
        }
        let is_drained = {
            let state_has_docs = self.state.lock().await.has_documents();
            let subs_empty = self.subscriptions.lock().await.is_empty();
            let widgets_empty = self.widgets.lock().await.is_empty();
            let handles_empty = self.result_handles.lock().await.is_empty();
            !state_has_docs && subs_empty && widgets_empty && handles_empty
        };
        if is_drained {
            let mut state = self.state.lock().await;
            state.force_rebind_canvas_uri(uri);
            return Ok(());
        }
        let mut state = self.state.lock().await;
        state
            .ensure_canvas_uri(uri)
            .map_err(tower_lsp::jsonrpc::Error::invalid_params)
    }

    fn ensure_snaq_canvas_uri(uri: &Url) -> tower_lsp::jsonrpc::Result<()> {
        if uri.scheme() != "snaq" || uri.host_str().is_none() {
            return Err(tower_lsp::jsonrpc::Error::invalid_params(
                "graph operations require snaq://<canvasId>/... URIs",
            ));
        }
        Ok(())
    }

    async fn ensure_graph_canvas_uri_request(&self, uri: &Url) -> tower_lsp::jsonrpc::Result<()> {
        Self::ensure_snaq_canvas_uri(uri)?;
        self.ensure_canvas_uri_request(uri).await
    }

    async fn current_canvas_id(&self) -> Option<String> {
        self.state.lock().await.active_canvas_id()
    }

    async fn upsert_result_handle_for_uri(
        &self,
        uri: &Url,
        revision: u64,
        value: snaq_lite_lang::Value,
    ) -> String {
        let mut handles = self.result_handles.lock().await;
        handles.upsert_result(uri.clone(), revision, value)
    }

    fn with_result_handle_data(
        data: Option<serde_json::Value>,
        result_handle: Option<&str>,
    ) -> Option<serde_json::Value> {
        let Some(result_handle) = result_handle else {
            return data;
        };
        let mut obj = match data {
            Some(serde_json::Value::Object(map)) => map,
            Some(other) => {
                let mut map = serde_json::Map::new();
                map.insert("value".to_string(), other);
                map
            }
            None => serde_json::Map::new(),
        };
        obj.insert(
            "resultHandle".to_string(),
            serde_json::Value::String(result_handle.to_string()),
        );
        Some(serde_json::Value::Object(obj))
    }

    fn canvas_payload_from_model(
        model: snaq_lite_lang::CanvasDocument,
    ) -> crate::pubsub::CanvasDocumentPayload {
        crate::pubsub::CanvasDocumentPayload {
            canvas_id: model.canvas_id,
            nodes: model
                .nodes
                .into_iter()
                .map(|n| crate::pubsub::CanvasNodeDocumentPayload {
                    uri: n.uri,
                    source: n.source,
                    version: n.version,
                })
                .collect(),
            edges: model
                .edges
                .into_iter()
                .map(|e| crate::pubsub::CanvasEdgePayload {
                    source_uri: e.source_uri,
                    target_uri: e.target_uri,
                    target_param_id: e.target_param_id,
                })
                .collect(),
        }
    }

    fn canvas_model_from_payload(
        payload: crate::pubsub::CanvasDocumentPayload,
    ) -> snaq_lite_lang::CanvasDocument {
        snaq_lite_lang::CanvasDocument {
            canvas_id: payload.canvas_id,
            nodes: payload
                .nodes
                .into_iter()
                .map(|n| snaq_lite_lang::CanvasNodeDocument {
                    uri: n.uri,
                    source: n.source,
                    version: n.version,
                })
                .collect(),
            edges: payload
                .edges
                .into_iter()
                .map(|e| snaq_lite_lang::CanvasEdge {
                    source_uri: e.source_uri,
                    target_uri: e.target_uri,
                    target_param_id: e.target_param_id,
                })
                .collect(),
        }
    }

    async fn send_publish_result_notifications(&self, params: PublishResultParams) {
        self.client
            .send_notification::<PublishResultNotification>(params.clone())
            .await;
        self.client
            .send_notification::<PublishNodeResultNotification>(params)
            .await;
    }

    #[cfg(target_arch = "wasm32")]
    #[allow(dead_code)]
    async fn send_wasm_vector_progress_notifications(
        &self,
        subscription_id: &str,
        db: &salsa::DatabaseImpl,
        inner: snaq_lite_lang::LazyVector,
        revision: u64,
        canvas_id: Option<String>,
        uri: &Url,
        result_handle: &str,
    ) {
        use futures::stream::StreamExt;
        const BATCH_SIZE: usize = 100;
        // Do not consume non-replayable input receivers here.
        // `fetchResultSlice` owns forward-only consumption for handle-scoped `FromInput` values.
        if !Self::should_stream_wasm_vector_progress(&inner) {
            return;
        }
        let mut stream = snaq_lite_lang::vector_into_stream(db, inner);
        let mut batch: Vec<serde_json::Value> = Vec::with_capacity(BATCH_SIZE);
        let mut offset: u64 = 0;
        while let Some(item) = stream.next().await {
            batch.push(crate::pubsub::stream_element_to_json(db, &item));
            if batch.len() >= BATCH_SIZE {
                self.send_publish_result_notifications(PublishResultParams {
                    subscription_id: subscription_id.to_string(),
                    status: PublishStatus::Running,
                    revision: Some(revision),
                    canvas_id: canvas_id.clone(),
                    uri: Some(uri.to_string()),
                    data: Self::with_result_handle_data(
                        Some(serde_json::json!({
                            "elements": batch,
                            "offset": offset,
                            "count": BATCH_SIZE
                        })),
                        Some(result_handle),
                    ),
                })
                .await;
                offset += BATCH_SIZE as u64;
                batch = Vec::with_capacity(BATCH_SIZE);
            }
        }
        if !batch.is_empty() {
            let count = batch.len();
            self.send_publish_result_notifications(PublishResultParams {
                subscription_id: subscription_id.to_string(),
                status: PublishStatus::Running,
                revision: Some(revision),
                canvas_id: canvas_id.clone(),
                uri: Some(uri.to_string()),
                data: Self::with_result_handle_data(
                    Some(serde_json::json!({
                        "elements": batch,
                        "offset": offset,
                        "count": count
                    })),
                    Some(result_handle),
                ),
            })
            .await;
        }
    }

    #[cfg(target_arch = "wasm32")]
    async fn publish_wasm_vector_subscription_payload(
        &self,
        subscription_id: &str,
        uri: &Url,
        revision: Option<u64>,
        canvas_id: Option<String>,
        payload: serde_json::Value,
        result_handle: Option<&str>,
    ) {
        self.send_publish_result_notifications(PublishResultParams {
            subscription_id: subscription_id.to_string(),
            status: PublishStatus::Running,
            revision,
            canvas_id: canvas_id.clone(),
            uri: Some(uri.to_string()),
            data: Self::with_result_handle_data(
                Some(serde_json::json!({
                    "elements": [],
                    "offset": 0,
                    "count": 0
                })),
                result_handle,
            ),
        })
        .await;
        self.send_publish_result_notifications(PublishResultParams {
            subscription_id: subscription_id.to_string(),
            status: PublishStatus::Completed,
            revision,
            canvas_id,
            uri: Some(uri.to_string()),
            data: Some(payload),
        })
        .await;
    }

    async fn publish_scalar_subscription_payload(
        &self,
        subscription_id: &str,
        uri: &Url,
        revision: Option<u64>,
        canvas_id: Option<String>,
        display: String,
        result_handle: Option<&str>,
    ) {
        self.send_publish_result_notifications(PublishResultParams {
            subscription_id: subscription_id.to_string(),
            status: PublishStatus::Completed,
            revision,
            canvas_id,
            uri: Some(uri.to_string()),
            data: Self::with_result_handle_data(Some(serde_json::json!({ "display": display })), result_handle),
        })
        .await;
    }

    async fn cancel_subscription_entries(
        &self,
        entries: Vec<(String, Option<futures::channel::oneshot::Sender<()>>)>,
        reason: &str,
    ) {
        let canvas_id = self.current_canvas_id().await;
        for (subscription_id, maybe_tx) in entries {
            if let Some(tx) = maybe_tx {
                let _ = tx.send(());
            }
            self.send_publish_result_notifications(PublishResultParams {
                subscription_id,
                status: PublishStatus::Cancelled,
                revision: None,
                canvas_id: canvas_id.clone(),
                uri: None,
                data: Some(serde_json::json!({ "reason": reason })),
            })
            .await;
        }
    }

    async fn cancel_widget_entries(
        &self,
        entries: Vec<(String, Option<futures::channel::oneshot::Sender<()>>)>,
        reason: &str,
    ) {
        let canvas_id = self.current_canvas_id().await;
        for (widget_id, maybe_tx) in entries {
            if let Some(tx) = maybe_tx {
                let _ = tx.send(());
            }
            self.client
                .send_notification::<WidgetDataUpdateNotification>(WidgetDataUpdateParams {
                    widget_id,
                    status: WidgetDataStatus::Cancelled,
                    revision: None,
                    canvas_id: canvas_id.clone(),
                    uri: None,
                    payload: Some(serde_json::json!({ "reason": reason })),
                })
                .await;
        }
    }

    async fn cleanup_for_closed_uri(&self, uri: &Url) -> Vec<Url> {
        let docs_before = {
            let state = self.state.lock().await;
            state.document_uris()
        };
        let descendants = {
            let graph = self.graph_state.lock().await;
            graph.descendants_from_source(uri, &docs_before)
        };
        {
            let mut state = self.state.lock().await;
            let _ = state.remove_document(uri);
        }
        {
            let mut graph = self.graph_state.lock().await;
            let _ = graph.remove_edges_for_uri(uri);
        }
        {
            let mut node_results = self.node_results.lock().await;
            let _ = node_results.remove(uri);
        }
        {
            let mut handles = self.result_handles.lock().await;
            let _ = handles.remove_for_uri(uri);
        }
        let subscription_entries = {
            let mut subs = self.subscriptions.lock().await;
            subs.remove_uri_all(uri)
        };
        self.cancel_subscription_entries(subscription_entries, "Document closed")
            .await;
        let widget_entries = {
            let mut widgets = self.widgets.lock().await;
            widgets.invalidate_uri(uri)
        };
        self.cancel_widget_entries(widget_entries, "Document closed")
            .await;
        descendants
            .into_iter()
            .filter(|u| u != uri)
            .collect::<Vec<Url>>()
    }

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
            self.send_publish_result_notifications(params).await;
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

    /// Reconcile edges that target the given URI against the current input declaration names.
    async fn reconcile_graph_for_uri(&self, uri: &Url) {
        let maybe_valid_inputs: Option<std::collections::HashSet<String>> = {
            let state = self.state.lock().await;
            state
                .get_document(uri)
                .and_then(|d| {
                    if !d.parse_succeeded {
                        return None;
                    }
                    d.root_def.as_ref().map(|root| {
                        snaq_lite_lang::extract_input_decls_from_block_with_ids(root)
                            .into_iter()
                            .map(|decl| decl.param_id)
                            .collect()
                    })
                })
        };
        let Some(valid_inputs) = maybe_valid_inputs else {
            // Keep existing graph wiring when the target document is temporarily invalid.
            return;
        };
        let _removed = {
            let mut graph = self.graph_state.lock().await;
            graph.reconcile_target_inputs(uri, &valid_inputs)
        };
    }

    async fn revalidate_related_edge_types(&self, changed_uri: &Url) -> Vec<Url> {
        let mut targets = vec![changed_uri.clone()];
        let mut seen = std::collections::HashSet::new();
        seen.insert(changed_uri.clone());
        let downstream = { self.graph_state.lock().await.targets_from_source(changed_uri) };
        for uri in downstream {
            if seen.insert(uri.clone()) {
                targets.push(uri);
            }
        }
        let mut disconnected_targets = Vec::new();
        for target_uri in targets {
            if self.revalidate_target_edge_types(&target_uri).await {
                disconnected_targets.push(target_uri);
            }
        }
        disconnected_targets
    }

    async fn revalidate_target_edge_types(&self, target_uri: &Url) -> bool {
        let incoming = { self.graph_state.lock().await.incoming(target_uri) };
        if incoming.is_empty() {
            return false;
        }
        let (target_inputs, source_docs, unit_registry) = {
            let state = self.state.lock().await;
            let Some(target_doc) = state.get_document(target_uri) else {
                return false;
            };
            if !target_doc.parse_succeeded {
                return false;
            }
            let target_inputs: std::collections::HashMap<String, String> = target_doc
                .root_def
                .as_ref()
                .map(snaq_lite_lang::extract_input_decls_from_block_with_ids)
                .unwrap_or_default()
                .into_iter()
                .map(|decl| (decl.param_id, decl.type_name))
                .collect();
            let source_docs: std::collections::HashMap<Url, (String, bool)> = incoming
                .iter()
                .map(|(_, source_uri)| {
                    let parse_succeeded = state
                        .get_document(source_uri)
                        .map(|d| d.parse_succeeded)
                        .unwrap_or(false);
                    (source_uri.clone(), (state.source(source_uri), parse_succeeded))
                })
                .collect();
            (
                target_inputs,
                source_docs,
                state.unit_registry().clone(),
            )
        };
        let mut invalid_inputs: Vec<String> = Vec::new();
        for (input_name, source_uri) in incoming {
            let Some(target_type) = target_inputs.get(&input_name) else {
                continue;
            };
            if target_type == "Undefined" {
                continue;
            }
            let Some((source_source, source_parse_succeeded)) = source_docs.get(&source_uri) else {
                invalid_inputs.push(input_name.clone());
                continue;
            };
            if !*source_parse_succeeded {
                continue;
            }
            let Some(source_output_type) = snaq_lite_lang::run_with_stream_inputs(
                source_source,
                &unit_registry,
                std::collections::HashMap::new(),
            )
            .ok()
            .and_then(|(value, _)| snaq_lite_lang::value_type_name(&value))
            else {
                // Keep existing wiring on transient source run failures.
                continue;
            };
            if !Self::are_graph_types_compatible(&source_output_type, target_type) {
                invalid_inputs.push(input_name);
            }
        }
        if invalid_inputs.is_empty() {
            return false;
        }
        let mut graph = self.graph_state.lock().await;
        for input_name in invalid_inputs {
            graph.disconnect(target_uri, &input_name);
        }
        true
    }

    async fn update_widget_subscribers_for_uri(
        &self,
        uri: &Url,
        result: Result<(snaq_lite_lang::Value, salsa::DatabaseImpl), snaq_lite_lang::RunError>,
        revision: Option<u64>,
        result_handle: Option<&str>,
    ) {
        let widget_ids = { self.widgets.lock().await.ids_for_uri(uri) };
        if widget_ids.is_empty() {
            return;
        }
        let canvas_id = { self.state.lock().await.active_canvas_id() };
        match result {
            Ok((value, db)) => {
                let payload = Self::build_completed_payload(&value, &db, result_handle);
                for widget_id in widget_ids {
                    self.widgets
                        .lock()
                        .await
                        .set_cached_value(&widget_id, Some(value.clone()));
                    self.client
                        .send_notification::<WidgetDataUpdateNotification>(WidgetDataUpdateParams {
                            widget_id,
                            status: WidgetDataStatus::Completed,
                            revision,
                            canvas_id: canvas_id.clone(),
                            uri: Some(uri.to_string()),
                            payload: Some(payload.clone()),
                        })
                        .await;
                }
            }
            Err(e) => {
                for widget_id in widget_ids {
                    self.widgets.lock().await.set_cached_value(&widget_id, None);
                    self.client
                        .send_notification::<WidgetDataUpdateNotification>(WidgetDataUpdateParams {
                            widget_id,
                            status: WidgetDataStatus::Error,
                            revision,
                            canvas_id: canvas_id.clone(),
                            uri: Some(uri.to_string()),
                            payload: Some(serde_json::json!({ "message": e.to_string() })),
                        })
                        .await;
                }
            }
        }
    }

    async fn update_document_subscribers_for_uri(
        &self,
        uri: &Url,
        result: Result<(snaq_lite_lang::Value, salsa::DatabaseImpl), snaq_lite_lang::RunError>,
        revision: Option<u64>,
        result_handle: Option<&str>,
    ) {
        let ids = { self.subscriptions.lock().await.ids_for_uri(uri) };
        let canvas_id = { self.state.lock().await.active_canvas_id() };
        for subscription_id in ids {
            // Stop previous stream consumer for this subscription before pushing fresh value.
            if let Some(tx) = self.subscriptions.lock().await.take_cancel_tx(&subscription_id) {
                let _ = tx.send(());
            }
            match result.clone() {
                Ok((value, db)) => match value {
                    snaq_lite_lang::Value::Vector(v) => {
                        #[cfg(not(target_arch = "wasm32"))]
                        {
                            let inner = v.inner.clone();
                            let (cancel_tx, cancel_rx) = futures::channel::oneshot::channel();
                            self.subscriptions
                                .lock()
                                .await
                                .set_cancel_tx(&subscription_id, Some(cancel_tx));
                            let sid = subscription_id.clone();
                            let notification_tx = self.notification_tx.clone();
                            let canvas_id_for_stream = canvas_id.clone();
                            let uri_for_stream = uri.to_string();
                            let result_handle_for_stream =
                                result_handle.map(ToOwned::to_owned);
                            std::thread::spawn(move || {
                                run_stream_consumer(
                                    db,
                                    inner,
                                    sid,
                                    revision,
                                    canvas_id_for_stream,
                                    Some(uri_for_stream),
                                    result_handle_for_stream,
                                    notification_tx,
                                    cancel_rx,
                                );
                            });
                        }
                        #[cfg(target_arch = "wasm32")]
                        {
                            self.publish_wasm_vector_subscription_payload(
                                &subscription_id,
                                &uri,
                                revision,
                                canvas_id.clone(),
                                Self::build_completed_payload(
                                    &snaq_lite_lang::Value::Vector(v.clone()),
                                    &db,
                                    result_handle,
                                ),
                                result_handle,
                            )
                            .await;
                            self.subscriptions
                                .lock()
                                .await
                                .set_cancel_tx(&subscription_id, None);
                        }
                    }
                    _ => {
                        self.publish_scalar_subscription_payload(
                            &subscription_id,
                            uri,
                            revision,
                            canvas_id.clone(),
                            snaq_lite_lang::format_value_for_display(&db, &value)
                                .unwrap_or_else(|_| "<error>".to_string()),
                            result_handle,
                        )
                        .await;
                        self.subscriptions
                            .lock()
                            .await
                            .set_cancel_tx(&subscription_id, None);
                    }
                },
                Err(e) => {
                    self.send_publish_result_notifications(PublishResultParams {
                        subscription_id: subscription_id.clone(),
                        status: PublishStatus::Error,
                        revision,
                        canvas_id: canvas_id.clone(),
                        uri: Some(uri.to_string()),
                        data: Some(serde_json::json!({ "message": e.to_string() })),
                    })
                    .await;
                    self.subscriptions
                        .lock()
                        .await
                        .set_cancel_tx(&subscription_id, None);
                }
            }
        }
    }

    /// Eager recompute for changed URIs + descendants and push update events.
    async fn recompute_and_push(&self, changed: &[Url], force_downstream: bool) {
        let docs = {
            let state = self.state.lock().await;
            state.document_uris()
        };
        let mut shared_cache = { self.run_cache.lock().await.clone() };
        let mut queue: std::collections::VecDeque<Url> = std::collections::VecDeque::new();
        let mut queued: std::collections::HashSet<Url> = std::collections::HashSet::new();
        // Seed changed roots; descendants are always enqueued for this mutation wave.
        for uri in changed {
            if docs.contains(uri) && queued.insert(uri.clone()) {
                shared_cache.remove(uri);
                queue.push_back(uri.clone());
            }
        }
        while let Some(uri) = queue.pop_front() {
            let result = self
                .run_node_with_graph_inputs_cached(&uri, None, &mut shared_cache)
                .await;
            let (revision, semantic_changed, result_handle) = {
                let mut store = self.node_results.lock().await;
                match &result {
                    Ok((value, _)) => {
                        let (rev, changed) =
                            store.upsert_value_if_changed(uri.clone(), value.clone());
                        (Some(rev), changed, Some((rev, value.clone())))
                    }
                    Err(e) => {
                        let (rev, changed) =
                            store.upsert_error_if_changed(uri.clone(), e.to_string());
                        (Some(rev), changed, None)
                    }
                }
            };
            let result_handle = if let Some((rev, value)) = result_handle {
                Some(self.upsert_result_handle_for_uri(&uri, rev, value).await)
            } else {
                let _ = self.result_handles.lock().await.remove_for_uri(&uri);
                None
            };
            self.update_widget_subscribers_for_uri(
                &uri,
                result.clone(),
                revision,
                result_handle.as_deref(),
            )
            .await;
            self.update_document_subscribers_for_uri(&uri, result, revision, result_handle.as_deref())
                .await;
            if force_downstream || semantic_changed {
                let downstream = { self.graph_state.lock().await.targets_from_source(&uri) };
                for target in downstream {
                    if !docs.contains(&target) || !queued.insert(target.clone()) {
                        continue;
                    }
                    shared_cache.remove(&target);
                    queue.push_back(target);
                }
            }
        }
        let mut cache = self.run_cache.lock().await;
        *cache = shared_cache;
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
                snaq_lite_lang::extract_input_decls_from_block_with_ids(root)
                    .into_iter()
                    .map(|decl| NodeInputPort {
                        name: decl.name,
                        param_id: decl.param_id,
                        r#type: decl.type_name,
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

    /// Handle snaqlite/subscribe: run document (root-only), return subscription id; if root is a vector, spawn consumer and stream batches.
    pub async fn subscribe(
        &self,
        params: SubscribeParams,
    ) -> tower_lsp::jsonrpc::Result<SubscribeResponse> {
        self.drain_notifications().await;
        let uri = params.text_document.uri;
        self.ensure_canvas_uri_request(&uri).await?;
        let state = self.state.lock().await;
        if !state.has_document(&uri) {
            drop(state);
            return Err(tower_lsp::jsonrpc::Error::invalid_params(
                "document not open or URI mismatch",
            ));
        }
        let source = state.source(&uri);
        let unit_registry = state.unit_registry().clone();
        let version = state.document_version(&uri);
        let canvas_id = state.active_canvas_id();
        drop(state);
        let stream_inputs = std::collections::HashMap::new();
        let result = snaq_lite_lang::run_with_stream_inputs(&source, &unit_registry, stream_inputs);
        match result {
            Err(e) => Err(tower_lsp::jsonrpc::Error::invalid_params(format!(
                "run error: {e}"
            ))),
            Ok((value, db)) => {
                let revision = {
                    let mut store = self.node_results.lock().await;
                    store.upsert_value(uri.clone(), value.clone())
                };
                let result_handle = self
                    .upsert_result_handle_for_uri(&uri, revision, value.clone())
                    .await;
                let subscription_id = uuid::Uuid::new_v4().to_string();
                self.subscriptions
                    .lock()
                    .await
                    .insert(subscription_id.clone(), uri.clone(), version, None);
                match &value {
                    snaq_lite_lang::Value::Vector(v) => {
                        let inner = v.inner.clone();
                        let (cancel_tx, cancel_rx) = futures::channel::oneshot::channel();
                        self.subscriptions
                            .lock()
                            .await
                            .set_cancel_tx(&subscription_id, Some(cancel_tx));
                        #[cfg(not(target_arch = "wasm32"))]
                        {
                            let sid = subscription_id.clone();
                            let notification_tx = self.notification_tx.clone();
                            let canvas_id_for_stream = canvas_id.clone();
                            let uri_for_stream = uri.to_string();
                            let result_handle_for_stream = result_handle.clone();
                            std::thread::spawn(move || {
                                run_stream_consumer(
                                    db,
                                    inner,
                                    sid,
                                    Some(revision),
                                    canvas_id_for_stream,
                                    Some(uri_for_stream),
                                    Some(result_handle_for_stream),
                                    notification_tx,
                                    cancel_rx,
                                );
                            });
                        }
                        #[cfg(target_arch = "wasm32")]
                        {
                            let _ = cancel_rx;
                            let _ = inner;
                            self.publish_wasm_vector_subscription_payload(
                                &subscription_id,
                                &uri,
                                Some(revision),
                                canvas_id.clone(),
                                Self::build_completed_payload(
                                    &snaq_lite_lang::Value::Vector(v.clone()),
                                    &db,
                                    Some(&result_handle),
                                ),
                                Some(&result_handle),
                            )
                            .await;
                        }
                    }
                    _ => {
                        self.publish_scalar_subscription_payload(
                            &subscription_id,
                            &uri,
                            Some(revision),
                            canvas_id.clone(),
                            snaq_lite_lang::format_value_for_display(&db, &value)
                                .unwrap_or_else(|_| "<error>".to_string()),
                            Some(&result_handle),
                        )
                        .await;
                    }
                }
                Ok(SubscribeResponse { subscription_id })
            }
        }
    }

    /// Handle snaqlite/subscribeNode: canonical node-centric subscription API.
    /// Internally reuses the same subscription runtime as snaqlite/subscribe.
    pub async fn subscribe_node(
        &self,
        params: SubscribeNodeParams,
    ) -> tower_lsp::jsonrpc::Result<SubscribeNodeResponse> {
        self.drain_notifications().await;
        let uri = Url::parse(&params.source_uri)
            .map_err(|_| tower_lsp::jsonrpc::Error::invalid_params("invalid sourceUri"))?;
        self.ensure_canvas_uri_request(&uri).await?;
        let state = self.state.lock().await;
        if !state.has_document(&uri) {
            drop(state);
            return Err(tower_lsp::jsonrpc::Error::invalid_params(
                "document not open or URI mismatch",
            ));
        }
        let version = state.document_version(&uri);
        let canvas_id = state.active_canvas_id();
        drop(state);

        let result = self.run_node_with_graph_inputs(&uri, None).await;
        match result {
            Err(e) => Err(tower_lsp::jsonrpc::Error::invalid_params(format!(
                "run error: {e}"
            ))),
            Ok((value, db)) => {
                let revision = {
                    let mut store = self.node_results.lock().await;
                    store.upsert_value(uri.clone(), value.clone())
                };
                let result_handle = self
                    .upsert_result_handle_for_uri(&uri, revision, value.clone())
                    .await;
                let subscription_id = uuid::Uuid::new_v4().to_string();
                self.subscriptions
                    .lock()
                    .await
                    .insert(subscription_id.clone(), uri.clone(), version, None);
                match &value {
                    snaq_lite_lang::Value::Vector(v) => {
                        let inner = v.inner.clone();
                        let (cancel_tx, cancel_rx) = futures::channel::oneshot::channel();
                        self.subscriptions
                            .lock()
                            .await
                            .set_cancel_tx(&subscription_id, Some(cancel_tx));
                        #[cfg(not(target_arch = "wasm32"))]
                        {
                            let sid = subscription_id.clone();
                            let notification_tx = self.notification_tx.clone();
                            let canvas_id_for_stream = canvas_id.clone();
                            let uri_for_stream = uri.to_string();
                            let result_handle_for_stream = result_handle.clone();
                            std::thread::spawn(move || {
                                run_stream_consumer(
                                    db,
                                    inner,
                                    sid,
                                    Some(revision),
                                    canvas_id_for_stream,
                                    Some(uri_for_stream),
                                    Some(result_handle_for_stream),
                                    notification_tx,
                                    cancel_rx,
                                );
                            });
                        }
                        #[cfg(target_arch = "wasm32")]
                        {
                            let _ = cancel_rx;
                            let _ = inner;
                            self.publish_wasm_vector_subscription_payload(
                                &subscription_id,
                                &uri,
                                Some(revision),
                                canvas_id.clone(),
                                Self::build_completed_payload(
                                    &snaq_lite_lang::Value::Vector(v.clone()),
                                    &db,
                                    Some(&result_handle),
                                ),
                                Some(&result_handle),
                            )
                            .await;
                        }
                    }
                    _ => {
                        self.publish_scalar_subscription_payload(
                            &subscription_id,
                            &uri,
                            Some(revision),
                            canvas_id.clone(),
                            snaq_lite_lang::format_value_for_display(&db, &value)
                                .unwrap_or_else(|_| "<error>".to_string()),
                            Some(&result_handle),
                        )
                        .await;
                    }
                }
                Ok(SubscribeNodeResponse {
                    subscription_id,
                    result_handle: Some(result_handle),
                })
            }
        }
    }

    /// Handle snaqlite/unsubscribe: cancel subscription and remove from registry.
    pub async fn unsubscribe(&self, params: UnsubscribeParams) -> tower_lsp::jsonrpc::Result<()> {
        self.drain_notifications().await;
        let mut subs = self.subscriptions.lock().await;
        if let Some(Some(cancel_tx)) = subs.remove(&params.subscription_id) {
            let _ = cancel_tx.send(());
        }
        Ok(())
    }

    /// Handle snaqlite/unsubscribeNode: canonical node-centric unsubscribe API.
    pub async fn unsubscribe_node(
        &self,
        params: UnsubscribeNodeParams,
    ) -> tower_lsp::jsonrpc::Result<()> {
        self.unsubscribe(UnsubscribeParams {
            subscription_id: params.subscription_id,
        })
        .await
    }

    /// Handle snaqlite/graph/connect: type-check and add edge.
    pub async fn graph_connect(&self, params: ConnectParams) -> tower_lsp::jsonrpc::Result<()> {
        let source_uri = Url::parse(&params.source_uri)
            .map_err(|_| tower_lsp::jsonrpc::Error::invalid_params("invalid sourceUri"))?;
        let target_uri = Url::parse(&params.target_uri)
            .map_err(|_| tower_lsp::jsonrpc::Error::invalid_params("invalid targetUri"))?;
        self.ensure_graph_canvas_uri_request(&source_uri).await?;
        self.ensure_graph_canvas_uri_request(&target_uri).await?;
        {
            let state = self.state.lock().await;
            let docs = state.document_uris();
            let graph = self.graph_state.lock().await;
            if graph.would_create_cycle(&source_uri, &target_uri, &docs) {
                return Err(tower_lsp::jsonrpc::Error {
                    code: tower_lsp::jsonrpc::ErrorCode::ServerError(-32002),
                    message: "graph cycle detected".into(),
                    data: None,
                });
            }
        }
        let (target_input_type, target_param_id) = {
            let state = self.state.lock().await;
            let _source_doc = state.get_document(&source_uri).ok_or_else(|| {
                tower_lsp::jsonrpc::Error::invalid_params("source document not open")
            })?;
            let target_doc = state.get_document(&target_uri).ok_or_else(|| {
                tower_lsp::jsonrpc::Error::invalid_params("target document not open")
            })?;
            let target_inputs = target_doc
                .root_def
                .as_ref()
                .map(snaq_lite_lang::extract_input_decls_from_block_with_ids)
                .unwrap_or_default();
            let target_param_id =
                Self::resolve_target_input_param_id(&target_inputs, &params.target_input_name);
            let target_input_type = target_param_id.as_ref().and_then(|resolved_param_id| {
                target_inputs
                    .iter()
                    .find(|decl| decl.param_id == *resolved_param_id)
                    .map(|decl| decl.type_name.clone())
            });
            let (target_param_id, target_input_type) = target_param_id
                .zip(target_input_type)
                .ok_or_else(|| {
                tower_lsp::jsonrpc::Error::invalid_params(format!(
                    "target has no input named or id '{}'",
                    params.target_input_name
                ))
            })?;
            (target_input_type, target_param_id)
        };
        let source_output_type = self
            .run_node_with_graph_inputs(&source_uri, None)
            .await
        .ok()
            .and_then(|(value, _db)| snaq_lite_lang::value_type_name(&value))
        .unwrap_or_else(|| "Unknown".to_string());
        // Target input type "Undefined" means accept any (e.g. presentation boxes).
        let source_type_unknown = source_output_type == "Unknown";
        if !source_type_unknown
            && !Self::are_graph_types_compatible(&source_output_type, &target_input_type)
        {
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
            graph.connect(source_uri, target_uri.clone(), target_param_id);
        }
        self.recompute_and_push(std::slice::from_ref(&target_uri), true).await;
        self.drain_widget_notifications().await;
        self.drain_notifications().await;
        Ok(())
    }

    /// Handle snaqlite/graph/disconnect: remove edge and invalidate widgets for the target node.
    pub async fn graph_disconnect(
        &self,
        params: DisconnectParams,
    ) -> tower_lsp::jsonrpc::Result<()> {
        let target_uri = Url::parse(&params.target_uri)
            .map_err(|_| tower_lsp::jsonrpc::Error::invalid_params("invalid targetUri"))?;
        self.ensure_graph_canvas_uri_request(&target_uri).await?;
        let target_param_id = {
            let state = self.state.lock().await;
            let target_doc = state.get_document(&target_uri).ok_or_else(|| {
                tower_lsp::jsonrpc::Error::invalid_params("target document not open")
            })?;
            let target_inputs = target_doc
                .root_def
                .as_ref()
                .map(snaq_lite_lang::extract_input_decls_from_block_with_ids)
                .unwrap_or_default();
            Self::resolve_target_input_param_id(&target_inputs, &params.target_input_name)
                .unwrap_or_else(|| params.target_input_name.clone())
        };
        {
            let mut graph = self.graph_state.lock().await;
            graph.disconnect(&target_uri, &target_param_id);
        }
        self.recompute_and_push(std::slice::from_ref(&target_uri), true).await;
        self.drain_widget_notifications().await;
        self.drain_notifications().await;
        Ok(())
    }

    fn is_valid_identifier(input: &str) -> bool {
        let mut chars = input.chars();
        match chars.next() {
            Some(c) if c == '_' || c.is_ascii_alphabetic() => {}
            _ => return false,
        }
        chars.all(|c| c == '_' || c.is_ascii_alphanumeric())
    }

    fn parsed_input_decls(
        source: &str,
    ) -> tower_lsp::jsonrpc::Result<Vec<(String, String, String, snaq_lite_lang::Span)>> {
        let parsed = snaq_lite_lang::parse(source)
            .map_err(|e| tower_lsp::jsonrpc::Error::invalid_params(format!("parse error: {e}")))?;
        let snaq_lite_lang::ir::SpannedExprDefKind::Block(items) = parsed.value else {
            return Ok(Vec::new());
        };
        let mut out = Vec::new();
        for item in items {
            if let snaq_lite_lang::ir::SpannedExprDefKind::InputDecl(name, param_id, type_name) =
                item.value
            {
                out.push((name, param_id, type_name, item.span));
            }
        }
        Ok(out)
    }

    fn replace_span(source: &str, span: snaq_lite_lang::Span, replacement: &str) -> String {
        let mut out = String::new();
        out.push_str(&source[..span.start]);
        out.push_str(replacement);
        out.push_str(&source[span.end..]);
        out
    }

    fn replace_identifier_spans(
        source: &str,
        spans: &[snaq_lite_lang::Span],
        replacement: &str,
    ) -> String {
        let mut ordered = spans.to_vec();
        ordered.sort_by(|a, b| b.start.cmp(&a.start).then_with(|| b.end.cmp(&a.end)));
        let mut out = source.to_string();
        for span in ordered {
            if span.start >= span.end || span.end > out.len() {
                continue;
            }
            if !out.is_char_boundary(span.start) || !out.is_char_boundary(span.end) {
                continue;
            }
            out.replace_range(span.start..span.end, replacement);
        }
        out
    }

    fn collect_param_symbol_rename_spans(
        source: &str,
        target_param_id: &str,
        old_name: &str,
        unit_registry: &snaq_lite_lang::UnitRegistry,
    ) -> tower_lsp::jsonrpc::Result<Vec<snaq_lite_lang::Span>> {
        use snaq_lite_lang::ir::{SpannedCallArg, SpannedExprDef, SpannedExprDefKind};

        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        enum BindingOrigin {
            TargetParam,
            Other,
        }

        fn current_binding(
            scopes: &[std::collections::HashMap<String, BindingOrigin>],
            name: &str,
        ) -> Option<BindingOrigin> {
            scopes.iter().rev().find_map(|scope| scope.get(name).copied())
        }

        fn visit_expr(
            expr: &SpannedExprDef,
            old_name: &str,
            scopes: &mut Vec<std::collections::HashMap<String, BindingOrigin>>,
            out: &mut Vec<snaq_lite_lang::Span>,
            target_param_id: &str,
        ) {
            match &expr.value {
                SpannedExprDefKind::LitSymbol(name) => {
                    if name == old_name
                        && matches!(current_binding(scopes, old_name), Some(BindingOrigin::TargetParam))
                    {
                        out.push(expr.span);
                    }
                }
                SpannedExprDefKind::Add(l, r)
                | SpannedExprDefKind::Sub(l, r)
                | SpannedExprDefKind::Mul(l, r)
                | SpannedExprDefKind::Div(l, r)
                | SpannedExprDefKind::Eq(l, r)
                | SpannedExprDefKind::Ne(l, r)
                | SpannedExprDefKind::Lt(l, r)
                | SpannedExprDefKind::Le(l, r)
                | SpannedExprDefKind::Gt(l, r)
                | SpannedExprDefKind::Ge(l, r)
                | SpannedExprDefKind::And(l, r)
                | SpannedExprDefKind::As(l, r)
                | SpannedExprDefKind::WithPrecision(l, r) => {
                    visit_expr(l, old_name, scopes, out, target_param_id);
                    visit_expr(r, old_name, scopes, out, target_param_id);
                }
                SpannedExprDefKind::Index(base, _) | SpannedExprDefKind::Member(base, _) => {
                    visit_expr(base, old_name, scopes, out, target_param_id);
                }
                SpannedExprDefKind::Neg(inner) | SpannedExprDefKind::Transpose(inner) => {
                    visit_expr(inner, old_name, scopes, out, target_param_id);
                }
                SpannedExprDefKind::Call(_, args)
                | SpannedExprDefKind::CallExpr(_, args)
                | SpannedExprDefKind::MethodCall(_, _, args) => {
                    if let SpannedExprDefKind::CallExpr(callee, _) = &expr.value {
                        visit_expr(callee, old_name, scopes, out, target_param_id);
                    }
                    if let SpannedExprDefKind::MethodCall(base, _, _) = &expr.value {
                        visit_expr(base, old_name, scopes, out, target_param_id);
                    }
                    for arg in args {
                        match arg {
                            SpannedCallArg::Positional(e) | SpannedCallArg::Named(_, e) => {
                                visit_expr(e, old_name, scopes, out, target_param_id);
                            }
                        }
                    }
                }
                SpannedExprDefKind::If(c, t, e) => {
                    visit_expr(c, old_name, scopes, out, target_param_id);
                    visit_expr(t, old_name, scopes, out, target_param_id);
                    visit_expr(e, old_name, scopes, out, target_param_id);
                }
                SpannedExprDefKind::VecLiteral(items) => {
                    for item in items {
                        visit_expr(item, old_name, scopes, out, target_param_id);
                    }
                }
                SpannedExprDefKind::MapLiteral(entries) => {
                    for (_, value) in entries {
                        visit_expr(value, old_name, scopes, out, target_param_id);
                    }
                }
                SpannedExprDefKind::Binding(name, rhs) => {
                    // Binding rhs is evaluated before the name enters scope.
                    visit_expr(rhs, old_name, scopes, out, target_param_id);
                    if let Some(frame) = scopes.last_mut() {
                        frame.insert(name.clone(), BindingOrigin::Other);
                    }
                }
                SpannedExprDefKind::InputDecl(name, param_id, _) => {
                    let origin = if name == old_name && param_id == target_param_id {
                        BindingOrigin::TargetParam
                    } else {
                        BindingOrigin::Other
                    };
                    if let Some(frame) = scopes.last_mut() {
                        frame.insert(name.clone(), origin);
                    }
                }
                SpannedExprDefKind::Block(items) => {
                    scopes.push(std::collections::HashMap::new());
                    for item in items {
                        visit_expr(item, old_name, scopes, out, target_param_id);
                    }
                    let _ = scopes.pop();
                }
                SpannedExprDefKind::Lambda(params, body) => {
                    // Default args are evaluated in outer scope; lambda body has parameter scope.
                    for (_, default) in params {
                        if let Some(expr) = default {
                            visit_expr(expr, old_name, scopes, out, target_param_id);
                        }
                    }
                    scopes.push(std::collections::HashMap::new());
                    if let Some(frame) = scopes.last_mut() {
                        for (param_name, _) in params {
                            frame.insert(param_name.clone(), BindingOrigin::Other);
                        }
                    }
                    visit_expr(body, old_name, scopes, out, target_param_id);
                    let _ = scopes.pop();
                }
                SpannedExprDefKind::LitScalar(_)
                | SpannedExprDefKind::LitWithUnit(_, _)
                | SpannedExprDefKind::LitUnit(_)
                | SpannedExprDefKind::Lit(_)
                | SpannedExprDefKind::LitFuzzyBool(_)
                | SpannedExprDefKind::LitTemporal(_)
                | SpannedExprDefKind::LitDate(_)
                | SpannedExprDefKind::ExternalStream(_) => {}
            }
        }

        let parsed = snaq_lite_lang::parse(source)
            .map_err(|e| tower_lsp::jsonrpc::Error::invalid_params(format!("parse error: {e}")))?;
        let resolved = snaq_lite_lang::resolve::resolve(parsed, unit_registry)
            .map_err(|e| tower_lsp::jsonrpc::Error::invalid_params(format!("resolve error: {e}")))?;
        let mut scopes = vec![std::collections::HashMap::new()];
        let mut out = Vec::new();
        visit_expr(&resolved, old_name, &mut scopes, &mut out, target_param_id);
        Ok(out)
    }

    fn compute_rename_param_source(
        source: &str,
        param_id: &str,
        new_name: &str,
        unit_registry: &snaq_lite_lang::UnitRegistry,
    ) -> tower_lsp::jsonrpc::Result<String> {
        if new_name.trim().is_empty() {
            return Err(tower_lsp::jsonrpc::Error::invalid_params(
                "newName must not be empty",
            ));
        }
        let trimmed_new_name = new_name.trim();
        if !Self::is_valid_identifier(trimmed_new_name) {
            return Err(tower_lsp::jsonrpc::Error::invalid_params(
                "newName must be a valid identifier",
            ));
        }
        let decls = Self::parsed_input_decls(source)?;
        let target = decls.iter().find(|(_, id, _, _)| id == param_id);
        let Some((old_name, found_param_id, ty, span)) = target else {
            return Err(tower_lsp::jsonrpc::Error::invalid_params(
                "paramId not found",
            ));
        };
        let rename_spans = Self::collect_param_symbol_rename_spans(
            source,
            found_param_id,
            old_name,
            unit_registry,
        )?;
        let symbols_updated = Self::replace_identifier_spans(source, &rename_spans, trimmed_new_name);
        let new_decl = format!("input {}@{}: {}", trimmed_new_name, found_param_id, ty);
        Ok(Self::replace_span(&symbols_updated, *span, &new_decl))
    }

    fn compute_add_param_source(
        source: &str,
        param_id: &str,
        name: &str,
        type_name: &str,
    ) -> tower_lsp::jsonrpc::Result<String> {
        let trimmed_name = name.trim();
        let trimmed_param_id = param_id.trim();
        let trimmed_type_name = type_name.trim();
        if trimmed_name.is_empty() || trimmed_param_id.is_empty() || trimmed_type_name.is_empty() {
            return Err(tower_lsp::jsonrpc::Error::invalid_params(
                "name, paramId and typeName must be non-empty",
            ));
        }
        if !Self::is_valid_identifier(trimmed_name) || !Self::is_valid_identifier(trimmed_param_id) {
            return Err(tower_lsp::jsonrpc::Error::invalid_params(
                "name and paramId must be valid identifiers",
            ));
        }
        let decls = Self::parsed_input_decls(source)?;
        for (decl_name, decl_param_id, _, _) in &decls {
            if decl_param_id == trimmed_param_id || decl_name == trimmed_name {
                return Err(tower_lsp::jsonrpc::Error::invalid_params(
                    "duplicate param name or id",
                ));
            }
        }
        let new_line = format!("input {}@{}: {}", trimmed_name, trimmed_param_id, trimmed_type_name);
        let parsed = snaq_lite_lang::parse(source)
            .map_err(|e| tower_lsp::jsonrpc::Error::invalid_params(format!("parse error: {e}")))?;
        let insert_offset = match parsed.value {
            snaq_lite_lang::ir::SpannedExprDefKind::Block(items) => {
                let mut end_of_input_prefix = 0usize;
                let mut saw_non_input = false;
                for item in items {
                    if saw_non_input {
                        break;
                    }
                    match item.value {
                        snaq_lite_lang::ir::SpannedExprDefKind::InputDecl(_, _, _) => {
                            end_of_input_prefix = item.span.end;
                        }
                        _ => saw_non_input = true,
                    }
                }
                end_of_input_prefix
            }
            _ => 0,
        };
        let updated = if insert_offset == 0 {
            if source.is_empty() {
                new_line
            } else {
                format!("{new_line}\n{source}")
            }
        } else {
            let prefix = &source[..insert_offset];
            let suffix = &source[insert_offset..];
            let mut out = String::new();
            out.push_str(prefix);
            if !prefix.ends_with('\n') {
                out.push('\n');
            }
            out.push_str(&new_line);
            if !suffix.is_empty() {
                if !suffix.starts_with('\n') {
                    out.push('\n');
                }
                out.push_str(suffix);
            }
            out
        };
        Ok(updated)
    }

    fn compute_remove_param_source(
        source: &str,
        param_id: &str,
    ) -> tower_lsp::jsonrpc::Result<String> {
        let decls = Self::parsed_input_decls(source)?;
        let target = decls.iter().find(|(_, id, _, _)| id == param_id);
        let Some((_name, _param_id, _ty, span)) = target else {
            return Err(tower_lsp::jsonrpc::Error::invalid_params(
                "paramId not found",
            ));
        };
        Ok(Self::replace_span(source, *span, ""))
    }

    fn input_decls_from_source(
        source: &str,
    ) -> tower_lsp::jsonrpc::Result<Vec<snaq_lite_lang::GraphInputDecl>> {
        let parsed = snaq_lite_lang::parse(source)
            .map_err(|e| tower_lsp::jsonrpc::Error::invalid_params(format!("parse error: {e}")))?;
        let root = parsed.to_expr_def();
        Ok(snaq_lite_lang::extract_input_decls_from_block_with_ids(&root))
    }

    fn reconcile_staged_target_inputs_for_source(
        staged_graph: &mut graph::GraphState,
        uri: &Url,
        source: &str,
    ) -> bool {
        let Ok(inputs) = Self::input_decls_from_source(source) else {
            return false;
        };
        let valid_inputs: std::collections::HashSet<String> =
            inputs.into_iter().map(|decl| decl.param_id).collect();
        !staged_graph
            .reconcile_target_inputs(uri, &valid_inputs)
            .is_empty()
    }

    fn infer_output_type_with_staged_graph(
        staged_graph: &graph::GraphState,
        source_by_uri: &std::collections::HashMap<Url, String>,
        unit_registry: &snaq_lite_lang::UnitRegistry,
        sink_uri: &Url,
    ) -> Option<String> {
        let docs: std::collections::HashSet<Url> = source_by_uri.keys().cloned().collect();
        let order = staged_graph.topological_order(sink_uri, &docs)?;
        let sources: Vec<(Url, String)> = order
            .iter()
            .map(|uri| {
                let source = source_by_uri.get(uri).cloned().unwrap_or_default();
                (uri.clone(), source)
            })
            .collect();
        let incoming_map: std::collections::HashMap<Url, Vec<(String, Url)>> = order
            .iter()
            .map(|uri| (uri.clone(), staged_graph.incoming(uri)))
            .collect();
        let input_name_by_param_id: std::collections::HashMap<
            Url,
            std::collections::HashMap<String, String>,
        > = order
            .iter()
            .map(|uri| {
                let names = source_by_uri
                    .get(uri)
                    .and_then(|source| Self::input_decls_from_source(source).ok())
                    .unwrap_or_default()
                    .into_iter()
                    .map(|decl| (decl.param_id, decl.name))
                    .collect();
                (uri.clone(), names)
            })
            .collect();
        run_node_with_graph_inputs_impl(
            &order,
            &sources,
            unit_registry,
            &incoming_map,
            &input_name_by_param_id,
            sink_uri,
            None,
            None,
        )
        .ok()
        .and_then(|(value, _)| snaq_lite_lang::value_type_name(&value))
    }

    async fn apply_param_source_update(
        &self,
        uri: &Url,
        new_source: String,
    ) -> tower_lsp::jsonrpc::Result<()> {
        let next_version = {
            let mut state = self.state.lock().await;
            let current = state.document_version(uri).unwrap_or(0);
            state.update_document(uri.clone(), current.saturating_add(1), &new_source);
            current.saturating_add(1)
        };
        let _ = next_version;
        self.reconcile_graph_for_uri(uri).await;
        let revalidated_targets = self.revalidate_related_edge_types(uri).await;
        let force_downstream = !revalidated_targets.is_empty();
        let changed_roots = Self::recompute_roots_for_change(uri, revalidated_targets);
        self.recompute_and_push(&changed_roots, force_downstream).await;
        self.drain_notifications().await;
        self.drain_widget_notifications().await;
        self.publish_diagnostics(uri.clone()).await;
        self.send_node_signature_updated(uri).await;
        Ok(())
    }

    pub async fn graph_rename_param(
        &self,
        params: RenameParamParams,
    ) -> tower_lsp::jsonrpc::Result<()> {
        let uri =
            Url::parse(&params.uri).map_err(|_| tower_lsp::jsonrpc::Error::invalid_params("invalid uri"))?;
        self.ensure_graph_canvas_uri_request(&uri).await?;
        let (source, unit_registry) = {
            let state = self.state.lock().await;
            if !state.has_document(&uri) {
                return Err(tower_lsp::jsonrpc::Error::invalid_params("document not open"));
            }
            (state.source(&uri), state.unit_registry().clone())
        };
        let updated = Self::compute_rename_param_source(
            &source,
            &params.param_id,
            &params.new_name,
            &unit_registry,
        )?;
        self.apply_param_source_update(&uri, updated).await
    }

    pub async fn graph_add_param(&self, params: AddParamParams) -> tower_lsp::jsonrpc::Result<()> {
        let uri =
            Url::parse(&params.uri).map_err(|_| tower_lsp::jsonrpc::Error::invalid_params("invalid uri"))?;
        self.ensure_graph_canvas_uri_request(&uri).await?;
        let source = {
            let state = self.state.lock().await;
            if !state.has_document(&uri) {
                return Err(tower_lsp::jsonrpc::Error::invalid_params("document not open"));
            }
            state.source(&uri)
        };
        let updated = Self::compute_add_param_source(
            &source,
            &params.param_id,
            &params.name,
            &params.type_name,
        )?;
        self.apply_param_source_update(&uri, updated).await
    }

    pub async fn graph_remove_param(
        &self,
        params: RemoveParamParams,
    ) -> tower_lsp::jsonrpc::Result<()> {
        let uri =
            Url::parse(&params.uri).map_err(|_| tower_lsp::jsonrpc::Error::invalid_params("invalid uri"))?;
        self.ensure_graph_canvas_uri_request(&uri).await?;
        let source = {
            let state = self.state.lock().await;
            if !state.has_document(&uri) {
                return Err(tower_lsp::jsonrpc::Error::invalid_params("document not open"));
            }
            state.source(&uri)
        };
        let updated = Self::compute_remove_param_source(&source, &params.param_id)?;
        self.apply_param_source_update(&uri, updated).await
    }

    #[allow(clippy::cognitive_complexity)]
    pub async fn graph_apply_patch(
        &self,
        params: ApplyGraphPatchParams,
    ) -> tower_lsp::jsonrpc::Result<ApplyGraphPatchResponse> {
        if params.operations.is_empty() {
            return Ok(ApplyGraphPatchResponse {
                applied_operations: 0,
                affected_uris: Vec::new(),
            });
        }
        let (mut source_by_uri, mut next_version_by_uri, unit_registry) = {
            let state = self.state.lock().await;
            let mut sources = std::collections::HashMap::new();
            let mut versions = std::collections::HashMap::new();
            for (uri, source, version) in state.snapshot_documents() {
                versions.insert(uri.clone(), version.unwrap_or(0));
                sources.insert(uri, source);
            }
            (sources, versions, state.unit_registry().clone())
        };
        let mut staged_graph = {
            let graph = self.graph_state.lock().await;
            let mut g = graph::GraphState::new();
            g.replace_edges(graph.edges_snapshot());
            g
        };
        let mut changed_sources: std::collections::HashSet<Url> = std::collections::HashSet::new();
        let mut topology_targets: std::collections::HashSet<Url> = std::collections::HashSet::new();

        for operation in &params.operations {
            match operation {
                GraphPatchOperation::SetNodeSource { uri, source } => {
                    let uri = Url::parse(uri)
                        .map_err(|_| tower_lsp::jsonrpc::Error::invalid_params("invalid uri"))?;
                    self.ensure_graph_canvas_uri_request(&uri).await?;
                    source_by_uri.insert(uri.clone(), source.clone());
                    changed_sources.insert(uri.clone());
                    next_version_by_uri.entry(uri.clone()).or_insert(0);
                    if Self::reconcile_staged_target_inputs_for_source(
                        &mut staged_graph,
                        &uri,
                        source,
                    ) {
                        topology_targets.insert(uri.clone());
                    }
                }
                GraphPatchOperation::Connect {
                    source_uri,
                    target_uri,
                    target_input_name,
                } => {
                    let source_uri = Url::parse(source_uri).map_err(|_| {
                        tower_lsp::jsonrpc::Error::invalid_params("invalid sourceUri")
                    })?;
                    let target_uri = Url::parse(target_uri).map_err(|_| {
                        tower_lsp::jsonrpc::Error::invalid_params("invalid targetUri")
                    })?;
                    self.ensure_graph_canvas_uri_request(&source_uri).await?;
                    self.ensure_graph_canvas_uri_request(&target_uri).await?;
                    if !source_by_uri.contains_key(&source_uri) || !source_by_uri.contains_key(&target_uri) {
                        return Err(tower_lsp::jsonrpc::Error::invalid_params(
                            "source or target document not open",
                        ));
                    }
                    let target_source = source_by_uri
                        .get(&target_uri)
                        .ok_or_else(|| {
                            tower_lsp::jsonrpc::Error::invalid_params("target document not open")
                        })?;
                    let target_inputs = Self::input_decls_from_source(target_source)?;
                    let target_param_id =
                        Self::resolve_target_input_param_id(&target_inputs, target_input_name)
                            .ok_or_else(|| {
                                tower_lsp::jsonrpc::Error::invalid_params(format!(
                                    "target has no input named or id '{}'",
                                    target_input_name
                                ))
                            })?;
                    let target_input_type = target_inputs
                        .iter()
                        .find(|decl| decl.param_id == target_param_id)
                        .map(|decl| decl.type_name.clone())
                        .ok_or_else(|| {
                            tower_lsp::jsonrpc::Error::invalid_params(format!(
                                "target has no input named or id '{}'",
                                target_input_name
                            ))
                        })?;
                    let docs: std::collections::HashSet<Url> =
                        source_by_uri.keys().cloned().collect();
                    if staged_graph.would_create_cycle(&source_uri, &target_uri, &docs) {
                        return Err(tower_lsp::jsonrpc::Error {
                            code: tower_lsp::jsonrpc::ErrorCode::ServerError(-32002),
                            message: "graph cycle detected".into(),
                            data: None,
                        });
                    }
                    let source_output_type = Self::infer_output_type_with_staged_graph(
                        &staged_graph,
                        &source_by_uri,
                        &unit_registry,
                        &source_uri,
                    );
                    if target_input_type != "Undefined" {
                        if let Some(source_output_type) = source_output_type {
                            if !Self::are_graph_types_compatible(&source_output_type, &target_input_type)
                            {
                                return Err(tower_lsp::jsonrpc::Error {
                                    code: tower_lsp::jsonrpc::ErrorCode::ServerError(-32001),
                                    message: format!(
                                        "Type mismatch: source output type '{}' does not match target input '{}' type '{}'",
                                        source_output_type, target_input_name, target_input_type
                                    )
                                    .into(),
                                    data: None,
                                });
                            }
                        }
                    }
                    staged_graph.connect(source_uri, target_uri.clone(), target_param_id);
                    topology_targets.insert(target_uri);
                }
                GraphPatchOperation::Disconnect {
                    target_uri,
                    target_input_name,
                } => {
                    let target_uri = Url::parse(target_uri).map_err(|_| {
                        tower_lsp::jsonrpc::Error::invalid_params("invalid targetUri")
                    })?;
                    self.ensure_graph_canvas_uri_request(&target_uri).await?;
                    let target_param_id = source_by_uri
                        .get(&target_uri)
                        .and_then(|source| {
                            Self::input_decls_from_source(source).ok().and_then(|decls| {
                                Self::resolve_target_input_param_id(&decls, target_input_name)
                            })
                        })
                        .unwrap_or_else(|| target_input_name.clone());
                    staged_graph.disconnect(&target_uri, &target_param_id);
                    topology_targets.insert(target_uri);
                }
                GraphPatchOperation::RenameParam {
                    uri,
                    param_id,
                    new_name,
                } => {
                    let uri = Url::parse(uri)
                        .map_err(|_| tower_lsp::jsonrpc::Error::invalid_params("invalid uri"))?;
                    self.ensure_graph_canvas_uri_request(&uri).await?;
                    let source = source_by_uri.get(&uri).ok_or_else(|| {
                        tower_lsp::jsonrpc::Error::invalid_params("document not open")
                    })?;
                    let updated = Self::compute_rename_param_source(
                        source,
                        param_id,
                        new_name,
                        &unit_registry,
                    )?;
                    source_by_uri.insert(uri.clone(), updated);
                    changed_sources.insert(uri.clone());
                    next_version_by_uri.entry(uri.clone()).or_insert(0);
                    if let Some(updated_source) = source_by_uri.get(&uri) {
                        if Self::reconcile_staged_target_inputs_for_source(
                            &mut staged_graph,
                            &uri,
                            updated_source,
                        ) {
                            topology_targets.insert(uri.clone());
                        }
                    }
                }
                GraphPatchOperation::AddParam {
                    uri,
                    param_id,
                    name,
                    type_name,
                } => {
                    let uri = Url::parse(uri)
                        .map_err(|_| tower_lsp::jsonrpc::Error::invalid_params("invalid uri"))?;
                    self.ensure_graph_canvas_uri_request(&uri).await?;
                    let source = source_by_uri.get(&uri).ok_or_else(|| {
                        tower_lsp::jsonrpc::Error::invalid_params("document not open")
                    })?;
                    let updated =
                        Self::compute_add_param_source(source, param_id, name, type_name)?;
                    source_by_uri.insert(uri.clone(), updated);
                    changed_sources.insert(uri.clone());
                    next_version_by_uri.entry(uri.clone()).or_insert(0);
                    if let Some(updated_source) = source_by_uri.get(&uri) {
                        if Self::reconcile_staged_target_inputs_for_source(
                            &mut staged_graph,
                            &uri,
                            updated_source,
                        ) {
                            topology_targets.insert(uri.clone());
                        }
                    }
                }
                GraphPatchOperation::RemoveParam { uri, param_id } => {
                    let uri = Url::parse(uri)
                        .map_err(|_| tower_lsp::jsonrpc::Error::invalid_params("invalid uri"))?;
                    self.ensure_graph_canvas_uri_request(&uri).await?;
                    let source = source_by_uri.get(&uri).ok_or_else(|| {
                        tower_lsp::jsonrpc::Error::invalid_params("document not open")
                    })?;
                    let updated = Self::compute_remove_param_source(source, param_id)?;
                    source_by_uri.insert(uri.clone(), updated);
                    changed_sources.insert(uri.clone());
                    next_version_by_uri.entry(uri.clone()).or_insert(0);
                    // Remove known stale edge even when edited source is temporarily invalid.
                    staged_graph.disconnect(&uri, param_id);
                    topology_targets.insert(uri.clone());
                    if let Some(updated_source) = source_by_uri.get(&uri) {
                        if Self::reconcile_staged_target_inputs_for_source(
                            &mut staged_graph,
                            &uri,
                            updated_source,
                        ) {
                            topology_targets.insert(uri.clone());
                        }
                    }
                }
            }
        }

        {
            let mut state = self.state.lock().await;
            for uri in &changed_sources {
                if let Some(new_source) = source_by_uri.get(uri) {
                    let next_version = next_version_by_uri
                        .get(uri)
                        .copied()
                        .unwrap_or(0)
                        .saturating_add(1);
                    state.update_document(uri.clone(), next_version, new_source);
                }
            }
        }
        {
            let mut graph = self.graph_state.lock().await;
            graph.replace_edges(staged_graph.edges_snapshot());
        }

        let mut revalidated_targets: std::collections::HashSet<Url> = std::collections::HashSet::new();
        let mut reconciled_pruned_edges = false;
        for uri in &changed_sources {
            let edges_before = { self.graph_state.lock().await.edges_snapshot().len() };
            self.reconcile_graph_for_uri(uri).await;
            let edges_after = { self.graph_state.lock().await.edges_snapshot().len() };
            if edges_after < edges_before {
                reconciled_pruned_edges = true;
            }
            for target in self.revalidate_related_edge_types(uri).await {
                revalidated_targets.insert(target);
            }
        }

        let mut changed_roots: std::collections::HashSet<Url> = changed_sources.clone();
        let had_topology_targets = !topology_targets.is_empty();
        for target in topology_targets {
            changed_roots.insert(target);
        }
        let had_revalidated_targets = !revalidated_targets.is_empty();
        for target in revalidated_targets {
            changed_roots.insert(target);
        }
        let force_downstream =
            reconciled_pruned_edges || had_topology_targets || had_revalidated_targets;
        let changed_roots_vec: Vec<Url> = changed_roots.iter().cloned().collect();
        self.recompute_and_push(&changed_roots_vec, force_downstream).await;
        self.drain_notifications().await;
        self.drain_widget_notifications().await;
        for uri in &changed_sources {
            self.publish_diagnostics(uri.clone()).await;
            self.send_node_signature_updated(uri).await;
        }

        let mut affected_uris: Vec<String> = changed_roots.into_iter().map(|u| u.to_string()).collect();
        affected_uris.sort();
        affected_uris.dedup();
        Ok(ApplyGraphPatchResponse {
            applied_operations: params.operations.len(),
            affected_uris,
        })
    }

    pub async fn bootstrap_session(
        &self,
        _params: BootstrapSessionParams,
    ) -> tower_lsp::jsonrpc::Result<BootstrapSessionResponse> {
        let (canvas_id, open_documents) = {
            let state = self.state.lock().await;
            (state.active_canvas_id(), state.document_count())
        };
        let subscriptions = self.subscriptions.lock().await.len();
        let widgets = self.widgets.lock().await.len();
        let result_handles = self.result_handles.lock().await.len_handles();
        let runtime_drained =
            open_documents == 0 && subscriptions == 0 && widgets == 0 && result_handles == 0;
        Ok(BootstrapSessionResponse {
            canvas_id,
            open_documents,
            subscriptions,
            widgets,
            result_handles,
            runtime_drained,
        })
    }

    /// Handle snaqlite/graph/resetNamespace: clear graph/runtime state for matching URI prefix.
    pub async fn graph_reset_namespace(
        &self,
        params: ResetNamespaceParams,
    ) -> tower_lsp::jsonrpc::Result<ResetNamespaceResponse> {
        if params.uri_prefix.is_empty() {
            return Err(tower_lsp::jsonrpc::Error::invalid_params(
                "uriPrefix must not be empty",
            ));
        }
        let docs_before = {
            let state = self.state.lock().await;
            state.document_uris()
        };
        let removed_uris: Vec<Url> = docs_before
            .iter()
            .filter(|u| Self::uri_matches_prefix(u.as_str(), &params.uri_prefix))
            .cloned()
            .collect();
        if removed_uris.is_empty() {
            return Ok(ResetNamespaceResponse {
                removed_documents: 0,
            });
        }
        let removed_uri_set: std::collections::HashSet<Url> = removed_uris.iter().cloned().collect();
        let impacted_descendants = {
            let graph = self.graph_state.lock().await;
            let mut impacted = Vec::new();
            let mut seen = std::collections::HashSet::new();
            for uri in &removed_uris {
                for d in graph.descendants_from_source(uri, &docs_before) {
                    if !removed_uri_set.contains(&d) && seen.insert(d.clone()) {
                        impacted.push(d);
                    }
                }
            }
            impacted
        };

        {
            let mut state = self.state.lock().await;
            let _ = state.remove_documents_with_prefix(&params.uri_prefix);
        }
        {
            let mut graph = self.graph_state.lock().await;
            let _ = graph.remove_edges_with_prefix(&params.uri_prefix);
        }
        {
            let mut node_results = self.node_results.lock().await;
            let _ = node_results.remove_with_prefix(&params.uri_prefix);
        }
        {
            let mut handles = self.result_handles.lock().await;
            let _ = handles.remove_with_prefix(&params.uri_prefix);
        }
        let subscription_entries = {
            let mut subs = self.subscriptions.lock().await;
            subs.remove_prefix_all(&params.uri_prefix)
        };
        self.cancel_subscription_entries(subscription_entries, "Namespace reset")
            .await;
        let widget_entries = {
            let mut widgets = self.widgets.lock().await;
            widgets.remove_prefix(&params.uri_prefix)
        };
        self.cancel_widget_entries(widget_entries, "Namespace reset")
            .await;

        for uri in &removed_uris {
            self.client.publish_diagnostics(uri.clone(), Vec::new(), None).await;
        }
        if !impacted_descendants.is_empty() {
            self.recompute_and_push(&impacted_descendants, true).await;
        }
        self.drain_notifications().await;
        self.drain_widget_notifications().await;
        Ok(ResetNamespaceResponse {
            removed_documents: removed_uris.len(),
        })
    }

    /// Export the canonical canvas snapshot (documents + graph edges).
    pub async fn graph_export_canvas_document(
        &self,
        _params: ExportCanvasDocumentParams,
    ) -> tower_lsp::jsonrpc::Result<ExportCanvasDocumentResponse> {
        let (canvas_id, docs, edges) = {
            let state = self.state.lock().await;
            let canvas_id = state.active_canvas_id();
            let docs = state.snapshot_documents();
            let edges = self.graph_state.lock().await.edges_snapshot();
            (canvas_id, docs, edges)
        };
        let model = snaq_lite_lang::CanvasDocument {
            canvas_id,
            nodes: docs
                .into_iter()
                .map(|(uri, source, version)| snaq_lite_lang::CanvasNodeDocument {
                    uri: uri.to_string(),
                    source,
                    version,
                })
                .collect(),
            edges: edges
                .into_iter()
                .map(|e| snaq_lite_lang::CanvasEdge {
                    source_uri: e.source_uri.to_string(),
                    target_uri: e.target_uri.to_string(),
                    target_param_id: e.target_input_name,
                })
                .collect(),
        };
        Ok(ExportCanvasDocumentResponse {
            canvas_document: Self::canvas_payload_from_model(model),
        })
    }

    /// Import a canonical canvas snapshot and rebuild runtime state.
    pub async fn graph_import_canvas_document(
        &self,
        params: ImportCanvasDocumentParams,
    ) -> tower_lsp::jsonrpc::Result<ImportCanvasDocumentResponse> {
        let model = Self::canvas_model_from_payload(params.canvas_document);
        let mut node_entries: Vec<(Url, String, i32)> = Vec::new();
        for (idx, node) in model.nodes.iter().enumerate() {
            let uri = Url::parse(&node.uri)
                .map_err(|_| tower_lsp::jsonrpc::Error::invalid_params("invalid node uri"))?;
            self.ensure_graph_canvas_uri_request(&uri).await?;
            let version = node.version.unwrap_or((idx as i32) + 1);
            node_entries.push((uri, node.source.clone(), version));
        }
        let node_uri_set: std::collections::HashSet<Url> =
            node_entries.iter().map(|(u, _, _)| u.clone()).collect();
        if node_uri_set.len() != node_entries.len() {
            return Err(tower_lsp::jsonrpc::Error::invalid_params(
                "duplicate node uri in canvasDocument",
            ));
        }
        let mut edges = Vec::with_capacity(model.edges.len());
        for edge in &model.edges {
            let source_uri = Url::parse(&edge.source_uri)
                .map_err(|_| tower_lsp::jsonrpc::Error::invalid_params("invalid edge sourceUri"))?;
            let target_uri = Url::parse(&edge.target_uri)
                .map_err(|_| tower_lsp::jsonrpc::Error::invalid_params("invalid edge targetUri"))?;
            if !node_uri_set.contains(&source_uri) || !node_uri_set.contains(&target_uri) {
                return Err(tower_lsp::jsonrpc::Error::invalid_params(
                    "edge uri must refer to an imported node uri",
                ));
            }
            edges.push(graph::GraphEdge {
                source_uri,
                target_uri,
                target_input_name: edge.target_param_id.clone(),
            });
        }

        // Cancel and clear runtime state first to avoid stale streams/subscriptions.
        let subscription_entries = {
            let mut subs = self.subscriptions.lock().await;
            subs.drain_all_entries()
        };
        self.cancel_subscription_entries(subscription_entries, "Canvas import")
            .await;
        let widget_entries = {
            let mut widgets = self.widgets.lock().await;
            widgets.drain_all_entries()
        };
        self.cancel_widget_entries(widget_entries, "Canvas import").await;
        {
            let mut results = self.node_results.lock().await;
            results.clear();
        }
        self.result_handles.lock().await.clear();
        let removed_docs = {
            let mut state = self.state.lock().await;
            state.clear_documents()
        };
        for uri in removed_docs {
            self.client.publish_diagnostics(uri, Vec::new(), None).await;
        }
        {
            let mut graph = self.graph_state.lock().await;
            graph.replace_edges(edges.clone());
        }
        {
            let mut state = self.state.lock().await;
            for (uri, source, version) in &node_entries {
                state.update_document(uri.clone(), *version, source);
            }
        }

        let uris: Vec<Url> = node_entries.iter().map(|(u, _, _)| u.clone()).collect();
        for uri in &uris {
            self.publish_diagnostics(uri.clone()).await;
            self.send_node_signature_updated(uri).await;
        }
        self.recompute_and_push(&uris, true).await;
        self.drain_notifications().await;
        self.drain_widget_notifications().await;
        Ok(ImportCanvasDocumentResponse {
            imported_nodes: node_entries.len(),
            imported_edges: edges.len(),
        })
    }

    /// Build Completed payload with resultType, resultSummary, and display/totalElements.
    fn build_completed_payload(
        value: &snaq_lite_lang::Value,
        db: &salsa::DatabaseImpl,
        result_handle: Option<&str>,
    ) -> serde_json::Value {
        use crate::pubsub::ResultSummary;
        use snaq_lite_lang::map_registry;
        let (result_type, result_summary, display, total_elements) = match value {
            snaq_lite_lang::Value::Vector(v) => {
                // Never force eager draining for summary payloads.
                // Length is only included when already known without consumption.
                let length = match &v.inner {
                    snaq_lite_lang::LazyVector::FromEvaluated(collected) => {
                        Some(collected.len() as u64)
                    }
                    snaq_lite_lang::LazyVector::FromExprs(defs) => Some(defs.len() as u64),
                    snaq_lite_lang::LazyVector::FromExprsWithEnv { defs, .. } => {
                        Some(defs.len() as u64)
                    }
                    _ => None,
                };
                (
                    ResultType::Vector,
                    Some(ResultSummary {
                        length,
                        keys: None,
                        key_count: None,
                    }),
                    None,
                    length,
                )
            }
            snaq_lite_lang::Value::Map(id) => {
                let entries = map_registry::get(*id).unwrap_or_default();
                let key_count = entries.len();
                let keys = if key_count <= 20 {
                    Some(entries.into_iter().map(|(k, _)| k).collect::<Vec<_>>())
                } else {
                    None
                };
                (
                    ResultType::Map,
                    Some(ResultSummary {
                        length: None,
                        keys,
                        key_count: Some(key_count),
                    }),
                    Some("<map>".to_string()),
                    Some(key_count as u64),
                )
            }
            snaq_lite_lang::Value::Undefined => (
                ResultType::Undefined,
                None,
                Some("undefined".to_string()),
                None,
            ),
            _ => {
                let display = snaq_lite_lang::format_value_for_display(db, value)
                    .unwrap_or_else(|_| "<error>".to_string());
                (ResultType::Scalar, None, Some(display), None)
            }
        };
        // json!({ ... }) always produces an object, so as_object_mut() is safe.
        let mut payload = serde_json::json!({
            "resultType": result_type,
        });
        let obj = payload.as_object_mut().expect("json! object");
        if let Some(summary) = result_summary {
            if summary.length.is_some() || summary.keys.is_some() || summary.key_count.is_some() {
                let mut sum = serde_json::json!({});
                if let Some(l) = summary.length {
                    sum["length"] = serde_json::json!(l);
                }
                if let Some(ref k) = summary.keys {
                    sum["keys"] = serde_json::json!(k);
                }
                if let Some(c) = summary.key_count {
                    sum["keyCount"] = serde_json::json!(c);
                }
                obj.insert("resultSummary".to_string(), sum);
            }
        }
        if let Some(d) = display {
            obj.insert("display".to_string(), serde_json::json!(d));
        }
        if let Some(t) = total_elements {
            obj.insert("totalElements".to_string(), serde_json::json!(t));
        }
        if let Some(handle) = result_handle {
            obj.insert("resultHandle".to_string(), serde_json::json!(handle));
        }
        serde_json::Value::Object(obj.clone())
    }

    /// Resolve path segments to a sub-value. Empty path returns Some(value). Returns None if path is invalid.
    fn resolve_path(
        value: &snaq_lite_lang::Value,
        path: &[PathSegment],
        db: &salsa::DatabaseImpl,
    ) -> Option<snaq_lite_lang::Value> {
        use crate::pubsub::PathSegment;
        use snaq_lite_lang::map_registry;
        let mut current = value.clone();
        for segment in path {
            current = match (&current, segment) {
                (snaq_lite_lang::Value::Vector(v), PathSegment::Index(i)) => {
                    let idx = *i as usize;
                    let slice = snaq_lite_lang::LazyVector::Take {
                        source: Box::new(v.inner.clone()),
                        start: idx,
                        length: 1,
                    };
                    use futures::stream::StreamExt;
                    let mut stream = snaq_lite_lang::vector_into_stream(db, slice);
                    match futures::executor::block_on(stream.next()) {
                        Some(Ok(Some(val))) => val,
                        _ => return None,
                    }
                }
                (snaq_lite_lang::Value::Map(id), PathSegment::Key(k)) => {
                    map_registry::get_key(*id, k)?.clone()
                }
                _ => return None,
            };
        }
        Some(current)
    }

    /// Handle snaqlite/graph/subscribeWidget: run source node (with graph inputs when wired), cache result and send Completed with summary.
    pub async fn subscribe_widget(
        &self,
        params: SubscribeWidgetParams,
    ) -> tower_lsp::jsonrpc::Result<()> {
        self.drain_notifications().await;
        self.drain_widget_notifications().await;
        let source_uri = Url::parse(&params.source_uri)
            .map_err(|_| tower_lsp::jsonrpc::Error::invalid_params("invalid sourceUri"))?;
        self.ensure_graph_canvas_uri_request(&source_uri).await?;
        {
            let state = self.state.lock().await;
            if !state.has_document(&source_uri) {
                return Err(tower_lsp::jsonrpc::Error::invalid_params(
                    "source document not open",
                ));
            }
        }
        let external_streams = resolve_external_streams(params.external_streams.as_ref());
        let canvas_id = self.current_canvas_id().await;
        let result = self
            .run_node_with_graph_inputs(&source_uri, external_streams)
            .await;
        match result {
            Err(e) => {
                self.client
                    .send_notification::<WidgetDataUpdateNotification>(WidgetDataUpdateParams {
                        widget_id: params.widget_id.clone(),
                        status: WidgetDataStatus::Error,
                        revision: None,
                        canvas_id: canvas_id.clone(),
                        uri: Some(source_uri.to_string()),
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
                let revision = {
                    let mut store = self.node_results.lock().await;
                    store.upsert_value(source_uri.clone(), value.clone())
                };
                let result_handle = self
                    .upsert_result_handle_for_uri(&source_uri, revision, value.clone())
                    .await;
                let payload = Self::build_completed_payload(&value, &db, Some(&result_handle));
                self.widgets.lock().await.insert_with_cached_value(
                    params.widget_id.clone(),
                    source_uri.clone(),
                    value,
                );
                self.client
                    .send_notification::<WidgetDataUpdateNotification>(WidgetDataUpdateParams {
                        widget_id: params.widget_id,
                        status: WidgetDataStatus::Completed,
                        revision: None,
                        canvas_id: canvas_id.clone(),
                        uri: Some(source_uri.to_string()),
                        payload: Some(payload),
                    })
                    .await;
                Ok(())
            }
        }
    }

    /// Handle snaqlite/graph/fetchResultSlice: return a slice of the result at the given path.
    pub async fn fetch_result_slice(
        &self,
        params: FetchResultSliceParams,
    ) -> tower_lsp::jsonrpc::Result<FetchResultSliceResponse> {
        let (value, source_uri, source_handle, handle_forward_only) =
            if let Some(handle) = params.result_handle.clone() {
            let entry = {
                let handles = self.result_handles.lock().await;
                handles.get(&handle).cloned()
            };
            let entry = entry.ok_or_else(|| {
                tower_lsp::jsonrpc::Error::invalid_params("Result handle not found")
            })?;
            (
                entry.value,
                entry.source_uri,
                Some(handle),
                entry.forward_only,
            )
        } else if let Some(widget_id) = params.widget_id.clone() {
            let (value, source_uri) = {
                let w = self.widgets.lock().await;
                (w.get_cached_value(&widget_id), w.source_uri(&widget_id))
            };
            let value = value.ok_or_else(|| {
                tower_lsp::jsonrpc::Error::invalid_params(
                    "Widget not found or result not available",
                )
            })?;
            let source_uri = source_uri.ok_or_else(|| {
                tower_lsp::jsonrpc::Error::invalid_params(
                    "Widget not found or result not available",
                )
            })?;
            (value, source_uri, None, false)
        } else {
            return Err(tower_lsp::jsonrpc::Error::invalid_params(
                "must provide widgetId or resultHandle",
            ));
        };
        self.ensure_graph_canvas_uri_request(&source_uri).await?;
        if params.limit == 0 {
            return Err(tower_lsp::jsonrpc::Error::invalid_params(
                "limit must be greater than 0",
            ));
        }
        let path_segments: Vec<PathSegment> = params.path;
        if let Some(handle) = source_handle.as_deref() {
            if let Some(cursor) = params.cursor.as_deref() {
                let valid = self
                    .result_handles
                    .lock()
                    .await
                    .validate_and_consume_cursor(
                        cursor,
                        handle,
                        &path_segments,
                        params.offset,
                    );
                if !valid {
                    return Err(tower_lsp::jsonrpc::Error::invalid_params(
                        "invalid or expired cursor",
                    ));
                }
            }
        } else if params.cursor.is_some() {
            return Err(tower_lsp::jsonrpc::Error::invalid_params(
                "cursor requires resultHandle",
            ));
        }
        if source_handle.is_some()
            && !path_segments.is_empty()
            && matches!(
                value,
                snaq_lite_lang::Value::Vector(snaq_lite_lang::VectorValue {
                    inner: snaq_lite_lang::LazyVector::FromInput(_),
                    ..
                })
            )
        {
            return Err(tower_lsp::jsonrpc::Error::invalid_params(
                "non-replayable stream slice does not support nested paths",
            ));
        }
        if source_handle.is_some() && handle_forward_only && params.cursor.is_none() && params.offset > 0 {
            return Err(tower_lsp::jsonrpc::Error::invalid_params(
                "forward-only handle requires cursor for offset > 0",
            ));
        }
        let path_json: Vec<serde_json::Value> = path_segments
            .iter()
            .map(|s| match s {
                PathSegment::Index(i) => serde_json::json!(i),
                PathSegment::Key(k) => serde_json::json!(k),
            })
            .collect();

        let db = {
            let state = self.state.lock().await;
            state.db().clone()
        };
        let (elements, total_count, supports_cursor, explicit_has_more) = {
            let sub_value = Self::resolve_path(&value, &path_segments, &db).ok_or_else(|| {
                tower_lsp::jsonrpc::Error::invalid_params("Invalid path or value not found")
            })?;

            let (elements, total_count, supports_cursor, explicit_has_more) = match &sub_value {
                snaq_lite_lang::Value::Vector(v) => {
                    let non_replayable = matches!(v.inner, snaq_lite_lang::LazyVector::FromInput(_));
                    let offset = params.offset as usize;
                    let limit = params.limit as usize;

                    let (total_count, slice_vec, has_more_override) = match &v.inner {
                        snaq_lite_lang::LazyVector::FromEvaluated(collected) => {
                            let total_count = collected.len() as u64;
                            let start = offset.min(collected.len());
                            let end = (offset + limit).min(collected.len());
                            let slice_vec: Vec<_> = collected[start..end].to_vec();
                            (total_count, slice_vec, None)
                        }
                        snaq_lite_lang::LazyVector::FromInput(_) if source_handle.is_some() => {
                            let handle = source_handle
                                .as_deref()
                                .expect("checked source_handle.is_some()");
                            let page = self
                                .result_handles
                                .lock()
                                .await
                                .read_forward_only_page(handle, params.offset, limit)
                                .map_err(tower_lsp::jsonrpc::Error::invalid_params)?;
                            (page.total_count, page.items, Some(page.has_more))
                        }
                        _ => {
                            // Stream once to compute both total count and requested window.
                            let (total_count, slice_vec) = collect_vector_slice_window(
                                &db,
                                v.inner.clone(),
                                offset,
                                limit,
                            );
                            (total_count, slice_vec, None)
                        }
                    };

                    let elements: Vec<serde_json::Value> = slice_vec
                        .into_iter()
                        .enumerate()
                        .map(|(i, item)| match &item {
                            Ok(Some(val)) => {
                                let mut elem_path = path_json.clone();
                                elem_path.push(serde_json::json!((offset + i) as u64));
                                crate::pubsub::value_to_slice_element(&db, val, &elem_path)
                            }
                            Ok(None) => serde_json::Value::Null,
                            Err(e) => serde_json::json!({
                                "kind": "error",
                                "message": e.to_string()
                            }),
                        })
                        .collect();
                    let supports_cursor = !non_replayable || source_handle.is_some();
                    (elements, total_count, supports_cursor, has_more_override)
                }
                snaq_lite_lang::Value::Map(id) => {
                    use snaq_lite_lang::map_registry;
                    let entries = map_registry::get(*id).unwrap_or_default();
                    let total_count = entries.len() as u64;
                    let offset = (params.offset as usize).min(entries.len());
                    let end = (offset + params.limit as usize).min(entries.len());
                    let slice_entries = &entries[offset..end];
                    let elements: Vec<serde_json::Value> = slice_entries
                        .iter()
                        .map(|(k, val)| {
                            let mut elem_path = path_json.clone();
                            elem_path.push(serde_json::json!(k));
                            serde_json::json!({
                                "key": k,
                                "value": crate::pubsub::value_to_slice_element(&db, val, &elem_path)
                            })
                        })
                        .collect();
                    (elements, total_count, true, None)
                }
                _ => {
                    return Err(tower_lsp::jsonrpc::Error::invalid_params(
                        "Path does not refer to a vector or map",
                    ));
                }
            };
            (elements, total_count, supports_cursor, explicit_has_more)
        };

        let has_more = explicit_has_more
            .unwrap_or_else(|| params.offset + (elements.len() as u64) < total_count);
        let next_cursor = if has_more && supports_cursor {
            if let Some(handle) = source_handle.as_deref() {
                Some(
                    self.result_handles
                        .lock()
                        .await
                        .issue_cursor(handle, &path_segments, params.offset + elements.len() as u64),
                )
            } else {
                None
            }
        } else {
            None
        };
        Ok(FetchResultSliceResponse {
            elements,
            total_count,
            has_more,
            next_cursor,
        })
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
            let canvas_id = self.current_canvas_id().await;
            self.client
                .send_notification::<WidgetDataUpdateNotification>(WidgetDataUpdateParams {
                    widget_id: params.widget_id,
                    status: WidgetDataStatus::Cancelled,
                    revision: None,
                    canvas_id,
                    uri: None,
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
    ) -> Result<(snaq_lite_lang::Value, salsa::DatabaseImpl), snaq_lite_lang::RunError> {
        self.run_node_with_graph_inputs_cached(
            sink_uri,
            external_streams,
            &mut std::collections::HashMap::new(),
        )
        .await
    }

    async fn run_node_with_graph_inputs_cached(
        &self,
        sink_uri: &Url,
        external_streams: Option<std::collections::HashMap<String, snaq_lite_lang::StreamHandleId>>,
        shared_cache: &mut std::collections::HashMap<Url, (snaq_lite_lang::Value, salsa::DatabaseImpl)>,
    ) -> Result<(snaq_lite_lang::Value, salsa::DatabaseImpl), snaq_lite_lang::RunError> {
        let (order, projections, unit_registry) = {
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
            let projections: Vec<WiredNodeProjection> = order
                .iter()
                .map(|u| {
                    let mut incoming = graph.incoming(u);
                    incoming.sort_by(|(left_param, left_source), (right_param, right_source)| {
                        left_param
                            .cmp(right_param)
                            .then_with(|| left_source.as_str().cmp(right_source.as_str()))
                    });
                    let input_name_by_param_id: std::collections::HashMap<String, String> = state
                        .get_document(u)
                        .and_then(|d| d.root_def.as_ref())
                        .map(snaq_lite_lang::extract_input_decls_from_block_with_ids)
                        .unwrap_or_default()
                        .into_iter()
                        .map(|decl| (decl.param_id, decl.name))
                        .collect();
                    WiredNodeProjection {
                        uri: u.clone(),
                        source: state.source(u),
                        incoming_by_param_id: incoming,
                        input_name_by_param_id,
                    }
                })
                .collect();
            (order, projections, state.unit_registry().clone())
        };
        let sources: Vec<(Url, String)> = projections
            .iter()
            .map(|p| (p.uri.clone(), p.source.clone()))
            .collect();
        let incoming_map: std::collections::HashMap<Url, Vec<(String, Url)>> = projections
            .iter()
            .map(|p| (p.uri.clone(), p.incoming_by_param_id.clone()))
            .collect();
        let input_name_by_param_id: std::collections::HashMap<
            Url,
            std::collections::HashMap<String, String>,
        > = projections
            .iter()
            .map(|p| (p.uri.clone(), p.input_name_by_param_id.clone()))
            .collect();
        run_node_with_graph_inputs_impl(
            &order,
            &sources,
            &unit_registry,
            &incoming_map,
            &input_name_by_param_id,
            sink_uri,
            external_streams.as_ref(),
            Some(shared_cache),
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
#[allow(clippy::too_many_arguments)]
fn run_node_with_graph_inputs_impl(
    order: &[Url],
    sources: &[(Url, String)],
    unit_registry: &snaq_lite_lang::UnitRegistry,
    incoming_map: &std::collections::HashMap<Url, Vec<(String, Url)>>,
    input_name_by_param_id: &std::collections::HashMap<Url, std::collections::HashMap<String, String>>,
    sink_uri: &Url,
    external_streams: Option<&std::collections::HashMap<String, snaq_lite_lang::StreamHandleId>>,
    mut shared_cache: Option<&mut std::collections::HashMap<Url, (snaq_lite_lang::Value, salsa::DatabaseImpl)>>,
) -> Result<(snaq_lite_lang::Value, salsa::DatabaseImpl), snaq_lite_lang::RunError> {
    let mut output_values: std::collections::HashMap<
        Url,
        (snaq_lite_lang::Value, salsa::DatabaseImpl),
    > = std::collections::HashMap::new();
    let mut last_value = None;
    let mut last_db = None;
    for (uri, source_entry) in order.iter().zip(sources.iter()) {
        if let Some(cache) = shared_cache.as_deref_mut() {
            if let Some((value, db)) = cache.get(uri).cloned() {
                if uri == sink_uri {
                    last_value = Some(value.clone());
                    last_db = Some(db.clone());
                }
                if uri != sink_uri {
                    output_values.insert(uri.clone(), (value, db));
                }
                continue;
            }
        }
        let source = &source_entry.1;
        let incoming = incoming_map.get(uri).map(|i| i.as_slice()).unwrap_or(&[]);
        let param_name_lookup = input_name_by_param_id.get(uri);
        let is_sink = uri == sink_uri;
        let mut stream_inputs: std::collections::HashMap<String, snaq_lite_lang::StreamHandleId> =
            if is_sink {
                external_streams.cloned().unwrap_or_default()
            } else {
                std::collections::HashMap::new()
            };
        let mut senders_by_source: std::collections::HashMap<
            Url,
            Vec<snaq_lite_lang::StreamChunkSender>,
        > = std::collections::HashMap::new();
        for (target_param_id, source_uri) in incoming {
            let name = param_name_lookup
                .and_then(|m| m.get(target_param_id))
                .cloned()
                .unwrap_or_else(|| target_param_id.clone());
            if stream_inputs.contains_key(&name) {
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
        if let Some(cache) = shared_cache.as_deref_mut() {
            cache.insert(uri.clone(), (value.clone(), db.clone()));
        }
        if uri == sink_uri {
            last_value = Some(value.clone());
            last_db = Some(db.clone());
        }
        if uri != sink_uri {
            output_values.insert(uri.clone(), (value, db));
        }
    }
    let (value, db) = match (last_value, last_db) {
        (Some(v), Some(d)) => (v, d),
        _ => {
            return Err(snaq_lite_lang::RunError::new(
                snaq_lite_lang::RunErrorKind::InvalidArgument(
                    "graph order did not contain sink node".to_string(),
                ),
            ))
        }
    };
    Ok((value, db))
}

fn collect_vector_slice_window(
    db: &salsa::DatabaseImpl,
    inner: snaq_lite_lang::LazyVector,
    offset: usize,
    limit: usize,
) -> (
    u64,
    Vec<Result<Option<snaq_lite_lang::Value>, snaq_lite_lang::RunError>>,
) {
    use futures::stream::StreamExt;
    let mut stream = snaq_lite_lang::vector_into_stream(db, inner);
    futures::executor::block_on(async move {
        let mut total = 0u64;
        let mut out: Vec<Result<Option<snaq_lite_lang::Value>, snaq_lite_lang::RunError>> =
            Vec::with_capacity(limit);
        let end = offset.saturating_add(limit);
        while let Some(item) = stream.next().await {
            let idx = total as usize;
            if idx >= offset && idx < end {
                out.push(item);
            }
            total += 1;
        }
        (total, out)
    })
}

fn run_local_future<F>(future: F) -> F::Output
where
    F: futures::Future,
{
    let mut pool = futures::executor::LocalPool::new();
    pool.run_until(future)
}

#[cfg(not(target_arch = "wasm32"))]
fn send_batch_native(
    senders: &mut [snaq_lite_lang::StreamChunkSender],
    mut batch: Vec<Result<Option<snaq_lite_lang::Value>, snaq_lite_lang::RunError>>,
) {
    use futures::sink::SinkExt;
    if senders.is_empty() {
        return;
    }
    let last_idx = senders.len().saturating_sub(1);
    for (idx, sender) in senders.iter_mut().enumerate() {
        if idx == last_idx {
            let payload = std::mem::take(&mut batch);
            let _ = run_local_future(sender.send(payload));
        } else {
            let _ = run_local_future(sender.send(batch.clone()));
        }
    }
}

/// Feed one upstream value to multiple Chunk senders (one handle per edge when one source feeds multiple inputs).
/// Uses bounded send (block_on on native, spawn_local on WASM) for back-pressure.
fn feed_value_to_senders(
    value: &snaq_lite_lang::Value,
    db: &salsa::DatabaseImpl,
    senders: Vec<snaq_lite_lang::StreamChunkSender>,
) {
    use futures::sink::SinkExt;

    match value {
        snaq_lite_lang::Value::Vector(v) => {
            #[cfg(not(target_arch = "wasm32"))]
            {
                use futures::stream::StreamExt;
                const FANOUT_CHUNK_SIZE: usize = 128;
                let mut senders = senders;
                let mut stream = snaq_lite_lang::vector_into_stream(db, v.inner.clone());
                let mut batch: Vec<Result<Option<snaq_lite_lang::Value>, snaq_lite_lang::RunError>> =
                    Vec::with_capacity(FANOUT_CHUNK_SIZE);
                loop {
                    let next = run_local_future(stream.next());
                    match next {
                        Some(item) => {
                            batch.push(item);
                            if batch.len() >= FANOUT_CHUNK_SIZE {
                                send_batch_native(&mut senders, std::mem::take(&mut batch));
                            }
                        }
                        None => break,
                    }
                }
                if !batch.is_empty() {
                    send_batch_native(&mut senders, batch);
                }
            }
            #[cfg(target_arch = "wasm32")]
            {
                const FANOUT_CHUNK_SIZE: usize = 128;
                for mut sender in senders {
                    let db_for_stream = db.clone();
                    let inner = v.inner.clone();
                    wasm_bindgen_futures::spawn_local(async move {
                        use futures::sink::SinkExt;
                        use futures::stream::StreamExt;

                        let mut stream = snaq_lite_lang::vector_into_stream(&db_for_stream, inner);
                        let mut batch: Vec<
                            Result<Option<snaq_lite_lang::Value>, snaq_lite_lang::RunError>,
                        > = Vec::with_capacity(FANOUT_CHUNK_SIZE);
                        while let Some(item) = stream.next().await {
                            batch.push(item);
                            if batch.len() >= FANOUT_CHUNK_SIZE {
                                if sender.send(std::mem::take(&mut batch)).await.is_err() {
                                    return;
                                }
                            }
                        }
                        if !batch.is_empty() {
                            let _ = sender.send(batch).await;
                        }
                    });
                }
            }
        }
        _ => {
            let chunk = vec![Ok(Some(value.clone()))];
            for mut sender in senders {
                #[cfg(not(target_arch = "wasm32"))]
                {
                    let _ = run_local_future(sender.send(chunk.clone()));
                }
                #[cfg(target_arch = "wasm32")]
                {
                    let c = chunk.clone();
                    wasm_bindgen_futures::spawn_local(async move {
                        let _ = sender.send(c).await;
                    });
                }
            }
        }
    }
}

/// Native: run the stream in a blocking thread and send batches via notification_tx.
/// Creates the stream inside the async block so it borrows db correctly.
/// Exits on stream end (sends Completed) or when cancel_rx fires (no final notification).
#[cfg(not(target_arch = "wasm32"))]
#[allow(clippy::too_many_arguments)]
fn run_stream_consumer(
    db: salsa::DatabaseImpl,
    inner: snaq_lite_lang::LazyVector,
    subscription_id: String,
    revision: Option<u64>,
    canvas_id: Option<String>,
    uri: Option<String>,
    result_handle: Option<String>,
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
                                let data = if let Some(handle) = &result_handle {
                                    serde_json::json!({
                                        "elements": batch.clone(),
                                        "offset": offset,
                                        "count": batch.len(),
                                        "resultHandle": handle
                                    })
                                } else {
                                    serde_json::json!({
                                    "elements": batch.clone(),
                                    "offset": offset,
                                    "count": batch.len()
                                    })
                                };
                                let _ = notification_tx.unbounded_send((
                                    subscription_id.clone(),
                                    PublishResultParams {
                                        subscription_id: subscription_id.clone(),
                                        status: PublishStatus::Running,
                                        revision,
                                        canvas_id: canvas_id.clone(),
                                        uri: uri.clone(),
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
            let data = if let Some(handle) = &result_handle {
                serde_json::json!({
                    "elements": batch,
                    "offset": offset,
                    "count": batch.len(),
                    "resultHandle": handle
                })
            } else {
                serde_json::json!({
                    "elements": batch,
                    "offset": offset,
                    "count": batch.len()
                })
            };
            let _ = notification_tx.unbounded_send((
                subscription_id.clone(),
                PublishResultParams {
                    subscription_id: subscription_id.clone(),
                    status: PublishStatus::Running,
                    revision,
                    canvas_id: canvas_id.clone(),
                    uri: uri.clone(),
                    data: Some(data),
                },
            ));
        }
        let sid = subscription_id.clone();
        let completed_data = if let Some(handle) = result_handle {
            serde_json::json!({ "totalElements": total, "resultHandle": handle })
        } else {
            serde_json::json!({ "totalElements": total })
        };
        let _ = notification_tx.unbounded_send((
            subscription_id,
            PublishResultParams {
                subscription_id: sid,
                status: PublishStatus::Completed,
                revision,
                canvas_id,
                uri,
                data: Some(completed_data),
            },
        ));
    };
    let mut pool = futures::executor::LocalPool::new();
    let spawner = pool.spawner();
    spawner.spawn_local(run).ok();
    pool.run();
}

/// Native: run the stream for a widget and send WidgetDataUpdate notifications.
/// Kept for potential backward compatibility; current flow uses cached value + fetchResultSlice.
#[cfg(not(target_arch = "wasm32"))]
#[allow(dead_code)]
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
                                single_display = json
                                    .get("display")
                                    .and_then(|v| v.as_str())
                                    .map(String::from);
                            }
                            batch.push(json);
                            total += 1;
                            if batch.len() >= BATCH_SIZE {
                                let _ = widget_tx.unbounded_send(WidgetDataUpdateParams {
                                    widget_id: widget_id.clone(),
                                    status: WidgetDataStatus::Running,
                                    revision: None,
                                    canvas_id: None,
                                    uri: None,
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
                revision: None,
                canvas_id: None,
                uri: None,
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
            revision: None,
            canvas_id: None,
            uri: None,
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
    let node_results: SharedNodeResults = Arc::new(Mutex::new(NodeResultRegistry::new()));
    let run_cache: SharedRunCache = Arc::new(Mutex::new(std::collections::HashMap::new()));
    let result_handles: SharedResultHandles = Arc::new(Mutex::new(ResultHandleRegistry::new()));
    let (notification_tx, notification_rx) = futures::channel::mpsc::unbounded();
    let (widget_notification_tx, widget_notification_rx) = futures::channel::mpsc::unbounded();
    let (service, socket) = LspService::build(move |client| SnaqLiteBackend {
        client,
        state: Arc::clone(&state),
        subscriptions: Arc::clone(&subscriptions),
        graph_state: Arc::clone(&graph_state),
        widgets: Arc::clone(&widgets),
        node_results: Arc::clone(&node_results),
        notification_tx,
        notification_rx: Arc::new(Mutex::new(notification_rx)),
        widget_notification_tx,
        widget_notification_rx: Arc::new(Mutex::new(widget_notification_rx)),
        run_cache: Arc::clone(&run_cache),
        result_handles: Arc::clone(&result_handles),
    })
    .custom_method("snaqlite/subscribe", SnaqLiteBackend::subscribe)
    .custom_method("snaqlite/subscribeNode", SnaqLiteBackend::subscribe_node)
    .custom_method("snaqlite/unsubscribe", SnaqLiteBackend::unsubscribe)
    .custom_method("snaqlite/unsubscribeNode", SnaqLiteBackend::unsubscribe_node)
    .custom_method("snaqlite/graph/connect", SnaqLiteBackend::graph_connect)
    .custom_method(
        "snaqlite/graph/disconnect",
        SnaqLiteBackend::graph_disconnect,
    )
    .custom_method(
        "snaqlite/graph/renameParam",
        SnaqLiteBackend::graph_rename_param,
    )
    .custom_method(
        "snaqlite/graph/addParam",
        SnaqLiteBackend::graph_add_param,
    )
    .custom_method(
        "snaqlite/graph/removeParam",
        SnaqLiteBackend::graph_remove_param,
    )
    .custom_method(
        "snaqlite/graph/resetNamespace",
        SnaqLiteBackend::graph_reset_namespace,
    )
    .custom_method(
        "snaqlite/graph/exportCanvasDocument",
        SnaqLiteBackend::graph_export_canvas_document,
    )
    .custom_method(
        "snaqlite/graph/importCanvasDocument",
        SnaqLiteBackend::graph_import_canvas_document,
    )
    .custom_method(
        "snaqlite/graph/subscribeWidget",
        SnaqLiteBackend::subscribe_widget,
    )
    .custom_method(
        "snaqlite/graph/unsubscribeWidget",
        SnaqLiteBackend::unsubscribe_widget,
    )
    .custom_method(
        "snaqlite/graph/fetchResultSlice",
        SnaqLiteBackend::fetch_result_slice,
    )
    .custom_method(
        "snaqlite/graph/applyPatch",
        SnaqLiteBackend::graph_apply_patch,
    )
    .custom_method(
        "snaqlite/bootstrapSession",
        SnaqLiteBackend::bootstrap_session,
    )
    .finish();
    (service, socket)
}

/// Run the LSP server with the given stdin and stdout (native).
#[cfg(not(target_arch = "wasm32"))]
pub async fn run_native<I, O>(
    stdin: I,
    stdout: O,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>>
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
        let range = span_to_range(&snaq_lite_lang::Span { start: 2, end: 5 }, source);
        assert_eq!(range.start.line, 0);
        assert_eq!(range.start.character, 2);
        assert_eq!(range.end.line, 0);
        assert_eq!(range.end.character, 5);
    }

    #[test]
    fn span_to_range_multiline_second_line() {
        let source = "a\nbc\nd";
        // span 3..5: starts on second line and ends at start of third line
        let range = span_to_range(&snaq_lite_lang::Span { start: 3, end: 5 }, source);
        assert_eq!(range.start.line, 1);
        assert_eq!(range.end.line, 2);
        assert_eq!(range.end.character, 0);
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
        assert_eq!(
            d.severity,
            Some(tower_lsp::lsp_types::DiagnosticSeverity::ERROR)
        );
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
        assert_eq!(
            d.severity,
            Some(tower_lsp::lsp_types::DiagnosticSeverity::ERROR)
        );
    }

    #[test]
    fn fallback_range_spans_first_line() {
        use crate::mapping::fallback_range;
        let r = fallback_range("anything");
        assert_eq!(r.start.line, 0);
        assert_eq!(r.start.character, 0);
        assert_eq!(r.end.line, 0);
        assert_eq!(r.end.character, 8, "first line \"anything\" has 8 chars");
    }

    #[test]
    fn fallback_range_empty_source_uses_min_length_one() {
        use crate::mapping::fallback_range;
        let r = fallback_range("");
        assert_eq!(r.start.line, 0);
        assert_eq!(r.start.character, 0);
        assert_eq!(r.end.line, 0);
        assert_eq!(r.end.character, 1);
    }

    #[test]
    fn fallback_range_multiline_uses_first_line_only() {
        use crate::mapping::fallback_range;
        let r = fallback_range("line1\nline2\nline3");
        assert_eq!(r.start.line, 0);
        assert_eq!(r.start.character, 0);
        assert_eq!(r.end.line, 0);
        assert_eq!(r.end.character, 5);
    }

    #[test]
    fn run_error_without_span_falls_back_to_first_line_range() {
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
        // Fallback range spans the first line so the user sees an error decoration (end = first line length)
        assert_eq!(d.range.end.character, 8);
    }

    #[test]
    fn run_node_with_graph_inputs_impl_empty_order_returns_invalid_argument() {
        // When order does not contain sink_uri, impl returns Err instead of panicking (WASM-safe).
        let order: &[Url] = &[];
        let sources: &[(Url, String)] = &[];
        let unit_registry = snaq_lite_lang::default_si_registry();
        let incoming_map = std::collections::HashMap::new();
        let input_name_by_param_id = std::collections::HashMap::new();
        let sink_uri = Url::parse("snaq://graph/sink.sl").unwrap();
        let result = run_node_with_graph_inputs_impl(
            order,
            sources,
            &unit_registry,
            &incoming_map,
            &input_name_by_param_id,
            &sink_uri,
            None,
            None,
        );
        match result {
            Err(e) => assert!(
                matches!(e.kind, snaq_lite_lang::RunErrorKind::InvalidArgument(ref msg) if msg.contains("graph order did not contain sink")),
                "expected InvalidArgument about sink, got {:?}",
                e.kind
            ),
            Ok(_) => panic!("expected Err(InvalidArgument), got Ok"),
        }
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
        assert_eq!(
            diags[0].severity,
            Some(tower_lsp::lsp_types::DiagnosticSeverity::ERROR)
        );
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
        reg.insert("sub-1".to_string(), uri.clone(), Some(1), Some(tx));
        let removed = reg.remove("sub-1");
        assert!(removed.is_some_and(|x| x.is_some()));
        assert!(reg.remove("sub-1").is_none());
    }

    #[test]
    fn subscription_registry_invalidate_uri() {
        let mut reg = subscription::SubscriptionRegistry::new();
        let uri = Url::parse("file:///doc.snaq").unwrap();
        let other = Url::parse("file:///other.snaq").unwrap();
        let (tx1, _rx1) = futures::channel::oneshot::channel();
        let (tx2, _rx2) = futures::channel::oneshot::channel();
        reg.insert("sub-a".to_string(), uri.clone(), Some(1), Some(tx1));
        reg.insert("sub-b".to_string(), other, Some(1), Some(tx2));
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
        assert!(obj
            .get("message")
            .and_then(|v| v.as_str())
            .unwrap_or("")
            .contains("division"));
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
        assert!(
            display.contains("3"),
            "display should show result: {}",
            display
        );
    }

    #[test]
    fn wasm_progress_guard_skips_from_input_vectors() {
        let (handle_id, _sender) = snaq_lite_lang::create_stream_input();
        let from_input = snaq_lite_lang::LazyVector::FromInput(handle_id);
        let replayable = snaq_lite_lang::LazyVector::FromEvaluated(vec![]);
        assert!(
            !SnaqLiteBackend::should_stream_wasm_vector_progress(&from_input),
            "FromInput must be excluded to preserve handle receiver for fetchResultSlice"
        );
        assert!(
            SnaqLiteBackend::should_stream_wasm_vector_progress(&replayable),
            "Replayable vectors should still support progress streaming"
        );
    }

    #[cfg(not(target_arch = "wasm32"))]
    #[test]
    fn run_stream_consumer_propagates_metadata_fields() {
        use futures::stream::StreamExt;
        let (value, db) = snaq_lite_lang::run_with_stream_inputs(
            "[1, 2, 3]",
            &snaq_lite_lang::default_si_registry(),
            std::collections::HashMap::new(),
        )
        .expect("vector run");
        let snaq_lite_lang::Value::Vector(v) = value else {
            panic!("expected vector value");
        };
        let (tx, mut rx) = futures::channel::mpsc::unbounded::<(String, PublishResultParams)>();
        let (_cancel_tx, cancel_rx) = futures::channel::oneshot::channel::<()>();
        run_stream_consumer(
            db,
            v.inner,
            "sub-1".to_string(),
            Some(7),
            Some("canvas-a".to_string()),
            Some("snaq://canvas-a/node.sl".to_string()),
            Some("handle-1".to_string()),
            tx,
            cancel_rx,
        );

        let messages = run_local_future(async move {
            let mut out = Vec::new();
            while let Some((_, params)) = rx.next().await {
                let is_completed = matches!(params.status, PublishStatus::Completed);
                out.push(params);
                if is_completed {
                    break;
                }
            }
            out
        });
        assert!(!messages.is_empty(), "stream consumer should emit notifications");
        for params in &messages {
            assert_eq!(params.revision, Some(7));
            assert_eq!(params.canvas_id.as_deref(), Some("canvas-a"));
            assert_eq!(params.uri.as_deref(), Some("snaq://canvas-a/node.sl"));
            if let Some(data) = &params.data {
                assert_eq!(data["resultHandle"].as_str(), Some("handle-1"));
            }
        }
        let completed = messages
            .iter()
            .find(|p| matches!(p.status, PublishStatus::Completed))
            .expect("completed payload");
        let completed_data = completed.data.as_ref().expect("completed data");
        assert!(
            completed_data.get("display").is_none(),
            "vector completion payload must not include eager display"
        );
        assert!(
            completed_data.get("totalElements").is_some(),
            "vector completion payload should include element count"
        );
    }

    #[test]
    fn build_completed_payload_vector_is_summary_only_with_handle() {
        let (value, db) = snaq_lite_lang::run_with_stream_inputs(
            "[1, 2, 3]",
            &snaq_lite_lang::default_si_registry(),
            std::collections::HashMap::new(),
        )
        .expect("vector run");
        let payload = SnaqLiteBackend::build_completed_payload(&value, &db, Some("handle-xyz"));
        assert_eq!(payload["resultType"].as_str(), Some("Vector"));
        assert_eq!(payload["resultHandle"].as_str(), Some("handle-xyz"));
        assert!(
            payload.get("display").is_none(),
            "vector completed payload should not eagerly include display"
        );
        assert!(
            payload.get("resultSummary").is_some() || payload.get("totalElements").is_some(),
            "vector payload should include summary metadata when available"
        );
    }

    #[test]
    fn subscription_registry_invalidate_all() {
        let mut reg = subscription::SubscriptionRegistry::new();
        let uri = Url::parse("file:///doc.snaq").unwrap();
        let (tx1, _rx1) = futures::channel::oneshot::channel();
        let (tx2, _rx2) = futures::channel::oneshot::channel();
        reg.insert("sub-1".to_string(), uri.clone(), Some(1), Some(tx1));
        reg.insert("sub-2".to_string(), uri, Some(1), Some(tx2));
        let cancelled = reg.invalidate_all();
        assert_eq!(cancelled.len(), 2);
        let ids: std::collections::HashSet<_> =
            cancelled.iter().map(|(id, _)| id.as_str()).collect();
        assert!(ids.contains("sub-1"));
        assert!(ids.contains("sub-2"));
        assert!(reg.remove("sub-1").is_none());
        assert!(reg.remove("sub-2").is_none());
    }

    #[test]
    fn subscription_registry_drain_all_entries_includes_scalar_and_streaming() {
        let mut reg = subscription::SubscriptionRegistry::new();
        let uri = Url::parse("file:///doc.snaq").unwrap();
        let (tx, _rx) = futures::channel::oneshot::channel();
        reg.insert("sub-stream".to_string(), uri.clone(), Some(1), Some(tx));
        reg.insert("sub-scalar".to_string(), uri, Some(1), None);
        let drained = reg.drain_all_entries();
        assert_eq!(drained.len(), 2);
        assert!(drained.iter().any(|(id, tx)| id == "sub-stream" && tx.is_some()));
        assert!(drained.iter().any(|(id, tx)| id == "sub-scalar" && tx.is_none()));
        assert!(reg.remove("sub-stream").is_none());
        assert!(reg.remove("sub-scalar").is_none());
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
    fn resolve_target_input_param_id_matches_name_or_param_id() {
        let decls = vec![snaq_lite_lang::GraphInputDecl {
            name: "revenue".to_string(),
            param_id: "p1".to_string(),
            type_name: "Vector".to_string(),
        }];
        assert_eq!(
            SnaqLiteBackend::resolve_target_input_param_id(&decls, "revenue"),
            Some("p1".to_string())
        );
        assert_eq!(
            SnaqLiteBackend::resolve_target_input_param_id(&decls, "p1"),
            Some("p1".to_string())
        );
        assert_eq!(
            SnaqLiteBackend::resolve_target_input_param_id(&decls, "missing"),
            None
        );
    }

    #[test]
    fn resolve_target_input_param_id_prefers_param_id_on_collision() {
        let decls = vec![
            snaq_lite_lang::GraphInputDecl {
                name: "a".to_string(),
                param_id: "x".to_string(),
                type_name: "Vector".to_string(),
            },
            snaq_lite_lang::GraphInputDecl {
                name: "x".to_string(),
                param_id: "y".to_string(),
                type_name: "Vector".to_string(),
            },
        ];
        assert_eq!(
            SnaqLiteBackend::resolve_target_input_param_id(&decls, "x"),
            Some("x".to_string())
        );
    }

    #[test]
    fn graph_type_compatibility_matrix() {
        assert!(SnaqLiteBackend::are_graph_types_compatible("Numeric", "Numeric"));
        assert!(SnaqLiteBackend::are_graph_types_compatible("Vector", "Undefined"));
        assert!(SnaqLiteBackend::are_graph_types_compatible("Numeric", "Symbolic"));
        assert!(SnaqLiteBackend::are_graph_types_compatible("FuzzyBool", "Symbolic"));
        assert!(!SnaqLiteBackend::are_graph_types_compatible("Vector", "Numeric"));
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
        let docs: std::collections::HashSet<_> =
            [a.clone(), b.clone(), c.clone()].into_iter().collect();
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

    #[test]
    fn impacted_from_changed_nodes_returns_full_closure() {
        let mut graph = graph::GraphState::new();
        let a = Url::parse("snaq://graph/a.sl").unwrap();
        let b = Url::parse("snaq://graph/b.sl").unwrap();
        let c = Url::parse("snaq://graph/c.sl").unwrap();
        let d = Url::parse("snaq://graph/d.sl").unwrap();
        graph.connect(a.clone(), b.clone(), "x".to_string());
        graph.connect(b.clone(), c.clone(), "x".to_string());
        graph.connect(a.clone(), d.clone(), "x".to_string());
        let docs: std::collections::HashSet<_> =
            [a.clone(), b.clone(), c.clone(), d.clone()].into_iter().collect();
        let impacted = graph.impacted_from_changed_nodes(std::slice::from_ref(&a), &docs);
        assert_eq!(impacted.len(), 4);
        assert!(impacted.contains(&a));
        assert!(impacted.contains(&b));
        assert!(impacted.contains(&c));
        assert!(impacted.contains(&d));
    }

    #[test]
    fn reconcile_target_inputs_prunes_stale_edges() {
        let mut graph = graph::GraphState::new();
        let a = Url::parse("snaq://graph/a.sl").unwrap();
        let b = Url::parse("snaq://graph/b.sl").unwrap();
        graph.connect(a.clone(), b.clone(), "x".to_string());
        graph.connect(a, b.clone(), "y".to_string());
        let valid: std::collections::HashSet<String> = ["y".to_string()].into_iter().collect();
        let removed = graph.reconcile_target_inputs(&b, &valid);
        assert_eq!(removed.len(), 1);
        assert_eq!(removed[0].target_input_name, "x");
        let incoming = graph.incoming(&b);
        assert_eq!(incoming.len(), 1);
        assert_eq!(incoming[0].0, "y");
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
        let ids: std::collections::HashSet<_> =
            cancelled.iter().map(|(id, _)| id.as_str()).collect();
        assert!(ids.contains("w1"));
        assert!(ids.contains("w2"));
    }

    #[test]
    fn widget_registry_drain_all_entries_includes_scalar_and_streaming() {
        let mut reg = widget_registry::WidgetRegistry::new();
        let uri = Url::parse("file:///a.snaq").unwrap();
        let (tx, _rx) = futures::channel::oneshot::channel();
        reg.insert("w-stream".to_string(), uri.clone(), tx);
        reg.insert_scalar("w-scalar".to_string(), uri);
        let drained = reg.drain_all_entries();
        assert_eq!(drained.len(), 2);
        assert!(drained.iter().any(|(id, tx)| id == "w-stream" && tx.is_some()));
        assert!(drained.iter().any(|(id, tx)| id == "w-scalar" && tx.is_none()));
        assert!(reg.remove("w-stream").is_none());
        assert!(reg.remove("w-scalar").is_none());
    }

    #[test]
    fn fetch_slice_has_more_and_total_count_consistency() {
        let total_count = 10_u64;
        let offset = 4_u64;
        let elements_len = 3_u64;
        let has_more = offset + elements_len < total_count;
        assert!(has_more);
        let offset2 = 8_u64;
        let elements_len2 = 2_u64;
        let has_more2 = offset2 + elements_len2 < total_count;
        assert!(!has_more2);
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
        let json =
            r#"{"widgetId":"w2","sourceUri":"file:///p.snaq","externalStreams":{"x":0,"y":1}}"#;
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
            revision: None,
            canvas_id: None,
            uri: None,
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
            revision: None,
            canvas_id: None,
            uri: None,
            data: Some(serde_json::json!({ "totalElements": 5 })),
        };
        let json = serde_json::to_string(&params).unwrap();
        assert!(
            json.contains("\"status\":\"Completed\""),
            "status should be PascalCase: {}",
            json
        );
        let back: PublishResultParams = serde_json::from_str(&json).unwrap();
        match back.status {
            PublishStatus::Completed => {}
            _ => panic!("round-trip should preserve Completed"),
        }
    }
}
