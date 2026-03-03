//! Custom LSP methods and notification payloads for live result pub-sub (snaqlite/*).
//! Stream chunk protocol: serialize stream elements to JSON for snaqlite/publishResult.

use serde::{Deserialize, Serialize};
use snaq_lite_lang::{format_value_for_display, RunError, Value};

/// Custom LSP notification for snaqlite/publishResult (server → client).
pub struct PublishResultNotification;
impl tower_lsp::lsp_types::notification::Notification for PublishResultNotification {
    type Params = PublishResultParams;
    const METHOD: &'static str = "snaqlite/publishResult";
}

/// Params for snaqlite/subscribe. Range identifies the code block/expression to watch.
/// Phase 1: root-only subscription (range can be omitted or ignored; whole document result).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SubscribeParams {
    pub text_document: TextDocumentIdentifier,
    /// Range of the block/expression to subscribe to. Optional for root-only.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub range: Option<tower_lsp::lsp_types::Range>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TextDocumentIdentifier {
    pub uri: tower_lsp::lsp_types::Url,
}

/// Response for snaqlite/subscribe: unique subscription id for unsubscribe and notifications.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SubscribeResponse {
    pub subscription_id: String,
}

/// Params for snaqlite/unsubscribe.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct UnsubscribeParams {
    pub subscription_id: String,
}

/// Status in snaqlite/publishResult notification.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "PascalCase")]
pub enum PublishStatus {
    Running,
    Completed,
    Error,
    Cancelled,
}

/// Payload for snaqlite/publishResult notification (server → client).
/// `data` is a JSON value: for Running, an object with elements, offset?, count?; for Error/Cancelled, object with message/reason.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PublishResultParams {
    pub subscription_id: String,
    pub status: PublishStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub data: Option<serde_json::Value>,
}

// ---- Graph (snaqlite/graph/*) ----

/// Custom LSP notification for snaqlite/graph/nodeSignatureUpdated (server → client).
/// Sent after didOpen/didChange for a document so the frontend can render input/output ports.
pub struct NodeSignatureUpdatedNotification;
impl tower_lsp::lsp_types::notification::Notification for NodeSignatureUpdatedNotification {
    type Params = NodeSignatureUpdatedParams;
    const METHOD: &'static str = "snaqlite/graph/nodeSignatureUpdated";
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NodeSignatureUpdatedParams {
    pub uri: String,
    pub inputs: Vec<NodeInputPort>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub output_type: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NodeInputPort {
    pub name: String,
    pub r#type: String,
}

/// Params for snaqlite/graph/connect request.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ConnectParams {
    pub source_uri: String,
    pub target_uri: String,
    pub target_input_name: String,
}

/// Params for snaqlite/graph/disconnect request.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DisconnectParams {
    pub target_uri: String,
    pub target_input_name: String,
}

/// Notification snaqlite/graph/widgetDataUpdate (server → client).
pub struct WidgetDataUpdateNotification;
impl tower_lsp::lsp_types::notification::Notification for WidgetDataUpdateNotification {
    type Params = WidgetDataUpdateParams;
    const METHOD: &'static str = "snaqlite/graph/widgetDataUpdate";
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct WidgetDataUpdateParams {
    pub widget_id: String,
    pub status: WidgetDataStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub payload: Option<serde_json::Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "PascalCase")]
pub enum WidgetDataStatus {
    Running,
    Completed,
    Cancelled,
    Error,
}

/// Params for snaqlite/graph/subscribeWidget request.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SubscribeWidgetParams {
    pub widget_id: String,
    pub source_uri: String,
    /// Optional map from input name to host stream index (for file-block–fed inputs). Resolved to StreamHandleId in WASM via host getStreamHandleId(index).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub external_streams: Option<std::collections::HashMap<String, u32>>,
}

/// Params for snaqlite/graph/unsubscribeWidget request.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct UnsubscribeWidgetParams {
    pub widget_id: String,
}

/// Serialize a single stream element (Result<Option<Value>, RunError>) to JSON for the protocol.
/// Uses format_value_for_display for Ok(Some(Value)); undefined → null; error → { kind, message }.
pub fn stream_element_to_json(
    db: &dyn salsa::Database,
    item: &Result<Option<Value>, RunError>,
) -> serde_json::Value {
    match item {
        Ok(Some(v)) => {
            let display = format_value_for_display(db, v).unwrap_or_else(|_| "<error>".to_string());
            serde_json::json!({ "display": display })
        }
        Ok(None) => serde_json::Value::Null,
        Err(e) => serde_json::json!({
            "kind": "error",
            "message": e.to_string()
        }),
    }
}
