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

/// Params for snaqlite/graph/resetNamespace request.
/// Removes graph/runtime state for all URIs that start with `uriPrefix`.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ResetNamespaceParams {
    pub uri_prefix: String,
}

/// Response for snaqlite/graph/resetNamespace.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ResetNamespaceResponse {
    pub removed_documents: usize,
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

// ---- Result summary and fetchResultSlice ----

/// Result type for Completed payload (resultType). Serialized as PascalCase to match frontend (Vector, Map, etc.).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "PascalCase")]
pub enum ResultType {
    Scalar,
    Vector,
    Map,
    Undefined,
}

/// Summary for vector (length) or map (keys or keyCount).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ResultSummary {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub length: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub keys: Option<Vec<String>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub key_count: Option<usize>,
}

/// Params for snaqlite/graph/fetchResultSlice request.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FetchResultSliceParams {
    pub widget_id: String,
    /// 0-based path: empty = root; numbers = vector index; strings = map key.
    pub path: Vec<PathSegment>,
    pub offset: u64,
    pub limit: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
pub enum PathSegment {
    Index(u64),
    Key(String),
}

/// Response for snaqlite/graph/fetchResultSlice.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FetchResultSliceResponse {
    pub elements: Vec<serde_json::Value>,
    pub total_count: u64,
    pub has_more: bool,
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

/// Serialize a Value to a ResultSliceElement: scalar → { display }; vector → { type, path }; map → { type, path [, keys] }.
/// path_json is the path to this value as JSON array (numbers and strings) for client to request children.
/// Nested vector length is omitted (client gets totalCount from first fetchResultSlice for that path).
pub fn value_to_slice_element(
    db: &dyn salsa::Database,
    value: &Value,
    path_json: &[serde_json::Value],
) -> serde_json::Value {
    use snaq_lite_lang::map_registry;
    match value {
        Value::Vector(_) => serde_json::json!({
            "type": "vector",
            "path": path_json
        }),
        Value::Map(id) => {
            let keys: Vec<String> = map_registry::get(*id)
                .map(|entries| entries.iter().map(|(k, _)| k.clone()).collect())
                .unwrap_or_default();
            let key_count = keys.len();
            let mut obj = serde_json::json!({
                "type": "map",
                "path": path_json
            });
            let obj_map = obj.as_object_mut().unwrap();
            if key_count <= 20 {
                obj_map.insert("keys".to_string(), serde_json::json!(keys));
            } else {
                obj_map.insert("keyCount".to_string(), serde_json::json!(key_count));
            }
            obj
        }
        _ => {
            let display = format_value_for_display(db, value).unwrap_or_else(|_| "<error>".to_string());
            serde_json::json!({ "display": display })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snaq_lite_lang::Value;

    #[test]
    fn value_to_slice_element_preserves_path_contract() {
        let (value, db) = snaq_lite_lang::run_with_stream_inputs(
            "[1, 2, 3]",
            &snaq_lite_lang::default_si_registry(),
            std::collections::HashMap::new(),
        )
        .unwrap();
        let path = vec![serde_json::json!(3_u64), serde_json::json!("x")];
        let elem = value_to_slice_element(&db, &value, &path);
        assert_eq!(elem["type"].as_str(), Some("vector"));
        assert_eq!(elem["path"], serde_json::json!(path));

        // Scalar elements intentionally include display only.
        let scalar = value_to_slice_element(
            &db,
            &Value::Numeric(snaq_lite_lang::Quantity::from_scalar(2.0)),
            &path,
        );
        assert_eq!(scalar["display"].as_str(), Some("2"));
        assert!(scalar.get("path").is_none());
    }
}
