//! Custom LSP methods and notification payloads for live result pub-sub (snaqlite/*).
//! Stream chunk protocol: serialize stream elements to JSON for snaqlite/publishNodeResult.

use serde::{Deserialize, Serialize};
use snaq_lite_lang::{format_value_for_display, RunError, Value};

/// Custom LSP notification for snaqlite/publishNodeResult (server → client).
pub struct PublishNodeResultNotification;
impl tower_lsp::lsp_types::notification::Notification for PublishNodeResultNotification {
    type Params = PublishResultParams;
    const METHOD: &'static str = "snaqlite/publishNodeResult";
}

/// Params for snaqlite/subscribeNode (node-centric canonical API).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SubscribeNodeParams {
    pub source_uri: String,
}

/// Response for snaqlite/subscribeNode.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SubscribeNodeResponse {
    pub subscription_id: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub result_handle: Option<String>,
}

/// Params for snaqlite/unsubscribeNode.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct UnsubscribeNodeParams {
    pub subscription_id: String,
}

/// Status in snaqlite/publishNodeResult notification.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "PascalCase")]
pub enum PublishStatus {
    Running,
    Completed,
    Error,
    Cancelled,
}

/// Payload for snaqlite/publishNodeResult notification (server → client).
/// `data` is a JSON value: for Running, an object with elements, offset?, count?; for Error/Cancelled, object with message/reason.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PublishResultParams {
    pub subscription_id: String,
    pub status: PublishStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub revision: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub canvas_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub uri: Option<String>,
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
    pub param_id: String,
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

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CanvasNodeDocumentPayload {
    pub uri: String,
    pub source: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub version: Option<i32>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CanvasEdgePayload {
    pub source_uri: String,
    pub target_uri: String,
    pub target_param_id: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CanvasDocumentPayload {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub canvas_id: Option<String>,
    #[serde(default)]
    pub revision: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub layout: Option<serde_json::Value>,
    pub nodes: Vec<CanvasNodeDocumentPayload>,
    pub edges: Vec<CanvasEdgePayload>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExportCanvasDocumentParams {}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ExportCanvasDocumentResponse {
    pub canvas_document: CanvasDocumentPayload,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ImportCanvasDocumentParams {
    pub canvas_document: CanvasDocumentPayload,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ImportCanvasDocumentResponse {
    pub imported_nodes: usize,
    pub imported_edges: usize,
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
    pub revision: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub canvas_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub uri: Option<String>,
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

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RenameParamParams {
    pub uri: String,
    pub param_id: String,
    pub new_name: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AddParamParams {
    pub uri: String,
    pub param_id: String,
    pub name: String,
    pub type_name: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RemoveParamParams {
    pub uri: String,
    pub param_id: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ApplyGraphPatchParams {
    pub operations: Vec<GraphPatchOperation>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "camelCase", rename_all_fields = "camelCase")]
pub enum GraphPatchOperation {
    SetNodeSource {
        uri: String,
        source: String,
    },
    Connect {
        source_uri: String,
        target_uri: String,
        target_input_name: String,
    },
    Disconnect {
        target_uri: String,
        target_input_name: String,
    },
    RenameParam {
        uri: String,
        param_id: String,
        new_name: String,
    },
    AddParam {
        uri: String,
        param_id: String,
        name: String,
        type_name: String,
    },
    RemoveParam {
        uri: String,
        param_id: String,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ApplyGraphPatchResponse {
    pub applied_operations: usize,
    pub affected_uris: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BootstrapSessionParams {}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct BootstrapSessionResponse {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub canvas_id: Option<String>,
    pub canvas_revision: u64,
    pub open_documents: usize,
    pub subscriptions: usize,
    pub widgets: usize,
    pub result_handles: usize,
    pub runtime_drained: bool,
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
    #[serde(skip_serializing_if = "Option::is_none")]
    pub widget_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub result_handle: Option<String>,
    /// 0-based path: empty = root; numbers = vector index; strings = map key.
    pub path: Vec<PathSegment>,
    pub offset: u64,
    pub limit: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cursor: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
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
    #[serde(skip_serializing_if = "Option::is_none")]
    pub next_cursor: Option<String>,
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
    use tower_lsp::lsp_types::notification::Notification;

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

    #[test]
    fn node_subscribe_params_roundtrip_json() {
        let params = SubscribeNodeParams {
            source_uri: "snaq://canvas/node_1.sl".to_string(),
        };
        let json = serde_json::to_value(&params).expect("serialize");
        assert_eq!(json["sourceUri"], serde_json::json!("snaq://canvas/node_1.sl"));
        let decoded: SubscribeNodeParams = serde_json::from_value(json).expect("deserialize");
        assert_eq!(decoded.source_uri, "snaq://canvas/node_1.sl");
    }

    #[test]
    fn publish_node_result_notification_method_name_is_stable() {
        assert_eq!(
            PublishNodeResultNotification::METHOD,
            "snaqlite/publishNodeResult"
        );
    }

    #[test]
    fn canvas_document_payload_roundtrip_json() {
        let payload = CanvasDocumentPayload {
            canvas_id: Some("canvas-a".to_string()),
            revision: 5,
            layout: Some(serde_json::json!({"viewport":{"x":1,"y":2,"zoom":1.0}})),
            nodes: vec![CanvasNodeDocumentPayload {
                uri: "snaq://canvas-a/n1.sl".to_string(),
                source: "1 + 2".to_string(),
                version: Some(1),
            }],
            edges: vec![CanvasEdgePayload {
                source_uri: "snaq://canvas-a/n1.sl".to_string(),
                target_uri: "snaq://canvas-a/n2.sl".to_string(),
                target_param_id: "p1".to_string(),
            }],
        };
        let json = serde_json::to_value(&payload).expect("serialize");
        let decoded: CanvasDocumentPayload = serde_json::from_value(json).expect("deserialize");
        assert_eq!(decoded.canvas_id.as_deref(), Some("canvas-a"));
        assert_eq!(decoded.revision, 5);
        assert_eq!(
            decoded.layout.as_ref().and_then(|v| v.get("viewport")),
            Some(&serde_json::json!({"x":1,"y":2,"zoom":1.0}))
        );
        assert_eq!(decoded.nodes.len(), 1);
        assert_eq!(decoded.edges.len(), 1);
    }

    #[test]
    fn publish_result_completed_vector_payload_supports_handle_and_summary() {
        let params = PublishResultParams {
            subscription_id: "sub-1".to_string(),
            status: PublishStatus::Completed,
            revision: Some(3),
            canvas_id: Some("canvas-a".to_string()),
            uri: Some("snaq://canvas-a/n1.sl".to_string()),
            data: Some(serde_json::json!({
                "resultType": "Vector",
                "resultSummary": { "length": 42 },
                "totalElements": 42,
                "resultHandle": "h-1"
            })),
        };
        let value = serde_json::to_value(&params).expect("serialize");
        let data = value.get("data").expect("data should exist");
        assert_eq!(data.get("resultType").and_then(|v| v.as_str()), Some("Vector"));
        assert_eq!(
            data.get("resultHandle").and_then(|v| v.as_str()),
            Some("h-1")
        );
        let decoded: PublishResultParams = serde_json::from_value(value).expect("deserialize");
        assert_eq!(decoded.subscription_id, "sub-1");
        assert!(matches!(decoded.status, PublishStatus::Completed));
    }

    #[test]
    fn fetch_result_slice_response_serializes_next_cursor_camel_case() {
        let response = FetchResultSliceResponse {
            elements: vec![serde_json::json!({ "display": "1" })],
            total_count: 10,
            has_more: true,
            next_cursor: Some("cursor-1".to_string()),
        };
        let value = serde_json::to_value(&response).expect("serialize");
        assert_eq!(value["totalCount"], serde_json::json!(10));
        assert_eq!(value["hasMore"], serde_json::json!(true));
        assert_eq!(value["nextCursor"], serde_json::json!("cursor-1"));
    }

    #[test]
    fn publish_result_params_serializes_canvas_id_camel_case() {
        let params = PublishResultParams {
            subscription_id: "sub-2".to_string(),
            status: PublishStatus::Running,
            revision: Some(5),
            canvas_id: Some("canvas-main".to_string()),
            uri: Some("snaq://canvas-main/node-1.sl".to_string()),
            data: Some(serde_json::json!({ "elements": [] })),
        };
        let value = serde_json::to_value(&params).expect("serialize");
        assert_eq!(value["canvasId"], serde_json::json!("canvas-main"));
        assert_eq!(value["subscriptionId"], serde_json::json!("sub-2"));
    }
}
