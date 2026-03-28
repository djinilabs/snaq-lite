//! Helpers for the visual computation graph (LSP): type names and input declaration extraction.

use crate::ir::ExprDef;
use crate::symbolic::Value;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GraphInputDecl {
    pub name: String,
    pub param_id: String,
    pub type_name: String,
}

/// Returns a stable type name for a value, for use in graph port type checking and LSP notifications.
/// Used as the node `outputType` in snaqlite/graph/nodeSignatureUpdated.
pub fn value_type_name(value: &Value) -> Option<String> {
    Some(match value {
        Value::Numeric(_) => "Numeric",
        Value::Symbolic(_) => "Symbolic",
        Value::FuzzyBool(_) => "FuzzyBool",
        Value::Vector(_) => "Vector",
        Value::Undefined => "Undefined",
        Value::Function(_) => "Function",
        Value::BuiltinFunction(_) => "BuiltinFunction",
        Value::Map(_) => "Map",
        Value::Date(_) => "Date",
    }
    .to_string())
}

/// Extracts declarative input declarations from a program root. The root is expected to be a
/// Block; any block item that is an InputDecl(name, type_name) is collected. Used by the LSP
/// to send snaqlite/graph/nodeSignatureUpdated with the inputs array.
pub fn extract_input_decls_from_block(root: &ExprDef) -> Vec<(String, String)> {
    extract_input_decls_from_block_with_ids(root)
        .into_iter()
        .map(|d| (d.name, d.type_name))
        .collect()
}

/// Like `extract_input_decls_from_block`, but preserves stable `param_id`.
pub fn extract_input_decls_from_block_with_ids(root: &ExprDef) -> Vec<GraphInputDecl> {
    let list = match root {
        ExprDef::Block(children) => children,
        _ => return Vec::new(),
    };
    let mut out = Vec::new();
    for item in list {
        if let ExprDef::InputDecl(name, param_id, type_name) = item {
            out.push(GraphInputDecl {
                name: name.clone(),
                param_id: param_id.clone(),
                type_name: type_name.clone(),
            });
        }
    }
    out
}
