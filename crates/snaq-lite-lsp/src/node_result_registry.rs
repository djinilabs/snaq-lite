//! URI-keyed node result cache for graph-runtime recomputation.

use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use tower_lsp::lsp_types::Url;

#[derive(Clone)]
pub struct NodeResultEntry {
    pub value: Option<snaq_lite_lang::Value>,
    pub error: Option<String>,
    pub fingerprint: String,
    pub revision: u64,
}

pub struct NodeResultRegistry {
    by_uri: HashMap<Url, NodeResultEntry>,
}

impl NodeResultRegistry {
    fn fingerprint_value(value: &snaq_lite_lang::Value) -> String {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        Self::hash_value(value, &mut hasher);
        format!("{:x}", hasher.finish())
    }

    fn hash_vector(
        vector: &snaq_lite_lang::VectorValue,
        hasher: &mut std::collections::hash_map::DefaultHasher,
    ) {
        use snaq_lite_lang::LazyVector;
        use snaq_lite_lang::VectorOrientation;

        match vector.orientation {
            VectorOrientation::Column => 0u8.hash(hasher),
            VectorOrientation::Row => 1u8.hash(hasher),
        }
        match &vector.inner {
            LazyVector::FromInput(id) => {
                0u8.hash(hasher);
                id.hash(hasher);
            }
            LazyVector::FromEvaluated(results) => {
                1u8.hash(hasher);
                results.len().hash(hasher);
                for item in results {
                    match item {
                        Ok(Some(v)) => {
                            0u8.hash(hasher);
                            Self::hash_value(v, hasher);
                        }
                        Ok(None) => 1u8.hash(hasher),
                        Err(e) => {
                            2u8.hash(hasher);
                            e.to_string().hash(hasher);
                        }
                    }
                }
            }
            LazyVector::FromExprs(defs) => {
                2u8.hash(hasher);
                defs.len().hash(hasher);
                format!("{defs:?}").hash(hasher);
            }
            LazyVector::FromExprsWithEnv { defs, env } => {
                3u8.hash(hasher);
                defs.len().hash(hasher);
                format!("{defs:?}").hash(hasher);
                env.hash(hasher);
            }
            LazyVector::Map { source, op } => {
                4u8.hash(hasher);
                format!("{op:?}").hash(hasher);
                Self::hash_vector(
                    &snaq_lite_lang::VectorValue {
                        inner: (**source).clone(),
                        orientation: vector.orientation,
                    },
                    hasher,
                );
            }
            LazyVector::Transpose { source } => {
                5u8.hash(hasher);
                Self::hash_vector(
                    &snaq_lite_lang::VectorValue {
                        inner: (**source).clone(),
                        orientation: vector.orientation,
                    },
                    hasher,
                );
            }
            LazyVector::ZipMap { left, right, op } => {
                6u8.hash(hasher);
                format!("{op:?}").hash(hasher);
                format!("{left:?}").hash(hasher);
                format!("{right:?}").hash(hasher);
            }
            LazyVector::Outer { left, right, op } => {
                7u8.hash(hasher);
                format!("{op:?}").hash(hasher);
                format!("{left:?}").hash(hasher);
                format!("{right:?}").hash(hasher);
            }
            LazyVector::Take {
                source,
                start,
                length,
            } => {
                8u8.hash(hasher);
                start.hash(hasher);
                length.hash(hasher);
                format!("{source:?}").hash(hasher);
            }
        }
    }

    fn hash_value(
        value: &snaq_lite_lang::Value,
        hasher: &mut std::collections::hash_map::DefaultHasher,
    ) {
        match value {
            snaq_lite_lang::Value::Numeric(q) => {
                0u8.hash(hasher);
                format!("{q:?}").hash(hasher);
            }
            snaq_lite_lang::Value::Symbolic(sq) => {
                1u8.hash(hasher);
                format!("{sq:?}").hash(hasher);
            }
            snaq_lite_lang::Value::FuzzyBool(fb) => {
                2u8.hash(hasher);
                format!("{fb:?}").hash(hasher);
            }
            snaq_lite_lang::Value::Undefined => 3u8.hash(hasher),
            snaq_lite_lang::Value::Vector(v) => {
                4u8.hash(hasher);
                Self::hash_vector(v, hasher);
            }
            snaq_lite_lang::Value::Function(uf) => {
                5u8.hash(hasher);
                uf.hash(hasher);
            }
            snaq_lite_lang::Value::BuiltinFunction(name) => {
                6u8.hash(hasher);
                name.hash(hasher);
            }
            snaq_lite_lang::Value::Map(id) => {
                7u8.hash(hasher);
                id.hash(hasher);
            }
            snaq_lite_lang::Value::Date(date) => {
                8u8.hash(hasher);
                format!("{date:?}").hash(hasher);
            }
        }
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

    pub fn new() -> Self {
        Self {
            by_uri: HashMap::new(),
        }
    }

    pub fn upsert_value(&mut self, uri: Url, value: snaq_lite_lang::Value) -> u64 {
        self.upsert_value_if_changed(uri, value).0
    }

    pub fn upsert_error(&mut self, uri: Url, error: String) -> u64 {
        self.upsert_error_if_changed(uri, error).0
    }

    pub fn upsert_value_if_changed(&mut self, uri: Url, value: snaq_lite_lang::Value) -> (u64, bool) {
        let fingerprint = format!("value:{}", Self::fingerprint_value(&value));
        self.upsert_entry(uri, Some(value), None, fingerprint)
    }

    pub fn upsert_error_if_changed(&mut self, uri: Url, error: String) -> (u64, bool) {
        let fingerprint = format!("error:{error}");
        self.upsert_entry(uri, None, Some(error), fingerprint)
    }

    fn upsert_entry(
        &mut self,
        uri: Url,
        value: Option<snaq_lite_lang::Value>,
        error: Option<String>,
        fingerprint: String,
    ) -> (u64, bool) {
        if let Some(prev) = self.by_uri.get(&uri) {
            if prev.fingerprint == fingerprint {
                return (prev.revision, false);
            }
        }
        let revision = self
            .by_uri
            .get(&uri)
            .map(|e| e.revision.saturating_add(1))
            .unwrap_or(1);
        self.by_uri.insert(
            uri,
            NodeResultEntry {
                value,
                error,
                fingerprint,
                revision,
            },
        );
        (revision, true)
    }

    pub fn get(&self, uri: &Url) -> Option<&NodeResultEntry> {
        self.by_uri.get(uri)
    }

    pub fn remove(&mut self, uri: &Url) -> bool {
        self.by_uri.remove(uri).is_some()
    }

    pub fn remove_with_prefix(&mut self, uri_prefix: &str) -> usize {
        let before = self.by_uri.len();
        self.by_uri
            .retain(|uri, _| !Self::uri_matches_prefix(uri.as_str(), uri_prefix));
        before.saturating_sub(self.by_uri.len())
    }

    pub fn clear(&mut self) {
        self.by_uri.clear();
    }
}

impl Default for NodeResultRegistry {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snaq_lite_lang::{Env, ExprDef, LazyVector, Quantity, StoredValue, Value, VectorValue};
    use snaq_lite_lang::user_function::UserFunction;

    #[test]
    fn upsert_and_read_latest_result_by_uri() {
        let mut store = NodeResultRegistry::new();
        let uri = Url::parse("snaq://graph/node.sl").unwrap();
        let rev1 = store.upsert_value(uri.clone(), Value::Numeric(Quantity::from_scalar(1.0)));
        let rev2 = store.upsert_value(uri.clone(), Value::Numeric(Quantity::from_scalar(2.0)));
        assert_eq!(rev1, 1);
        assert_eq!(rev2, 2);
        let entry = store.get(&uri).expect("entry");
        assert_eq!(entry.revision, 2);
        let Value::Numeric(q) = entry.value.clone().expect("value") else {
            panic!("expected numeric value");
        };
        assert!((q.value() - 2.0).abs() < 1e-10);
    }

    #[test]
    fn upsert_error_updates_revision() {
        let mut store = NodeResultRegistry::new();
        let uri = Url::parse("snaq://graph/node.sl").unwrap();
        let rev1 = store.upsert_error(uri.clone(), "boom".to_string());
        let rev2 = store.upsert_error(uri.clone(), "boom2".to_string());
        assert_eq!(rev1, 1);
        assert_eq!(rev2, 2);
        let entry = store.get(&uri).expect("entry");
        assert_eq!(entry.error.as_deref(), Some("boom2"));
        assert!(entry.value.is_none());
    }

    #[test]
    fn multiple_subscribers_receive_same_versioned_update() {
        let mut store = NodeResultRegistry::new();
        let uri = Url::parse("snaq://graph/node.sl").unwrap();
        let rev = store.upsert_value(uri.clone(), Value::Numeric(Quantity::from_scalar(9.0)));
        let left = store.get(&uri).expect("left read").revision;
        let right = store.get(&uri).expect("right read").revision;
        assert_eq!(rev, left);
        assert_eq!(left, right);
    }

    #[test]
    fn unchanged_fingerprint_keeps_revision_stable() {
        let mut store = NodeResultRegistry::new();
        let uri = Url::parse("snaq://graph/same.sl").unwrap();
        let (rev1, changed1) =
            store.upsert_value_if_changed(uri.clone(), Value::Numeric(Quantity::from_scalar(3.0)));
        let (rev2, changed2) =
            store.upsert_value_if_changed(uri.clone(), Value::Numeric(Quantity::from_scalar(3.0)));
        assert!(changed1);
        assert!(!changed2);
        assert_eq!(rev1, 1);
        assert_eq!(rev2, 1);
    }

    #[test]
    fn changed_fingerprint_increments_revision() {
        let mut store = NodeResultRegistry::new();
        let uri = Url::parse("snaq://graph/change.sl").unwrap();
        let (rev1, changed1) =
            store.upsert_value_if_changed(uri.clone(), Value::Numeric(Quantity::from_scalar(3.0)));
        let (rev2, changed2) =
            store.upsert_value_if_changed(uri.clone(), Value::Numeric(Quantity::from_scalar(4.0)));
        assert!(changed1);
        assert!(changed2);
        assert_eq!(rev1, 1);
        assert_eq!(rev2, 2);
    }

    #[test]
    fn from_input_vector_fingerprint_uses_handle_identity() {
        let mut store = NodeResultRegistry::new();
        let uri = Url::parse("snaq://graph/stream.sl").unwrap();
        let (id1, _tx1) = snaq_lite_lang::create_stream_input();
        let (id2, _tx2) = snaq_lite_lang::create_stream_input();
        let v1 = Value::Vector(snaq_lite_lang::VectorValue::column(
            snaq_lite_lang::LazyVector::FromInput(id1),
        ));
        let v2 = Value::Vector(snaq_lite_lang::VectorValue::column(
            snaq_lite_lang::LazyVector::FromInput(id2),
        ));
        let (rev1, changed1) = store.upsert_value_if_changed(uri.clone(), v1);
        let (rev2, changed2) = store.upsert_value_if_changed(uri.clone(), v2);
        assert!(changed1);
        assert!(changed2);
        assert_eq!(rev1, 1);
        assert_eq!(rev2, 2);
    }

    #[test]
    fn from_exprs_with_env_fingerprint_changes_when_env_changes() {
        let mut store = NodeResultRegistry::new();
        let uri = Url::parse("snaq://graph/deferred.sl").unwrap();
        let defs = vec![ExprDef::LitSymbol("a".to_string())];
        let env1 = Env::empty().extend(
            "a".to_string(),
            StoredValue::Numeric(Quantity::from_scalar(1.0)),
        );
        let env2 = Env::empty().extend(
            "a".to_string(),
            StoredValue::Numeric(Quantity::from_scalar(2.0)),
        );
        let v1 = Value::Vector(VectorValue::column(LazyVector::FromExprsWithEnv {
            defs: defs.clone(),
            env: env1,
        }));
        let v2 = Value::Vector(VectorValue::column(LazyVector::FromExprsWithEnv {
            defs,
            env: env2,
        }));
        let (rev1, changed1) = store.upsert_value_if_changed(uri.clone(), v1);
        let (rev2, changed2) = store.upsert_value_if_changed(uri, v2);
        assert!(changed1);
        assert!(
            changed2,
            "changing captured lexical env must change deferred vector fingerprint"
        );
        assert_eq!(rev1, 1);
        assert_eq!(rev2, 2);
    }

    #[test]
    fn function_fingerprint_changes_when_function_payload_changes() {
        let mut store = NodeResultRegistry::new();
        let uri = Url::parse("snaq://graph/function.sl").unwrap();
        let f1 = Value::Function(Box::new(UserFunction::new(
            vec![("x".to_string(), None)],
            Box::new(ExprDef::Lit(Quantity::from_scalar(1.0))),
            1,
        )));
        let f2 = Value::Function(Box::new(UserFunction::new(
            vec![("x".to_string(), None)],
            Box::new(ExprDef::Lit(Quantity::from_scalar(2.0))),
            1,
        )));
        let (rev1, changed1) = store.upsert_value_if_changed(uri.clone(), f1);
        let (rev2, changed2) = store.upsert_value_if_changed(uri, f2);
        assert!(changed1);
        assert!(
            changed2,
            "changing function body must change semantic fingerprint"
        );
        assert_eq!(rev1, 1);
        assert_eq!(rev2, 2);
    }
}
