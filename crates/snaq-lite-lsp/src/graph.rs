//! Graph state and snaqlite/graph/connect for the visual computation DAG.

use std::collections::{HashMap, HashSet, VecDeque};
use tower_lsp::lsp_types::Url;

/// One edge: source URI → target URI, with the target's input port name.
#[derive(Clone, Debug)]
pub struct GraphEdge {
    pub source_uri: Url,
    pub target_uri: Url,
    pub target_input_name: String,
}

/// Graph state: edges and type-checking for connect.
pub struct GraphState {
    /// Edges: (source_uri, target_uri, target_input_name). No duplicates for (target_uri, target_input_name).
    edges: Vec<GraphEdge>,
}

impl GraphState {
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
            edges: Vec::new(),
        }
    }

    /// Incoming edges for a URI: list of (input_name, source_uri).
    pub fn incoming(&self, target_uri: &Url) -> Vec<(String, Url)> {
        self.edges
            .iter()
            .filter(|e| e.target_uri == *target_uri)
            .map(|e| (e.target_input_name.clone(), e.source_uri.clone()))
            .collect()
    }

    /// Target URIs that have an edge from this source (downstream nodes). Used to invalidate
    /// their widget subscriptions when the source document changes.
    pub fn targets_from_source(&self, source_uri: &Url) -> Vec<Url> {
        self.edges
            .iter()
            .filter(|e| e.source_uri == *source_uri)
            .map(|e| e.target_uri.clone())
            .collect()
    }

    /// Full downstream closure for a source URI (BFS), excluding the source itself.
    pub fn descendants_from_source(
        &self,
        source_uri: &Url,
        documents: &HashSet<Url>,
    ) -> Vec<Url> {
        let mut out = Vec::new();
        let mut visited: HashSet<Url> = HashSet::new();
        let mut q: VecDeque<Url> = VecDeque::new();
        q.push_back(source_uri.clone());
        visited.insert(source_uri.clone());
        while let Some(cur) = q.pop_front() {
            for next in self
                .edges
                .iter()
                .filter(|e| e.source_uri == cur)
                .map(|e| e.target_uri.clone())
            {
                if !documents.contains(&next) || !visited.insert(next.clone()) {
                    continue;
                }
                out.push(next.clone());
                q.push_back(next);
            }
        }
        out
    }

    /// Return changed roots plus all their downstream descendants, deduplicated.
    pub fn impacted_from_changed_nodes(
        &self,
        changed: &[Url],
        documents: &HashSet<Url>,
    ) -> Vec<Url> {
        let mut impacted = Vec::new();
        let mut seen = HashSet::new();
        for root in changed {
            if documents.contains(root) && seen.insert(root.clone()) {
                impacted.push(root.clone());
            }
            for d in self.descendants_from_source(root, documents) {
                if seen.insert(d.clone()) {
                    impacted.push(d);
                }
            }
        }
        impacted
    }

    /// Add or replace edge: at most one source per (target_uri, target_input_name).
    pub fn connect(&mut self, source_uri: Url, target_uri: Url, target_input_name: String) {
        self.disconnect(&target_uri, &target_input_name);
        self.edges.push(GraphEdge {
            source_uri,
            target_uri,
            target_input_name,
        });
    }

    /// True when adding `source -> target` would create a cycle in the current graph.
    pub fn would_create_cycle(
        &self,
        source_uri: &Url,
        target_uri: &Url,
        documents: &HashSet<Url>,
    ) -> bool {
        if source_uri == target_uri {
            return true;
        }
        // If target already reaches source, adding source->target closes the loop.
        let mut visited: HashSet<Url> = HashSet::new();
        let mut q: VecDeque<Url> = VecDeque::new();
        q.push_back(target_uri.clone());
        visited.insert(target_uri.clone());
        while let Some(cur) = q.pop_front() {
            if &cur == source_uri {
                return true;
            }
            for next in self
                .edges
                .iter()
                .filter(|e| e.source_uri == cur)
                .map(|e| e.target_uri.clone())
            {
                if !documents.contains(&next) || !visited.insert(next.clone()) {
                    continue;
                }
                q.push_back(next);
            }
        }
        false
    }

    /// Remove edge for this target and input name.
    pub fn disconnect(&mut self, target_uri: &Url, target_input_name: &str) {
        self.edges
            .retain(|e| !(e.target_uri == *target_uri && e.target_input_name == target_input_name));
    }

    /// Remove all edges where `uri` is either source or target.
    /// Returns the number of removed edges.
    pub fn remove_edges_for_uri(&mut self, uri: &Url) -> usize {
        let before = self.edges.len();
        self.edges
            .retain(|e| e.source_uri != *uri && e.target_uri != *uri);
        before.saturating_sub(self.edges.len())
    }

    /// Remove all edges where source or target URI starts with `uri_prefix`.
    /// Returns the number of removed edges.
    pub fn remove_edges_with_prefix(&mut self, uri_prefix: &str) -> usize {
        let before = self.edges.len();
        self.edges.retain(|e| {
            !Self::uri_matches_prefix(e.source_uri.as_str(), uri_prefix)
                && !Self::uri_matches_prefix(e.target_uri.as_str(), uri_prefix)
        });
        before.saturating_sub(self.edges.len())
    }

    /// Remove edges whose target input no longer exists on the target node.
    /// Returns removed edges so caller can emit invalidation metadata if needed.
    pub fn reconcile_target_inputs(
        &mut self,
        target_uri: &Url,
        valid_inputs: &HashSet<String>,
    ) -> Vec<GraphEdge> {
        let mut removed = Vec::new();
        self.edges.retain(|e| {
            let keep = e.target_uri != *target_uri || valid_inputs.contains(&e.target_input_name);
            if !keep {
                removed.push(e.clone());
            }
            keep
        });
        removed
    }

    /// Topological order of URIs that are ancestors of `sink` (including sink). Returns None if cycle.
    pub fn topological_order(&self, sink: &Url, documents: &HashSet<Url>) -> Option<Vec<Url>> {
        // rev_adj[target] = list of sources (who feeds into target)
        let mut rev_adj: HashMap<Url, Vec<Url>> = HashMap::new();
        for e in &self.edges {
            if documents.contains(&e.source_uri) && documents.contains(&e.target_uri) {
                rev_adj
                    .entry(e.target_uri.clone())
                    .or_default()
                    .push(e.source_uri.clone());
            }
        }
        // Ancestors of sink (BFS backward).
        let mut ancestors = HashSet::new();
        let mut q = VecDeque::new();
        q.push_back(sink.clone());
        ancestors.insert(sink.clone());
        while let Some(u) = q.pop_front() {
            if let Some(sources) = rev_adj.get(&u) {
                for s in sources {
                    if ancestors.insert(s.clone()) {
                        q.push_back(s.clone());
                    }
                }
            }
        }
        // In-degree: for each node in ancestors, count edges (s, node) with s in ancestors.
        let mut in_degree: HashMap<Url, usize> = ancestors.iter().map(|u| (u.clone(), 0)).collect();
        for e in &self.edges {
            if ancestors.contains(&e.source_uri) && ancestors.contains(&e.target_uri) {
                *in_degree.get_mut(&e.target_uri).unwrap() += 1;
            }
        }
        let mut order = Vec::new();
        let mut q: VecDeque<Url> = in_degree
            .iter()
            .filter(|(_, &d)| d == 0)
            .map(|(u, _)| u.clone())
            .collect();
        while let Some(u) = q.pop_front() {
            order.push(u.clone());
            for e in &self.edges {
                if e.source_uri == u && ancestors.contains(&e.target_uri) {
                    let t = e.target_uri.clone();
                    if let Some(d) = in_degree.get_mut(&t) {
                        *d = d.saturating_sub(1);
                        if *d == 0 {
                            q.push_back(t);
                        }
                    }
                }
            }
        }
        if order.len() == ancestors.len() {
            Some(order)
        } else {
            None
        }
    }
}

impl Default for GraphState {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn would_create_cycle_rejects_back_edge() {
        let mut graph = GraphState::new();
        let a = Url::parse("snaq://canvas/a.sl").unwrap();
        let b = Url::parse("snaq://canvas/b.sl").unwrap();
        let c = Url::parse("snaq://canvas/c.sl").unwrap();
        graph.connect(a.clone(), b.clone(), "p1".to_string());
        graph.connect(b.clone(), c.clone(), "p2".to_string());
        let docs: HashSet<_> = [a.clone(), b.clone(), c.clone()].into_iter().collect();
        assert!(graph.would_create_cycle(&c, &a, &docs));
        assert!(!graph.would_create_cycle(&a, &c, &docs));
    }
}
