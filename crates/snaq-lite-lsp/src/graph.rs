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

    /// Add or replace edge: at most one source per (target_uri, target_input_name).
    pub fn connect(&mut self, source_uri: Url, target_uri: Url, target_input_name: String) {
        self.disconnect(&target_uri, &target_input_name);
        self.edges.push(GraphEdge {
            source_uri,
            target_uri,
            target_input_name,
        });
    }

    /// Remove edge for this target and input name.
    pub fn disconnect(&mut self, target_uri: &Url, target_input_name: &str) {
        self.edges
            .retain(|e| !(e.target_uri == *target_uri && e.target_input_name == target_input_name));
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
