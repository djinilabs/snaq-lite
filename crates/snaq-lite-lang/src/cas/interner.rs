//! Hash-consing interner for CAS expression nodes.

use crate::fuzzy::FuzzyBool;
use crate::quantity::Quantity;
use std::collections::HashMap;

/// Opaque handle into the expression pool. Structural equality is O(1) by id comparison.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct ExprId(pub u32);

/// A single node in the interned CAS AST. Children are ExprIds.
/// Add and Mul are n-ary for canonicalization; Sub and Div stay binary.
/// Call is opaque (name + args as (param name if named, child id)).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum ExprNode {
    Lit(Quantity),
    LitFuzzyBool(FuzzyBool),
    LitSymbol(String),
    Add(Vec<ExprId>),
    Mul(Vec<ExprId>),
    Sub(ExprId, ExprId),
    Div(ExprId, ExprId),
    Neg(ExprId),
    Call(String, Vec<(Option<String>, ExprId)>),
    /// Unit conversion: value expr, unit expr. Not folded; conversion in value().
    As(ExprId, ExprId),
    /// Vector literal: element expr ids. Pass-through in CAS.
    VecLiteral(Vec<ExprId>),
    /// Postfix transpose: inner must evaluate to a vector. Pass-through in CAS.
    Transpose(ExprId),
    /// Comparison: ==, !=, <, <=, >, >=. Result is FuzzyBool (LitFuzzyBool when constant-folded).
    Eq(ExprId, ExprId),
    Ne(ExprId, ExprId),
    Lt(ExprId, ExprId),
    Le(ExprId, ExprId),
    Gt(ExprId, ExprId),
    Ge(ExprId, ExprId),
    /// Conditional: if condition then then_branch else else_branch.
    If(ExprId, ExprId, ExprId),
    /// Explicit precision: left ~ right (variance = right.value()²).
    WithPrecision(ExprId, ExprId),
    /// Block: sequence of expressions; value is the last, or undefined if empty. Order preserved in CAS.
    Block(Vec<ExprId>),
}

/// Central cache: same structure => same ExprId. New nodes are interned on construction.
#[derive(Clone, Default)]
pub struct ExprInterner {
    nodes: Vec<ExprNode>,
    dedup: HashMap<ExprNode, ExprId>,
}

impl ExprInterner {
    pub fn new() -> Self {
        Self::default()
    }

    /// Return the node for an id. Panics if id is invalid.
    pub fn get(&self, id: ExprId) -> &ExprNode {
        &self.nodes[id.0 as usize]
    }

    /// If an identical node already exists, return its id. Otherwise push the node and return the new id.
    pub fn intern(&mut self, node: ExprNode) -> ExprId {
        if let Some(&id) = self.dedup.get(&node) {
            return id;
        }
        let id = ExprId(self.nodes.len() as u32);
        self.dedup.insert(node.clone(), id);
        self.nodes.push(node);
        id
    }
}
