//! Lazy, async vector type: ordered collection streamed from start to end.
//! Elements are `Option<Value>` (None = undefined/sparse). Vectors can be nested.
//! Vectors have orientation (column by default, row after transpose); see [VectorValue].
//! Display is intentionally `"<vector>"` for all vectors (orientation not shown); transpose flips
//! orientation, and element-wise Map preserves the operand's orientation.
//!
//! **Vector–vector binary ops** (add, sub, mul, div, and comparison ==, !=, <, <=, >, >=) depend on
//! orientation: column×column or row×row → element-wise ([ZipMap](LazyVector::ZipMap)), result
//! column or row (comparisons yield bool per element); column×row → outer product ([Outer](LazyVector::Outer)),
//! result = vector of column vectors (N×M matrix; comparisons yield bool per cell); row×column →
//! dot product (mul), sum(left) op sum(right) (add/sub), or compare(sum(left), sum(right)) (comparisons), scalar.

use crate::error::RunError;
use crate::ir::ExprDef;
use crate::symbolic::Value;
use futures::stream::{self, Stream};
use std::fmt;

/// Column (default) or row orientation. Transpose flips orientation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VectorOrientation {
    Column,
    Row,
}

impl VectorOrientation {
    pub fn flip(self) -> Self {
        match self {
            VectorOrientation::Column => VectorOrientation::Row,
            VectorOrientation::Row => VectorOrientation::Column,
        }
    }
}

/// Vector with orientation. Wraps [LazyVector]; used by [Value](crate::symbolic::Value).
/// Literals and 2D column yields are column; [transpose](VectorValue::transpose) flips to row;
/// Map (e.g. vector + scalar) preserves the vector operand's orientation.
#[derive(Clone, Debug, PartialEq)]
pub struct VectorValue {
    pub inner: LazyVector,
    pub orientation: VectorOrientation,
}

impl VectorValue {
    pub fn column(inner: LazyVector) -> Self {
        Self {
            inner,
            orientation: VectorOrientation::Column,
        }
    }

    pub fn row(inner: LazyVector) -> Self {
        Self {
            inner,
            orientation: VectorOrientation::Row,
        }
    }

    /// Wrap inner in [LazyVector::Transpose] and flip orientation.
    pub fn transpose(self) -> Self {
        Self {
            inner: LazyVector::Transpose {
                source: Box::new(self.inner),
            },
            orientation: self.orientation.flip(),
        }
    }
}

impl fmt::Display for VectorValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<vector>")
    }
}

/// Operation to apply element-wise when streaming a [LazyVector::Map].
/// Scalar operands are boxed to avoid recursive type size (Value → LazyVector → VectorMapOp → Value).
#[derive(Clone, Debug, PartialEq)]
pub enum VectorMapOp {
    /// elem + scalar (or scalar + elem)
    Add(Box<Value>),
    /// vector - scalar → elem - scalar
    SubRhs(Box<Value>),
    /// scalar - vector → scalar - elem
    SubLhs(Box<Value>),
    /// elem * scalar (or scalar * elem)
    Mul(Box<Value>),
    /// vector / scalar → elem / scalar
    DivRhs(Box<Value>),
    /// scalar / vector → scalar / elem
    DivLhs(Box<Value>),
    /// -elem
    Neg,
    /// Unary built-in by name (e.g. "sin", "cos", "tan")
    UnaryFunc(String),
    /// Comparison: elem == scalar, etc. Result FuzzyBool per element (Value::FuzzyBool).
    Eq(Box<Value>),
    Ne(Box<Value>),
    Lt(Box<Value>),
    Le(Box<Value>),
    Gt(Box<Value>),
    Ge(Box<Value>),
}

/// Binary operation for vector–vector (zip element-wise or outer product).
/// Used by [LazyVector::ZipMap] and [LazyVector::Outer].
#[derive(Clone, Debug, PartialEq)]
pub enum VectorBinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// Lazy vector: produces a stream of elements on demand (async).
/// Construction does no work; evaluation happens when the stream is consumed (or at creation for FromEvaluated).
#[derive(Clone, Debug, PartialEq)]
pub enum LazyVector {
    /// Vector from a literal: elements are expressions (evaluated when streamed via [VectorEvalContext]).
    FromExprs(Vec<ExprDef>),
    /// Pre-evaluated elements (from a literal evaluated inside a Salsa query; stream yields these).
    FromEvaluated(Vec<Result<Option<Value>, RunError>>),
    /// Element-wise map: when streamed (via [crate::queries::vector_into_stream]), each element is transformed by [VectorMapOp].
    Map {
        source: Box<LazyVector>,
        op: VectorMapOp,
    },
    /// Placeholder for transform (one vector → another); not implemented yet.
    #[allow(dead_code)]
    Transform {
        source: Box<LazyVector>,
    },
    /// Postfix transpose (e.g. `[1,2,3]'`, `[[1,4],[2,2],[3,5]]'`). For 1D vectors, streaming yields the same elements (identity). For vectors of vectors (2D), rows become columns (see [crate::queries::vector_into_stream]).
    Transpose {
        source: Box<LazyVector>,
    },
    /// Element-wise zip of two vectors (same orientation: column×column or row×row). When streamed, yields op(left_i, right_i) for each i. Result orientation preserved.
    ZipMap {
        left: Box<LazyVector>,
        right: Box<LazyVector>,
        op: VectorBinaryOp,
    },
    /// Outer product: column (left) × row (right). When streamed, yields one column per right (row) element: column j = [op(left_0, right_j), ..., op(left_{N-1}, right_j)]. Result is vector of column vectors (N×M matrix).
    Outer {
        left: Box<LazyVector>,
        right: Box<LazyVector>,
        op: VectorBinaryOp,
    },
    /// Slice: elements from index `start`, up to `length` elements. 0-based; out-of-range yields fewer/zero elements. Streaming: skip first `start`, then yield up to `length`.
    Take {
        source: Box<LazyVector>,
        start: usize,
        length: usize,
    },
}

/// Context for evaluating an expression when streaming a vector.
/// Implemented by the query layer so that streaming can call [value](crate::queries::value) without circular dependency.
pub trait VectorEvalContext {
    /// Evaluate a single expression to a value.
    fn eval_expr(&self, def: ExprDef) -> Result<Value, RunError>;
}

impl LazyVector {
    /// Build a lazy vector from a list of expression definitions (e.g. from a literal).
    pub fn from_exprs(defs: Vec<ExprDef>) -> Self {
        LazyVector::FromExprs(defs)
    }

    /// Build a lazy vector from pre-evaluated results (e.g. from a literal evaluated in value()).
    pub fn from_evaluated(results: Vec<Result<Option<Value>, RunError>>) -> Self {
        LazyVector::FromEvaluated(results)
    }

    /// If this is [LazyVector::FromEvaluated], take the results (consumes self).
    pub fn take_evaluated_results(self) -> Option<Vec<Result<Option<Value>, RunError>>> {
        match self {
            LazyVector::FromEvaluated(r) => Some(r),
            LazyVector::Map { .. }
            | LazyVector::FromExprs(_)
            | LazyVector::Transform { .. }
            | LazyVector::Transpose { .. }
            | LazyVector::ZipMap { .. }
            | LazyVector::Outer { .. }
            | LazyVector::Take { .. } => None,
        }
    }

    /// If this is a [LazyVector::FromExprs], take the expression list (consumes self).
    /// Used when streaming with a [VectorEvalContext].
    pub fn take_literal_defs(self) -> Option<Vec<ExprDef>> {
        match self {
            LazyVector::FromExprs(defs) => Some(defs),
            LazyVector::Map { .. }
            | LazyVector::FromEvaluated(_)
            | LazyVector::Transform { .. }
            | LazyVector::Transpose { .. }
            | LazyVector::ZipMap { .. }
            | LazyVector::Outer { .. }
            | LazyVector::Take { .. } => None,
        }
    }

    /// Produce a stream of elements. Each element is evaluated only when the stream is polled for that position.
    /// For `FromExprs`, `ctx.eval_expr(def)` is called for each element in order.
    pub fn into_stream(
        self,
        ctx: &impl VectorEvalContext,
    ) -> Box<dyn Stream<Item = Result<Option<Value>, RunError>> + '_> {
        match self {
            LazyVector::FromExprs(defs) => {
                let iter = defs
                    .into_iter()
                    .map(|d| ctx.eval_expr(d).map(Some));
                Box::new(stream::iter(iter))
            }
            LazyVector::FromEvaluated(results) => Box::new(stream::iter(results)),
            LazyVector::Map { .. } | LazyVector::Transform { .. } => {
                // Stub: yield nothing (or could return an error)
                Box::new(stream::iter(std::iter::empty::<Result<Option<Value>, RunError>>()))
            }
            LazyVector::Transpose { source } => (*source).into_stream(ctx),
            LazyVector::ZipMap { .. } | LazyVector::Outer { .. } => {
                // Streaming for ZipMap/Outer is done via vector_into_stream in queries (needs db).
                Box::new(stream::iter(std::iter::empty::<Result<Option<Value>, RunError>>()))
            }
            LazyVector::Take { .. } => {
                // Take is streamed via vector_into_stream in queries (needs db).
                Box::new(stream::iter(std::iter::empty::<Result<Option<Value>, RunError>>()))
            }
        }
    }
}

impl fmt::Display for LazyVector {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<vector>")
    }
}
