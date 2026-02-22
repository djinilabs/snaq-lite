//! Lazy, async vector type: ordered collection streamed from start to end.
//! Elements are `Option<Value>` (None = undefined/sparse). Vectors can be nested.

use crate::error::RunError;
use crate::ir::ExprDef;
use crate::symbolic::Value;
use futures::stream::{self, Stream};
use std::fmt;

/// Lazy vector: produces a stream of elements on demand (async).
/// Construction does no work; evaluation happens when the stream is consumed (or at creation for FromEvaluated).
#[derive(Clone, Debug, PartialEq)]
pub enum LazyVector {
    /// Vector from a literal: elements are expressions (evaluated when streamed via [VectorEvalContext]).
    FromExprs(Vec<ExprDef>),
    /// Pre-evaluated elements (from a literal evaluated inside a Salsa query; stream yields these).
    FromEvaluated(Vec<Result<Option<Value>, RunError>>),
    /// Placeholder for transform (one vector → another); not implemented yet.
    #[allow(dead_code)]
    Transform {
        source: Box<LazyVector>,
    },
    /// Placeholder for transpose (vector of vectors → vector of column vectors); not implemented yet.
    #[allow(dead_code)]
    Transpose {
        source: Box<LazyVector>,
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
            _ => None,
        }
    }

    /// If this is a [LazyVector::FromExprs], take the expression list (consumes self).
    /// Used when streaming with a [VectorEvalContext].
    pub fn take_literal_defs(self) -> Option<Vec<ExprDef>> {
        match self {
            LazyVector::FromExprs(defs) => Some(defs),
            _ => None,
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
            LazyVector::Transform { .. } | LazyVector::Transpose { .. } => {
                // Stub: yield nothing (or could return an error)
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
