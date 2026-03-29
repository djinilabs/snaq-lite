//! Query group: build expression graph and evaluate.
//!
//! When inputs (`ProgramDef`) change, Salsa invalidates only the memoized
//! results that depended on them, so recomputation is incremental.
//! Evaluation returns Value (Numeric or Symbolic).

use crate::error::{RunError, RunErrorKind, Span};
use crate::functions;
use crate::ir::{CallArg, ExprData, ExprDef, Expression, ProgramDef, SpannedExprDef, SpannedExprDefKind, StreamInputRegistry};
#[cfg(not(target_arch = "wasm32"))]
use crate::stream_handle::create_stream_input;
use crate::stream_handle::{take_receiver, ChunkFlattenStream};
use crate::map_registry;
use crate::scope::{closure_env_get, closure_env_register, Env, Scope, StoredValue};
use crate::user_function;
use crate::quantity::Quantity;
use crate::stat_compare::{
    comparison_probability, probability_to_fuzzy_bool, ComparisonKind, CONFIDENCE_THRESHOLD,
};
use crate::symbolic::{SymbolicExpr, SymbolicQuantity, Value};
use crate::unit::Unit;
use crate::unit_registry::UnitRegistry;
use crate::vector::{LazyVector, VectorBinaryOp, VectorMapOp, VectorOrientation, VectorValue};
use std::cell::RefCell;
use std::collections::HashMap;
use std::ops::Neg;
use std::pin::Pin;
use std::sync::OnceLock;
use std::task::{Context, Poll};

thread_local! {
    /// Registry used during evaluation (set by run()).
    static EVAL_REGISTRY: RefCell<Option<UnitRegistry>> = const { RefCell::new(None) };
    /// Stream input registry for $name lookups (set by run() before evaluation).
    static STREAM_INPUT_REGISTRY: RefCell<Option<StreamInputRegistry>> = const { RefCell::new(None) };
}

const DEFAULT_TRANSPOSE_BUFFER_LIMIT: usize = 100_000;
const DEFAULT_OUTER_LEFT_BUFFER_LIMIT: usize = 100_000;

#[cfg(test)]
thread_local! {
    static TEST_TRANSPOSE_BUFFER_LIMIT: RefCell<Option<usize>> = const { RefCell::new(None) };
    static TEST_OUTER_LEFT_BUFFER_LIMIT: RefCell<Option<usize>> = const { RefCell::new(None) };
}

fn parse_positive_usize_env(var: &str, default: usize) -> usize {
    std::env::var(var)
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .filter(|v| *v > 0)
        .unwrap_or(default)
}

fn transpose_buffer_limit() -> usize {
    #[cfg(test)]
    {
        if let Some(v) = TEST_TRANSPOSE_BUFFER_LIMIT.with(|c| *c.borrow()) {
            return v;
        }
    }
    static LIMIT: OnceLock<usize> = OnceLock::new();
    *LIMIT.get_or_init(|| {
        parse_positive_usize_env(
            "SNAQ_TRANSPOSE_BUFFER_LIMIT",
            DEFAULT_TRANSPOSE_BUFFER_LIMIT,
        )
    })
}

fn outer_left_buffer_limit() -> usize {
    #[cfg(test)]
    {
        if let Some(v) = TEST_OUTER_LEFT_BUFFER_LIMIT.with(|c| *c.borrow()) {
            return v;
        }
    }
    static LIMIT: OnceLock<usize> = OnceLock::new();
    *LIMIT.get_or_init(|| {
        parse_positive_usize_env(
            "SNAQ_OUTER_LEFT_BUFFER_LIMIT",
            DEFAULT_OUTER_LEFT_BUFFER_LIMIT,
        )
    })
}

#[cfg(test)]
pub fn set_test_vector_buffer_limits(transpose_limit: Option<usize>, outer_left_limit: Option<usize>) {
    TEST_TRANSPOSE_BUFFER_LIMIT.with(|c| *c.borrow_mut() = transpose_limit);
    TEST_OUTER_LEFT_BUFFER_LIMIT.with(|c| *c.borrow_mut() = outer_left_limit);
}

/// Set the unit registry for the current thread (used by run() before evaluation).
pub fn set_eval_registry(registry: UnitRegistry) {
    EVAL_REGISTRY.with(|r| *r.borrow_mut() = Some(registry));
}

/// Set the stream input registry for the current thread (used by run() before evaluation when using $name).
pub fn set_stream_input_registry(registry: StreamInputRegistry) {
    STREAM_INPUT_REGISTRY.with(|r| *r.borrow_mut() = Some(registry));
}

/// Stream that yields pre-evaluated vector elements. Elements are evaluated at stream creation
/// time (Salsa does not allow creating tracked structs from within stream poll).
/// Unpin so it can be used with StreamExt::next/collect.
pub struct LiteralVectorStream {
    results: std::vec::IntoIter<Result<Option<Value>, RunError>>,
}

impl futures::stream::Stream for LiteralVectorStream {
    type Item = Result<Option<Value>, RunError>;

    fn poll_next(
        self: Pin<&mut Self>,
        _cx: &mut Context<'_>,
    ) -> Poll<Option<Self::Item>> {
        let this = self.get_mut();
        Poll::Ready(this.results.next())
    }
}

impl std::marker::Unpin for LiteralVectorStream {}

/// Evaluate one deferred vector-literal element inside a tracked query context.
#[salsa::tracked]
fn eval_deferred_vector_element(
    db: &dyn salsa::Database,
    env: Env,
    def: ExprDef,
) -> Result<Option<Value>, RunError> {
    let registry = EVAL_REGISTRY.with(|r| {
        r.borrow()
            .clone()
            .unwrap_or_else(crate::unit_registry::default_si_registry)
    });
    let scope = Scope::new(db, env);
    let expr = build_expression(db, def, None);
    value_inner(db, scope, expr, &registry).map(Some)
}

/// Stream that lazily evaluates literal element ExprDefs using a captured lexical environment.
pub struct DeferredLiteralVectorStream<'a> {
    db: &'a dyn salsa::Database,
    env: Env,
    defs: std::vec::IntoIter<ExprDef>,
}

impl<'a> futures::stream::Stream for DeferredLiteralVectorStream<'a> {
    type Item = Result<Option<Value>, RunError>;

    fn poll_next(
        self: Pin<&mut Self>,
        _cx: &mut Context<'_>,
    ) -> Poll<Option<Self::Item>> {
        let this = self.get_mut();
        let Some(def) = this.defs.next() else {
            return Poll::Ready(None);
        };
        Poll::Ready(Some(eval_deferred_vector_element(this.db, this.env.clone(), def)))
    }
}

impl std::marker::Unpin for DeferredLiteralVectorStream<'_> {}

/// Empty stream (for transpose/transform stubs). Unpin.
pub struct EmptyVectorStream;

impl futures::stream::Stream for EmptyVectorStream {
    type Item = Result<Option<Value>, RunError>;

    fn poll_next(
        self: Pin<&mut Self>,
        _cx: &mut Context<'_>,
    ) -> Poll<Option<Self::Item>> {
        Poll::Ready(None)
    }
}

impl std::marker::Unpin for EmptyVectorStream {}

/// Stream that yields a single error then completes. Used when a stream input handle is not available at consume time.
pub struct OneErrorStream {
    error: Option<RunError>,
}

impl futures::stream::Stream for OneErrorStream {
    type Item = Result<Option<Value>, RunError>;

    fn poll_next(
        self: Pin<&mut Self>,
        _cx: &mut Context<'_>,
    ) -> Poll<Option<Self::Item>> {
        let this = self.get_mut();
        Poll::Ready(this.error.take().map(Err))
    }
}

impl std::marker::Unpin for OneErrorStream {}

/// Stream that applies a [VectorMapOp] to each element of an inner stream.
/// When op is [VectorMapOp::UserMap], [db] is used to evaluate the user function per element.
pub struct MappedVectorStream<'a> {
    inner: Box<VectorStream<'a>>,
    op: VectorMapOp,
    db: Option<&'a dyn salsa::Database>,
}

impl<'a> futures::stream::Stream for MappedVectorStream<'a> {
    type Item = Result<Option<Value>, RunError>;

    fn poll_next(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Option<Self::Item>> {
        let this = self.get_mut();
        match Pin::new(this.inner.as_mut()).poll_next(cx) {
            Poll::Ready(Some(Ok(opt_elem))) => {
                let result = with_registry(|registry| {
                    apply_map_op(this.db, &this.op, opt_elem, registry)
                });
                Poll::Ready(Some(result))
            }
            Poll::Ready(Some(Err(e))) => Poll::Ready(Some(Err(e))),
            Poll::Ready(None) => Poll::Ready(None),
            Poll::Pending => Poll::Pending,
        }
    }
}

impl std::marker::Unpin for MappedVectorStream<'_> {}

/// Stream state for 2D transpose. Created by [vector_into_stream] for [crate::vector::LazyVector::Transpose].
/// Collects source rows in poll-based steps, then yields columns if every element is a vector,
/// else yields the original 1D stream content.
///
/// Note: true transpose requires row buffering; we avoid eager API-level materialization,
/// but row contents must still be buffered to emit columns.
pub struct TransposedVectorStream<'a> {
    db: &'a dyn salsa::Database,
    inner: Box<VectorStream<'a>>,
    row_stream: Option<Box<VectorStream<'a>>>,
    buffer: Vec<Result<Option<Value>, RunError>>,
    current_row: Vec<Result<Option<Value>, RunError>>,
    rows: Vec<Vec<Result<Option<Value>, RunError>>>,
    phase: TransposePhase,
}

enum TransposePhase {
    Collecting,
    Yielding1D { index: usize },
    YieldingColumns {
        col_index: usize,
        max_cols: usize,
    },
    Done,
}

impl<'a> TransposedVectorStream<'a> {
    fn new(db: &'a dyn salsa::Database, inner: VectorStream<'a>) -> Self {
        Self {
            db,
            inner: Box::new(inner),
            row_stream: None,
            buffer: Vec::new(),
            current_row: Vec::new(),
            rows: Vec::new(),
            phase: TransposePhase::Collecting,
        }
    }
}

impl<'a> futures::stream::Stream for TransposedVectorStream<'a> {
    type Item = Result<Option<Value>, RunError>;

    fn poll_next(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Option<Self::Item>> {
        let this = self.get_mut();
        loop {
            match &mut this.phase {
                TransposePhase::Collecting => {
                    if let Some(ref mut row_stream) = this.row_stream {
                        match Pin::new(row_stream.as_mut()).poll_next(cx) {
                            Poll::Ready(Some(item)) => {
                                this.current_row.push(item);
                                if this.current_row.len() > transpose_buffer_limit() {
                                    return Poll::Ready(Some(Err(RunError::new(
                                        RunErrorKind::InvalidArgument(format!(
                                            "transpose buffering limit exceeded ({})",
                                            transpose_buffer_limit()
                                        )),
                                    ))));
                                }
                                continue;
                            }
                            Poll::Ready(None) => {
                                this.rows.push(std::mem::take(&mut this.current_row));
                                this.row_stream = None;
                                continue;
                            }
                            Poll::Pending => return Poll::Pending,
                        }
                    }
                    match Pin::new(this.inner.as_mut()).poll_next(cx) {
                        Poll::Ready(Some(item)) => {
                            this.buffer.push(item.clone());
                            if this.buffer.len() > transpose_buffer_limit() {
                                return Poll::Ready(Some(Err(RunError::new(
                                    RunErrorKind::InvalidArgument(format!(
                                        "transpose buffering limit exceeded ({})",
                                        transpose_buffer_limit()
                                    )),
                                ))));
                            }
                            if let Ok(Some(Value::Vector(v))) = &item {
                                let row_stream = vector_into_stream(this.db, v.inner.clone());
                                this.row_stream = Some(Box::new(row_stream));
                            }
                            continue;
                        }
                        Poll::Ready(None) => {
                            if this.rows.len() == this.buffer.len() && !this.buffer.is_empty() {
                                let max_cols =
                                    this.rows.iter().map(|r| r.len()).max().unwrap_or(0);
                                this.phase = TransposePhase::YieldingColumns {
                                    col_index: 0,
                                    max_cols,
                                };
                                continue;
                            }
                            this.phase = TransposePhase::Yielding1D { index: 0 };
                            continue;
                        }
                        Poll::Pending => return Poll::Pending,
                    }
                }
                TransposePhase::Yielding1D { index } => {
                    let i = *index;
                    if i >= this.buffer.len() {
                        this.phase = TransposePhase::Done;
                        return Poll::Ready(None);
                    }
                    *index += 1;
                    return Poll::Ready(Some(this.buffer[i].clone()));
                }
                TransposePhase::YieldingColumns {
                    col_index,
                    max_cols,
                } => {
                    if *col_index >= *max_cols {
                        this.phase = TransposePhase::Done;
                        return Poll::Ready(None);
                    }
                    let col: Vec<Result<Option<Value>, RunError>> = this
                        .rows
                        .iter()
                        .map(|row| row.get(*col_index).cloned().unwrap_or(Ok(None)))
                        .collect();
                    *col_index += 1;
                    let val = Ok(Some(Value::Vector(VectorValue::column(
                        LazyVector::from_evaluated(col),
                    ))));
                    return Poll::Ready(Some(val));
                }
                TransposePhase::Done => return Poll::Ready(None),
            }
        }
    }
}

impl std::marker::Unpin for TransposedVectorStream<'_> {}

/// Stream that zips two vectors element-wise and applies a binary op. Used for column×column and row×row.
pub struct ZippedVectorStream<'a> {
    left: Box<VectorStream<'a>>,
    right: Box<VectorStream<'a>>,
    op: VectorBinaryOp,
    left_count: usize,
    right_count: usize,
}

impl<'a> ZippedVectorStream<'a> {
    fn new(left: VectorStream<'a>, right: VectorStream<'a>, op: VectorBinaryOp) -> Self {
        Self {
            left: Box::new(left),
            right: Box::new(right),
            op,
            left_count: 0,
            right_count: 0,
        }
    }
}

impl<'a> futures::stream::Stream for ZippedVectorStream<'a> {
    type Item = Result<Option<Value>, RunError>;

    fn poll_next(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Option<Self::Item>> {
        let this = self.get_mut();
        let left_item = Pin::new(this.left.as_mut()).poll_next(cx);
        let right_item = Pin::new(this.right.as_mut()).poll_next(cx);
        match (left_item, right_item) {
            (Poll::Ready(Some(Ok(la))), Poll::Ready(Some(Ok(rb)))) => {
                this.left_count += 1;
                this.right_count += 1;
                let result = with_registry(|registry| {
                    apply_binary_op(&this.op, la, rb, registry)
                });
                Poll::Ready(Some(result))
            }
            (Poll::Ready(Some(Err(e))), _) | (_, Poll::Ready(Some(Err(e)))) => {
                Poll::Ready(Some(Err(e)))
            }
            (Poll::Ready(None), Poll::Ready(None)) => Poll::Ready(None),
            (Poll::Ready(None), Poll::Ready(Some(_))) => Poll::Ready(Some(Err(
                RunError::new(RunErrorKind::VectorLengthMismatch {
                    left_len: this.left_count,
                    right_len: this.right_count + 1,
                }),
            ))),
            (Poll::Ready(Some(_)), Poll::Ready(None)) => Poll::Ready(Some(Err(
                RunError::new(RunErrorKind::VectorLengthMismatch {
                    left_len: this.left_count + 1,
                    right_len: this.right_count,
                }),
            ))),
            _ => Poll::Pending,
        }
    }
}

impl std::marker::Unpin for ZippedVectorStream<'_> {}

/// Stream for outer product (column × row): yields one column vector per right (row) element.
/// Column j = [left_0 op right_j, left_1 op right_j, ...], so matrix(i,j) = left_i op right_j.
///
/// Note: each emitted column depends on the full left input, so the left stream is buffered once
/// and reused while the right stream is consumed.
pub struct OuterProductVectorStream<'a> {
    left_buffer: Vec<Result<Option<Value>, RunError>>,
    right: Box<VectorStream<'a>>,
    op: VectorBinaryOp,
    phase: OuterPhase<'a>,
}

enum OuterPhase<'a> {
    /// Still draining the left (column) stream into left_buffer.
    DrainingLeft(Box<VectorStream<'a>>),
    /// Left buffer full; each poll fetches one right element and yields one column (Value::Vector).
    YieldColumn,
    /// No more right elements.
    Done,
}

impl<'a> OuterProductVectorStream<'a> {
    fn new(
        left: VectorStream<'a>,
        right: VectorStream<'a>,
        op: VectorBinaryOp,
    ) -> Self {
        Self {
            left_buffer: Vec::new(),
            right: Box::new(right),
            op,
            phase: OuterPhase::DrainingLeft(Box::new(left)),
        }
    }
}

impl<'a> futures::stream::Stream for OuterProductVectorStream<'a> {
    type Item = Result<Option<Value>, RunError>;

    fn poll_next(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Option<Self::Item>> {
        let this = self.get_mut();
        loop {
            match &mut this.phase {
                OuterPhase::DrainingLeft(ref mut left_stream) => {
                    match Pin::new(left_stream.as_mut()).poll_next(cx) {
                        Poll::Ready(Some(item)) => {
                            this.left_buffer.push(item);
                            if this.left_buffer.len() > outer_left_buffer_limit() {
                                return Poll::Ready(Some(Err(RunError::new(
                                    RunErrorKind::InvalidArgument(format!(
                                        "outer product left-buffer limit exceeded ({})",
                                        outer_left_buffer_limit()
                                    )),
                                ))));
                            }
                            continue;
                        }
                        Poll::Ready(None) => {
                            if this.left_buffer.is_empty() {
                                this.phase = OuterPhase::Done;
                            } else {
                                this.phase = OuterPhase::YieldColumn;
                            }
                            continue;
                        }
                        Poll::Pending => return Poll::Pending,
                    }
                }
                OuterPhase::YieldColumn => {
                    // Fetch next right element (if any) and build column = [left_i op right_j for all i].
                    match Pin::new(this.right.as_mut()).poll_next(cx) {
                        Poll::Ready(Some(Ok(Some(right_val)))) => {
                            let column: Vec<Result<Option<Value>, RunError>> = this
                                .left_buffer
                                .iter()
                                .map(|r| {
                                    let left_opt = r.as_ref().ok().and_then(|x| x.clone());
                                    with_registry(|registry| {
                                        apply_binary_op(
                                            &this.op,
                                            left_opt,
                                            Some(right_val.clone()),
                                            registry,
                                        )
                                    })
                                })
                                .collect();
                            let col_vec = VectorValue::column(LazyVector::from_evaluated(
                                column,
                            ));
                            return Poll::Ready(Some(Ok(Some(Value::Vector(col_vec)))));
                        }
                        Poll::Ready(Some(Ok(None))) => {
                            let column = this
                                .left_buffer
                                .iter()
                                .map(|_| Ok(None))
                                .collect();
                            let col_vec = VectorValue::column(LazyVector::from_evaluated(
                                column,
                            ));
                            return Poll::Ready(Some(Ok(Some(Value::Vector(col_vec)))));
                        }
                        Poll::Ready(Some(Err(e))) => return Poll::Ready(Some(Err(e))),
                        Poll::Ready(None) => {
                            this.phase = OuterPhase::Done;
                            return Poll::Ready(None);
                        }
                        Poll::Pending => return Poll::Pending,
                    }
                }
                OuterPhase::Done => return Poll::Ready(None),
            }
        }
    }
}

impl std::marker::Unpin for OuterProductVectorStream<'_> {}

/// Stream that yields a slice of the inner stream: skip first `skip` items, then yield up to `take` items.
pub struct TakeVectorStream<'a> {
    inner: Box<VectorStream<'a>>,
    skip: usize,
    take: usize,
    skipped: usize,
    yielded: usize,
}

impl<'a> TakeVectorStream<'a> {
    fn new(inner: VectorStream<'a>, skip: usize, take: usize) -> Self {
        Self {
            inner: Box::new(inner),
            skip,
            take,
            skipped: 0,
            yielded: 0,
        }
    }
}

impl<'a> futures::stream::Stream for TakeVectorStream<'a> {
    type Item = Result<Option<Value>, RunError>;

    fn poll_next(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Option<Self::Item>> {
        let this = self.get_mut();
        while this.skipped < this.skip {
            match Pin::new(this.inner.as_mut()).poll_next(cx) {
                Poll::Ready(Some(_item)) => {
                    this.skipped += 1;
                }
                Poll::Ready(None) => return Poll::Ready(None),
                Poll::Pending => return Poll::Pending,
            }
        }
        if this.yielded >= this.take {
            return Poll::Ready(None);
        }
        match Pin::new(this.inner.as_mut()).poll_next(cx) {
            Poll::Ready(Some(item)) => {
                this.yielded += 1;
                Poll::Ready(Some(item))
            }
            Poll::Ready(None) => Poll::Ready(None),
            Poll::Pending => Poll::Pending,
        }
    }
}

impl std::marker::Unpin for TakeVectorStream<'_> {}

/// Apply a binary op to two optional element values (for zip and outer). None propagates as Ok(None).
fn apply_binary_op(
    op: &VectorBinaryOp,
    a: Option<Value>,
    b: Option<Value>,
    registry: &UnitRegistry,
) -> Result<Option<Value>, RunError> {
    let (Some(a), Some(b)) = (a, b) else {
        return Ok(None);
    };
    let result = match op {
        VectorBinaryOp::Add => add_values(&a, &b, registry, None, None)?,
        VectorBinaryOp::Sub => sub_values(&a, &b, registry, None, None)?,
        VectorBinaryOp::Mul => mul_values(&a, &b, registry, None, None)?,
        VectorBinaryOp::Div => div_values(&a, &b, registry, None, None)?,
        VectorBinaryOp::Eq => cmp_values(CmpOp::Eq, &a, &b, registry, None, None)?,
        VectorBinaryOp::Ne => cmp_values(CmpOp::Ne, &a, &b, registry, None, None)?,
        VectorBinaryOp::Lt => cmp_values(CmpOp::Lt, &a, &b, registry, None, None)?,
        VectorBinaryOp::Le => cmp_values(CmpOp::Le, &a, &b, registry, None, None)?,
        VectorBinaryOp::Gt => cmp_values(CmpOp::Gt, &a, &b, registry, None, None)?,
        VectorBinaryOp::Ge => cmp_values(CmpOp::Ge, &a, &b, registry, None, None)?,
    };
    Ok(Some(result))
}

/// Unified stream type for vector elements (literal, mapped, empty, transposed, zipped, outer, take, or from external input).
pub enum VectorStream<'a> {
    Literal(LiteralVectorStream),
    DeferredLiteral(DeferredLiteralVectorStream<'a>),
    Mapped(MappedVectorStream<'a>),
    Empty(EmptyVectorStream),
    Transposed(TransposedVectorStream<'a>),
    Zipped(ZippedVectorStream<'a>),
    OuterProduct(OuterProductVectorStream<'a>),
    Take(TakeVectorStream<'a>),
    /// Stream from external input (`$name`); flattens chunks to elements.
    FromInput(ChunkFlattenStream),
    /// Single error then done (e.g. stream input handle not available).
    OneError(OneErrorStream),
}

impl<'a> futures::stream::Stream for VectorStream<'a> {
    type Item = Result<Option<Value>, RunError>;

    fn poll_next(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Option<Self::Item>> {
        match self.get_mut() {
            VectorStream::Literal(s) => Pin::new(s).poll_next(cx),
            VectorStream::DeferredLiteral(s) => Pin::new(s).poll_next(cx),
            VectorStream::Mapped(s) => Pin::new(s).poll_next(cx),
            VectorStream::Empty(s) => Pin::new(s).poll_next(cx),
            VectorStream::Transposed(s) => Pin::new(s).poll_next(cx),
            VectorStream::Zipped(s) => Pin::new(s).poll_next(cx),
            VectorStream::OuterProduct(s) => Pin::new(s).poll_next(cx),
            VectorStream::Take(s) => Pin::new(s).poll_next(cx),
            VectorStream::FromInput(s) => Pin::new(s).poll_next(cx),
            VectorStream::OneError(s) => Pin::new(s).poll_next(cx),
        }
    }
}

impl std::marker::Unpin for VectorStream<'_> {}

/// Apply a vector map op to one element. For `None` (sparse slot) returns `Ok(None)`.
/// Used by [MappedVectorStream] when streaming a [LazyVector::Map].
/// Invoke a user function with a single argument (used by [VectorMapOp::UserMap] per element).
fn apply_user_map_element(
    db: &dyn salsa::Database,
    uf: &user_function::UserFunction,
    elem: Value,
    _registry: &UnitRegistry,
) -> Result<Value, RunError> {
    if uf.params.len() != 1 {
        return Err(RunError::new(RunErrorKind::UnknownFunction(format!(
            "map requires a function of one parameter (got {} parameters)",
            uf.params.len()
        ))));
    }
    let closure_env = closure_env_get(uf.closure_env_id).ok_or_else(|| {
        RunError::new(RunErrorKind::UnknownFunction("closure env not found (wrong thread or stale id)".to_string()))
    })?;
    let param_name = uf.params[0].0.clone();
    let stored = StoredValue::from_value(&elem)
        .map_err(|_| RunError::new(RunErrorKind::BindingValueNotSupported("map: function parameter value cannot be stored".to_string())))?;
    let env = closure_env.extend(param_name, stored);
    // Build the lambda body through `program()` so tracked node construction happens
    // inside a tracked query, then evaluate in the same database/scope.
    let scope = Scope::new(db, env);
    let program_def = ProgramDef::new(db, *uf.body.clone(), None);
    let root = program(db, program_def);
    value(db, scope, root)
}

fn apply_map_op(
    db: Option<&dyn salsa::Database>,
    op: &VectorMapOp,
    elem: Option<Value>,
    registry: &UnitRegistry,
) -> Result<Option<Value>, RunError> {
    let Some(v) = elem else {
        return Ok(None);
    };
    let result = match op {
        VectorMapOp::Add(scalar) => add_values(&v, scalar, registry, None, None)?,
        VectorMapOp::SubRhs(scalar) => sub_values(&v, scalar, registry, None, None)?,
        VectorMapOp::SubLhs(scalar) => sub_values(scalar, &v, registry, None, None)?,
        VectorMapOp::Mul(scalar) => mul_values(&v, scalar, registry, None, None)?,
        VectorMapOp::DivRhs(scalar) => div_values(&v, scalar, registry, None, None)?,
        VectorMapOp::DivLhs(scalar) => div_values(scalar, &v, registry, None, None)?,
        VectorMapOp::Neg => neg_value(&v, None)?,
        VectorMapOp::UnaryFunc(name) => apply_unary_builtin(name, &v, registry)?,
        VectorMapOp::Eq(scalar) => cmp_values(CmpOp::Eq, &v, scalar, registry, None, None)?,
        VectorMapOp::Ne(scalar) => cmp_values(CmpOp::Ne, &v, scalar, registry, None, None)?,
        VectorMapOp::Lt(scalar) => cmp_values(CmpOp::Lt, &v, scalar, registry, None, None)?,
        VectorMapOp::Le(scalar) => cmp_values(CmpOp::Le, &v, scalar, registry, None, None)?,
        VectorMapOp::Gt(scalar) => cmp_values(CmpOp::Gt, &v, scalar, registry, None, None)?,
        VectorMapOp::Ge(scalar) => cmp_values(CmpOp::Ge, &v, scalar, registry, None, None)?,
        VectorMapOp::UserMap(uf) => {
            let db = db.ok_or_else(|| {
                RunError::new(RunErrorKind::UnknownFunction("internal: db required for UserMap".to_string()))
            })?;
            apply_user_map_element(db, uf, v, registry)?
        }
    };
    Ok(Some(result))
}

/// Evaluate a single-argument built-in on a scalar value.
/// Used when applying [VectorMapOp::UnaryFunc] per element; currently only sin, cos, tan are mapped over vectors.
fn apply_unary_builtin(
    name: &str,
    v: &Value,
    registry: &UnitRegistry,
) -> Result<Value, RunError> {
    let sym_reg = crate::symbol_registry::SymbolRegistry::default_registry();
    if let Ok(q) = v.to_quantity(&sym_reg) {
        if matches!(name, "sin" | "cos" | "tan") {
            let rad_unit = Unit::from_base_unit("rad");
            if let Ok(in_rad) = q.clone().convert_to(registry, &rad_unit) {
                let angle_rad = in_rad.value();
                if let Some(m) = functions::known_angle_from_rad(angle_rad) {
                    let exact = match name {
                        "sin" => Some(functions::exact_sin_match(m)),
                        "cos" => Some(functions::exact_cos_match(m)),
                        "tan" => functions::exact_tan_match(m),
                        _ => unreachable!(),
                    };
                    if let Some(expr) = exact {
                        return Ok(Value::Symbolic(SymbolicQuantity::new(
                            expr,
                            Unit::scalar(),
                        )));
                    }
                }
            }
        }
        return functions::call_builtin(name, &[q], registry);
    }
    if matches!(name, "sin" | "cos" | "tan") {
        if let Value::Symbolic(sq) = v {
            if let Some(m) =
                functions::known_angle_from_symbolic(&sq.expr, &sq.unit, registry)
            {
                let exact = match name {
                    "sin" => Some(functions::exact_sin_match(m)),
                    "cos" => Some(functions::exact_cos_match(m)),
                    "tan" => functions::exact_tan_match(m),
                    _ => unreachable!(),
                };
                if let Some(expr) = exact {
                    return Ok(Value::Symbolic(SymbolicQuantity::new(
                        expr,
                        Unit::scalar(),
                    )));
                }
            }
        }
    }
    // Reject types that value_to_symbolic_expr would panic on (Map, Undefined, Date).
    match v {
        Value::Map(_) => {
            return Err(RunError::new(RunErrorKind::UnsupportedVectorOperation))
        }
        Value::Undefined => return Err(RunError::new(RunErrorKind::UndefinedResult)),
        Value::Date(_) => {
            return Err(RunError::new(RunErrorKind::InvalidArgument(
                "date not supported for this function".to_string(),
            )))
        }
        _ => {}
    }
    let sym_args = vec![value_to_symbolic_expr(v)?];
    Ok(functions::symbolic_call(name, &sym_args, Unit::scalar()))
}

/// Turn a vector into a stream of elements.
///
/// For [LazyVector::FromEvaluated], elements are already computed and yielded as-is.
/// For [LazyVector::Map], each element is computed when the stream is consumed (op applied per element).
/// For [LazyVector::Transpose], 1D is identity; 2D (vector of vectors) is streamed without blocking (rows become columns).
/// Requires the same database that was used to create the program (e.g. from [run_with_registry]).
pub fn vector_into_stream<'db>(
    db: &'db dyn salsa::Database,
    vector: LazyVector,
) -> VectorStream<'db> {
    match vector {
        LazyVector::FromEvaluated(results) => VectorStream::Literal(LiteralVectorStream {
            results: results.into_iter(),
        }),
        LazyVector::FromExprsWithEnv { defs, env } => {
            VectorStream::DeferredLiteral(DeferredLiteralVectorStream {
                db,
                env,
                defs: defs.into_iter(),
            })
        }
        LazyVector::Map { source, op } => {
            let inner = vector_into_stream(db, *source);
            VectorStream::Mapped(MappedVectorStream {
                inner: Box::new(inner),
                op,
                db: Some(db),
            })
        }
        LazyVector::FromExprs(_) => VectorStream::OneError(OneErrorStream {
            error: Some(RunError::new(RunErrorKind::UnsupportedVectorOperation)),
        }),
        LazyVector::Transpose { source } => {
            let inner = vector_into_stream(db, *source);
            VectorStream::Transposed(TransposedVectorStream::new(db, inner))
        }
        LazyVector::ZipMap { left, right, op } => {
            let left_s = vector_into_stream(db, *left);
            let right_s = vector_into_stream(db, *right);
            VectorStream::Zipped(ZippedVectorStream::new(left_s, right_s, op))
        }
        LazyVector::Outer { left, right, op } => {
            let left_s = vector_into_stream(db, *left);
            let right_s = vector_into_stream(db, *right);
            VectorStream::OuterProduct(OuterProductVectorStream::new(
                left_s,
                right_s,
                op,
            ))
        }
        LazyVector::Take { source, start, length } => {
            let inner = vector_into_stream(db, *source);
            VectorStream::Take(TakeVectorStream::new(inner, start, length))
        }
        LazyVector::FromInput(id) => {
            match take_receiver(id) {
                Some(receiver) => VectorStream::FromInput(ChunkFlattenStream::new(receiver)),
                None => VectorStream::OneError(OneErrorStream {
                    error: Some(RunError::new(RunErrorKind::StreamInputNotAvailable)),
                }),
            }
        }
    }
}

fn with_registry<R, F: FnOnce(&UnitRegistry) -> R>(f: F) -> R {
    EVAL_REGISTRY.with(|r| {
        let reg = r.borrow();
        let reg = reg.as_ref().expect("unit registry not set; use run() or set_eval_registry()");
        f(reg)
    })
}

/// Collect a vector stream to a vec (used for row×column dot product and sum).
/// Also used by the LSP to fan-out one upstream vector to multiple downstream inputs.
pub fn collect_vector_stream(
    db: &dyn salsa::Database,
    v: LazyVector,
) -> Vec<Result<Option<Value>, RunError>> {
    use futures::stream::StreamExt;
    let stream = vector_into_stream(db, v);
    futures::executor::block_on(async move { stream.collect().await })
}

fn count_vector_stream(db: &dyn salsa::Database, v: LazyVector) -> usize {
    use futures::stream::StreamExt;
    let mut stream = vector_into_stream(db, v);
    futures::executor::block_on(async move {
        let mut count = 0usize;
        while stream.next().await.is_some() {
            count += 1;
        }
        count
    })
}

fn vector_index_stream(
    db: &dyn salsa::Database,
    v: LazyVector,
    index: usize,
) -> Result<Option<Value>, RunErrorKind> {
    use futures::stream::StreamExt;
    let mut stream = vector_into_stream(db, v);
    let mut seen = 0usize;
    futures::executor::block_on(async move {
        while let Some(item) = stream.next().await {
            if seen == index {
                return match item {
                    Ok(opt) => Ok(opt),
                    Err(e) => Err(e.kind),
                };
            }
            seen += 1;
        }
        Err(RunErrorKind::IndexOutOfBounds {
            index,
            length: seen,
        })
    })
}

/// Consume a stream input handle once and return its value (single element -> that value; multiple -> Vector).
/// Used by scalar-friendly native input declaration binding paths.
#[cfg(not(target_arch = "wasm32"))]
fn stream_input_to_value(handle_id: crate::stream_handle::StreamHandleId) -> Result<Value, RunError> {
    use futures::stream::StreamExt;
    let receiver = take_receiver(handle_id)
        .ok_or_else(|| RunError::new(RunErrorKind::StreamInputNotAvailable))?;
    let mut stream = ChunkFlattenStream::new(receiver);
    let first = futures::executor::block_on(async { stream.next().await });
    let Some(first_item) = first else {
        return Ok(Value::Undefined);
    };
    match first_item {
        Err(e) => Err(e),
        Ok(first_opt) => {
            let second = futures::executor::block_on(async { stream.next().await });
            let Some(second_item) = second else {
                return match first_opt {
                    Some(v) => Ok(v),
                    None => Ok(Value::Undefined),
                };
            };
            let (new_handle, mut sender) = create_stream_input();
            futures::executor::block_on(async {
                use futures::SinkExt;
                sender
                    .send(vec![Ok(first_opt), second_item])
                    .await
                    .map_err(|_| RunError::new(RunErrorKind::StreamInputNotAvailable))
            })?;
            std::thread::spawn(move || {
                use futures::SinkExt;
                use futures::stream::StreamExt;
                const FORWARD_CHUNK_SIZE: usize = 128;
                let mut batch: Vec<Result<Option<Value>, RunError>> =
                    Vec::with_capacity(FORWARD_CHUNK_SIZE);
                loop {
                    let next = futures::executor::block_on(async { stream.next().await });
                    match next {
                        Some(item) => {
                            batch.push(item);
                            if batch.len() >= FORWARD_CHUNK_SIZE
                                && futures::executor::block_on(async {
                                    sender.send(std::mem::take(&mut batch)).await
                                })
                                .is_err()
                            {
                                return;
                            }
                        }
                        None => break,
                    }
                }
                if !batch.is_empty() {
                    let _ = futures::executor::block_on(async { sender.send(batch).await });
                }
            });
            Ok(Value::Vector(VectorValue::column(LazyVector::FromInput(new_handle))))
        }
    }
}

/// Parse bracket-key string as vector index: non-negative integer literal, or variable name (look up in scope).
fn parse_index_key(
    env: &Env,
    key_string: &str,
) -> Result<usize, RunErrorKind> {
    if let Ok(n) = key_string.parse::<u64>() {
        let u = n as usize;
        if u as u64 == n {
            return Ok(u);
        }
    }
    if let Some(stored) = env.get(key_string) {
        let val = stored.to_value();
        let sym_reg = crate::symbol_registry::SymbolRegistry::default_registry();
        if let Ok(q) = val.to_quantity(&sym_reg) {
            let f = q.value();
            if !f.is_finite() || f < 0.0 {
                return Err(RunErrorKind::InvalidIndex(
                    "index must be a non-negative integer".to_string(),
                ));
            }
            if f.fract() != 0.0 {
                return Err(RunErrorKind::InvalidIndex(
                    "index must be an integer".to_string(),
                ));
            }
            return Ok(f as usize);
        }
    }
    Err(RunErrorKind::InvalidIndex(
        "index must be a non-negative integer or a variable name".to_string(),
    ))
}

/// Build the tracked expression graph from the program definition; returns the root.
/// When [ProgramDef::spanned_root] is set, each node gets a source span for runtime error location.
#[salsa::tracked]
pub fn program(db: &dyn salsa::Database, program_def: ProgramDef) -> Expression<'_> {
    let root_def = program_def.root(db).clone();
    let spanned_root = program_def.spanned_root(db).clone();
    build_expression(db, root_def, spanned_root)
}

/// Recursively build tracked Expression nodes from ExprDef.
/// When [spanned] is [Some], each node gets that subtree's span for runtime error location.
fn build_expression(db: &dyn salsa::Database, def: ExprDef, spanned: Option<SpannedExprDef>) -> Expression<'_> {
    let span = spanned.as_ref().map(|s| s.span);
    let data = match def {
        ExprDef::Lit(q) => return Expression::new(db, ExprData::Lit(q), span),
        ExprDef::LitFuzzyBool(f) => return Expression::new(db, ExprData::LitFuzzyBool(f.clone()), span),
        ExprDef::LitSymbol(name) => return Expression::new(db, ExprData::LitSymbol(name), span),
        ExprDef::LitDate(gd) => return Expression::new(db, ExprData::LitDate(gd.clone()), span),
        ExprDef::ExternalStream(name) => return Expression::new(db, ExprData::ExternalStream(name), span),
        ExprDef::InputDecl(name, param_id, type_name) => {
            return Expression::new(db, ExprData::InputDecl(name, param_id, type_name), span)
        }
        ExprDef::LitTemporal(_) => {
            panic!("unresolved LitTemporal: resolve() must convert to LitDate before building the graph")
        }
        ExprDef::LitScalar(..) | ExprDef::LitWithUnit(..) | ExprDef::LitUnit(..) => {
            panic!("unresolved expression: resolve() must be called before building the graph")
        }
        ExprDef::Add(l, r) => {
            let (ls, rs) = children2(&spanned, |s| {
                if let SpannedExprDefKind::Add(ls, rs) = &s.value {
                    Some((*ls.clone(), *rs.clone()))
                } else {
                    None
                }
            });
            let left = build_expression(db, *l, ls);
            let right = build_expression(db, *r, rs);
            ExprData::Add(left, right)
        }
        ExprDef::Sub(l, r) => {
            let (ls, rs) = children2(&spanned, |s| {
                if let SpannedExprDefKind::Sub(ls, rs) = &s.value {
                    Some((*ls.clone(), *rs.clone()))
                } else {
                    None
                }
            });
            let left = build_expression(db, *l, ls);
            let right = build_expression(db, *r, rs);
            ExprData::Sub(left, right)
        }
        ExprDef::Mul(l, r) => {
            let (ls, rs) = children2(&spanned, |s| {
                if let SpannedExprDefKind::Mul(ls, rs) = &s.value {
                    Some((*ls.clone(), *rs.clone()))
                } else {
                    None
                }
            });
            let left = build_expression(db, *l, ls);
            let right = build_expression(db, *r, rs);
            ExprData::Mul(left, right)
        }
        ExprDef::Div(l, r) => {
            let (ls, rs) = children2(&spanned, |s| {
                if let SpannedExprDefKind::Div(ls, rs) = &s.value {
                    Some((*ls.clone(), *rs.clone()))
                } else {
                    None
                }
            });
            let left = build_expression(db, *l, ls);
            let right = build_expression(db, *r, rs);
            ExprData::Div(left, right)
        }
        ExprDef::Eq(l, r) => {
            let (ls, rs) = children2(&spanned, |s| {
                if let SpannedExprDefKind::Eq(ls, rs) = &s.value {
                    Some((*ls.clone(), *rs.clone()))
                } else {
                    None
                }
            });
            let left = build_expression(db, *l, ls);
            let right = build_expression(db, *r, rs);
            ExprData::Eq(left, right)
        }
        ExprDef::Ne(l, r) => {
            let (ls, rs) = children2(&spanned, |s| {
                if let SpannedExprDefKind::Ne(ls, rs) = &s.value {
                    Some((*ls.clone(), *rs.clone()))
                } else {
                    None
                }
            });
            let left = build_expression(db, *l, ls);
            let right = build_expression(db, *r, rs);
            ExprData::Ne(left, right)
        }
        ExprDef::Lt(l, r) => {
            let (ls, rs) = children2(&spanned, |s| {
                if let SpannedExprDefKind::Lt(ls, rs) = &s.value {
                    Some((*ls.clone(), *rs.clone()))
                } else {
                    None
                }
            });
            let left = build_expression(db, *l, ls);
            let right = build_expression(db, *r, rs);
            ExprData::Lt(left, right)
        }
        ExprDef::Le(l, r) => {
            let (ls, rs) = children2(&spanned, |s| {
                if let SpannedExprDefKind::Le(ls, rs) = &s.value {
                    Some((*ls.clone(), *rs.clone()))
                } else {
                    None
                }
            });
            let left = build_expression(db, *l, ls);
            let right = build_expression(db, *r, rs);
            ExprData::Le(left, right)
        }
        ExprDef::Gt(l, r) => {
            let (ls, rs) = children2(&spanned, |s| {
                if let SpannedExprDefKind::Gt(ls, rs) = &s.value {
                    Some((*ls.clone(), *rs.clone()))
                } else {
                    None
                }
            });
            let left = build_expression(db, *l, ls);
            let right = build_expression(db, *r, rs);
            ExprData::Gt(left, right)
        }
        ExprDef::Ge(l, r) => {
            let (ls, rs) = children2(&spanned, |s| {
                if let SpannedExprDefKind::Ge(ls, rs) = &s.value {
                    Some((*ls.clone(), *rs.clone()))
                } else {
                    None
                }
            });
            let left = build_expression(db, *l, ls);
            let right = build_expression(db, *r, rs);
            ExprData::Ge(left, right)
        }
        ExprDef::And(l, r) => {
            let (ls, rs) = children2(&spanned, |s| {
                if let SpannedExprDefKind::And(ls, rs) = &s.value {
                    Some((*ls.clone(), *rs.clone()))
                } else {
                    None
                }
            });
            let left = build_expression(db, *l, ls);
            let right = build_expression(db, *r, rs);
            ExprData::And(left, right)
        }
        ExprDef::Neg(inner) => {
            let inner_s = child1(&spanned, |s| {
                if let SpannedExprDefKind::Neg(x) = &s.value {
                    Some((**x).clone())
                } else {
                    None
                }
            });
            let inner_expr = build_expression(db, *inner, inner_s);
            ExprData::Neg(inner_expr)
        }
        ExprDef::Call(name, args) => {
            let arg_spans = spanned.as_ref().and_then(|s| {
                if let SpannedExprDefKind::Call(_, a) = &s.value {
                    Some(a.iter().map(|a| match a {
                        crate::ir::SpannedCallArg::Positional(e) => Some((**e).clone()),
                        crate::ir::SpannedCallArg::Named(_, e) => Some((**e).clone()),
                    }).collect::<Vec<_>>())
                } else {
                    None
                }
            });
            let arg_exprs: Vec<(Option<String>, Expression<'_>)> = args
                .into_iter()
                .enumerate()
                .map(|(i, arg)| {
                    let (n, e) = match arg {
                        CallArg::Positional(e) => (None, build_expression(db, *e, arg_spans.as_ref().and_then(|v| v.get(i).and_then(|x| x.clone())))),
                        CallArg::Named(n, e) => (Some(n), build_expression(db, *e, arg_spans.as_ref().and_then(|v| v.get(i).and_then(|x| x.clone())))),
                    };
                    (n, e)
                })
                .collect();
            ExprData::Call(name, arg_exprs)
        }
        ExprDef::As(l, r) => {
            let (ls, rs) = children2(&spanned, |s| {
                if let SpannedExprDefKind::As(ls, rs) = &s.value {
                    Some((*ls.clone(), *rs.clone()))
                } else {
                    None
                }
            });
            let left = build_expression(db, *l, ls);
            let right = build_expression(db, *r, rs);
            ExprData::As(left, right)
        }
        ExprDef::VecLiteral(elems) => {
            let elem_spans = spanned.as_ref().and_then(|s| {
                if let SpannedExprDefKind::VecLiteral(es) = &s.value {
                    Some(es.clone())
                } else {
                    None
                }
            });
            let exprs: Vec<Expression<'_>> = elems
                .into_iter()
                .enumerate()
                .map(|(i, d)| build_expression(db, d, elem_spans.as_ref().and_then(|v| v.get(i).cloned())))
                .collect();
            ExprData::VecLiteral(exprs)
        }
        ExprDef::MapLiteral(entries) => {
            let value_spans = spanned.as_ref().and_then(|s| {
                if let SpannedExprDefKind::MapLiteral(es) = &s.value {
                    Some(es.iter().map(|(_, v)| v.clone()).collect::<Vec<_>>())
                } else {
                    None
                }
            });
            let exprs: Vec<(String, Expression<'_>)> = entries
                .into_iter()
                .enumerate()
                .map(|(i, (k, d))| {
                    let child_span = value_spans.as_ref().and_then(|v| v.get(i).cloned());
                    (k, build_expression(db, *d, child_span))
                })
                .collect();
            ExprData::MapLiteral(exprs)
        }
        ExprDef::Transpose(inner) => {
            let inner_s = child1(&spanned, |s| {
                if let SpannedExprDefKind::Transpose(x) = &s.value {
                    Some((**x).clone())
                } else {
                    None
                }
            });
            let inner_expr = build_expression(db, *inner, inner_s);
            ExprData::Transpose(inner_expr)
        }
        ExprDef::Index(base, key) => {
            let base_s = child1(&spanned, |s| {
                if let SpannedExprDefKind::Index(b, _) = &s.value {
                    Some((**b).clone())
                } else {
                    None
                }
            });
            let base_expr = build_expression(db, *base, base_s);
            ExprData::Index(base_expr, key)
        }
        ExprDef::Member(base, name) => {
            let base_s = child1(&spanned, |s| {
                if let SpannedExprDefKind::Member(b, _) = &s.value {
                    Some((**b).clone())
                } else {
                    None
                }
            });
            let base_expr = build_expression(db, *base, base_s);
            ExprData::Member(base_expr, name)
        }
        ExprDef::MethodCall(base, name, args) => {
            let (base_s, arg_spans) = match spanned.as_ref().and_then(|s| {
                if let SpannedExprDefKind::MethodCall(b, _, a) = &s.value {
                    Some(((**b).clone(), a.iter().map(|a| match a {
                        crate::ir::SpannedCallArg::Positional(e) => (**e).clone(),
                        crate::ir::SpannedCallArg::Named(_, e) => (**e).clone(),
                    }).collect::<Vec<_>>()))
                } else {
                    None
                }
            }) {
                Some((b, a)) => (Some(b), Some(a)),
                None => (None, None),
            };
            let base_expr = build_expression(db, *base, base_s);
            let arg_exprs: Vec<(Option<String>, Expression<'_>)> = args
                .into_iter()
                .enumerate()
                .map(|(i, arg)| match arg {
                    CallArg::Positional(e) => (None, build_expression(db, *e, arg_spans.as_ref().and_then(|v| v.get(i).cloned()))),
                    CallArg::Named(n, e) => (Some(n), build_expression(db, *e, arg_spans.as_ref().and_then(|v| v.get(i).cloned()))),
                })
                .collect();
            ExprData::MethodCall(base_expr, name, arg_exprs)
        }
        ExprDef::If(cond, then_b, else_b) => {
            let (cs, ts, es) = match spanned.as_ref().and_then(|s| {
                if let SpannedExprDefKind::If(c, t, e) = &s.value {
                    Some(((**c).clone(), (**t).clone(), (**e).clone()))
                } else {
                    None
                }
            }) {
                Some((c, t, e)) => (Some(c), Some(t), Some(e)),
                None => (None, None, None),
            };
            let cond_expr = build_expression(db, *cond, cs);
            let then_expr = build_expression(db, *then_b, ts);
            let else_expr = build_expression(db, *else_b, es);
            ExprData::If(cond_expr, then_expr, else_expr)
        }
        ExprDef::WithPrecision(l, r) => {
            let (ls, rs) = children2(&spanned, |s| {
                if let SpannedExprDefKind::WithPrecision(ls, rs) = &s.value {
                    Some((*ls.clone(), *rs.clone()))
                } else {
                    None
                }
            });
            let left = build_expression(db, *l, ls);
            let right = build_expression(db, *r, rs);
            ExprData::WithPrecision(left, right)
        }
        ExprDef::Block(exprs) => {
            let block_spans = spanned.as_ref().and_then(|s| {
                if let SpannedExprDefKind::Block(es) = &s.value {
                    Some(es.clone())
                } else {
                    None
                }
            });
            let exprs: Vec<Expression<'_>> = exprs
                .into_iter()
                .enumerate()
                .map(|(i, d)| build_expression(db, d, block_spans.as_ref().and_then(|v| v.get(i).cloned())))
                .collect();
            ExprData::Block(exprs)
        }
        ExprDef::Binding(name, rhs) => {
            let rhs_s = child1(&spanned, |s| {
                if let SpannedExprDefKind::Binding(_, r) = &s.value {
                    Some((**r).clone())
                } else {
                    None
                }
            });
            let rhs_expr = build_expression(db, *rhs, rhs_s);
            ExprData::Binding(name, rhs_expr)
        }
        ExprDef::Lambda(params, body) => {
            let (param_spans, body_s) = match spanned.as_ref().and_then(|s| {
                if let SpannedExprDefKind::Lambda(ps, b) = &s.value {
                    Some((ps.iter().map(|(_, o)| o.as_ref().map(|e| (**e).clone())).collect::<Vec<_>>(), (**b).clone()))
                } else {
                    None
                }
            }) {
                Some((p, b)) => (Some(p), Some(b)),
                None => (None, None),
            };
            let param_exprs: Vec<(String, Option<Expression<'_>>)> = params
                .into_iter()
                .enumerate()
                .map(|(i, (name, opt_def))| {
                    let opt_s = param_spans.as_ref().and_then(|v| v.get(i).cloned()).flatten();
                    (
                        name,
                        opt_def.map(|d| build_expression(db, *d, opt_s)),
                    )
                })
                .collect();
            let body_expr = build_expression(db, *body, body_s);
            ExprData::Lambda(param_exprs, body_expr)
        }
        ExprDef::CallExpr(callee, args) => {
            let (callee_s, arg_spans) = match spanned.as_ref().and_then(|s| {
                if let SpannedExprDefKind::CallExpr(c, a) = &s.value {
                    Some(((**c).clone(), a.iter().map(|a| match a {
                        crate::ir::SpannedCallArg::Positional(e) => (**e).clone(),
                        crate::ir::SpannedCallArg::Named(_, e) => (**e).clone(),
                    }).collect::<Vec<_>>()))
                } else {
                    None
                }
            }) {
                Some((c, a)) => (Some(c), Some(a)),
                None => (None, None),
            };
            let callee_expr = build_expression(db, *callee, callee_s);
            let arg_exprs: Vec<(Option<String>, Expression<'_>)> = args
                .into_iter()
                .enumerate()
                .map(|(i, arg)| match arg {
                    CallArg::Positional(e) => (None, build_expression(db, *e, arg_spans.as_ref().and_then(|v| v.get(i).cloned()))),
                    CallArg::Named(n, e) => (Some(n), build_expression(db, *e, arg_spans.as_ref().and_then(|v| v.get(i).cloned()))),
                })
                .collect();
            ExprData::CallExpr(callee_expr, arg_exprs)
        }
    };
    Expression::new(db, data, span)
}

fn child1(spanned: &Option<SpannedExprDef>, f: impl FnOnce(&SpannedExprDef) -> Option<SpannedExprDef>) -> Option<SpannedExprDef> {
    spanned.as_ref().and_then(f)
}

fn children2(spanned: &Option<SpannedExprDef>, f: impl FnOnce(&SpannedExprDef) -> Option<(SpannedExprDef, SpannedExprDef)>) -> (Option<SpannedExprDef>, Option<SpannedExprDef>) {
    match spanned.as_ref().and_then(f) {
        Some((a, b)) => (Some(a), Some(b)),
        None => (None, None),
    }
}

/// Evaluate a (possibly chained) binding and return the value and the scope after all bindings in the chain.
/// For non-binding expressions, returns (value, scope unchanged).
fn eval_binding_chain<'db>(
    db: &'db dyn salsa::Database,
    scope: Scope<'db>,
    expr: Expression<'db>,
    registry: &UnitRegistry,
) -> Result<(Value, Scope<'db>), RunError> {
    match expr.data(db) {
        ExprData::Binding(name, rhs) => {
            if functions::param_names(name).is_some() {
                return Err(run_err_with_span(db, expr, RunErrorKind::CannotObfuscateBuiltin(name.clone())));
            }
            let (v, inner_scope) = eval_binding_chain(db, scope, *rhs, registry)?;
            let stored = StoredValue::from_value(&v)?;
            let new_env = inner_scope.env(db).clone().extend(name.clone(), stored);
            let new_scope = Scope::new(db, new_env);
            Ok((v, new_scope))
        }
        _ => {
            let v = value_inner(db, scope, expr, registry)?;
            Ok((v, scope))
        }
    }
}

/// Evaluate an expression to a Value (Numeric or Symbolic). Uses the registry set by run() (thread-local).
/// Scope is passed so variable lookups and block bindings are memoized per (scope, expr).
/// We call with_registry only once here so that recursive evaluation does not stack with_registry
/// frames (fixes "Maximum call stack size exceeded" on WASM where the stack is small).
#[salsa::tracked]
pub fn value<'db>(
    db: &'db dyn salsa::Database,
    scope: Scope<'db>,
    expr: Expression<'db>,
) -> Result<Value, RunError> {
    let _data = expr.data(db);
    let _env = scope.env(db);
    with_registry(|registry| value_inner(db, scope, expr, registry))
}

/// Inner evaluator: same logic as value() but takes registry and recurses without with_registry,
/// so stack depth is one frame per expression level instead of two (value + with_registry).
#[allow(clippy::cognitive_complexity)]
fn value_inner<'db>(
    db: &'db dyn salsa::Database,
    scope: Scope<'db>,
    expr: Expression<'db>,
    registry: &UnitRegistry,
) -> Result<Value, RunError> {
    let data = expr.data(db);
    let env = scope.env(db);
    match data {
        ExprData::Lit(q) => Ok(Value::Numeric(q.clone())),
        ExprData::LitFuzzyBool(f) => Ok(Value::FuzzyBool(f.clone())),
        ExprData::LitDate(gd) => Ok(Value::Date(gd.clone())),
        ExprData::LitSymbol(name) => {
            // Scope first (variables shadow units), then built-in function name, then unit, then symbolic.
            if let Some(stored) = env.get(name) {
                Ok(stored.to_value())
            } else if functions::param_names(name).is_some() {
                Ok(Value::BuiltinFunction(name.clone()))
            } else if let Some(unit) = registry.get_unit_with_prefix(name) {
                Ok(Value::Numeric(Quantity::new(1.0, unit)))
            } else {
                Ok(Value::Symbolic(SymbolicQuantity::new(
                    SymbolicExpr::symbol(name.clone()),
                    Unit::scalar(),
                )))
            }
        }
        ExprData::ExternalStream(name) => {
            let stream_registry = STREAM_INPUT_REGISTRY.with(|r| *r.borrow());
            let handle = stream_registry
                .as_ref()
                .and_then(|reg| reg.inputs(db).get(name).copied())
                .ok_or_else(|| run_err_with_span(db, expr, RunErrorKind::UnboundStreamInput(name.clone())))?;
            Ok(Value::Vector(VectorValue::column(LazyVector::FromInput(handle))))
        }
        ExprData::InputDecl(_, _, _) => {
            // Metadata only; not evaluated standalone. Block iteration skips these.
            Ok(Value::Undefined)
        }
        ExprData::Add(l, r) => {
            let left = value_inner(db, scope, *l, registry)?;
            let right = value_inner(db, scope, *r, registry)?;
            add_values(&left, &right, registry, Some(db), expr.span(db))
        }
        ExprData::Sub(l, r) => {
            let left = value_inner(db, scope, *l, registry)?;
            let right = value_inner(db, scope, *r, registry)?;
            sub_values(&left, &right, registry, Some(db), expr.span(db))
        }
        ExprData::Mul(l, r) => {
            let left = value_inner(db, scope, *l, registry)?;
            let right = value_inner(db, scope, *r, registry)?;
            mul_values(&left, &right, registry, Some(db), expr.span(db))
        }
        ExprData::Div(l, r) => {
            let left = value_inner(db, scope, *l, registry)?;
            let right = value_inner(db, scope, *r, registry)?;
            match div_values(&left, &right, registry, Some(db), expr.span(db)) {
                Ok(v) => Ok(v),
                Err(e) if matches!(e.kind, RunErrorKind::DivisionByZero) => Ok(Value::Undefined),
                Err(e) => Err(e),
            }
        }
        ExprData::Eq(l, r) => {
            let left = value_inner(db, scope, *l, registry)?;
            let right = value_inner(db, scope, *r, registry)?;
            cmp_values(CmpOp::Eq, &left, &right, registry, Some(db), expr.span(db))
        }
        ExprData::Ne(l, r) => {
            let left = value_inner(db, scope, *l, registry)?;
            let right = value_inner(db, scope, *r, registry)?;
            cmp_values(CmpOp::Ne, &left, &right, registry, Some(db), expr.span(db))
        }
        ExprData::Lt(l, r) => {
            let left = value_inner(db, scope, *l, registry)?;
            let right = value_inner(db, scope, *r, registry)?;
            cmp_values(CmpOp::Lt, &left, &right, registry, Some(db), expr.span(db))
        }
        ExprData::Le(l, r) => {
            let left = value_inner(db, scope, *l, registry)?;
            let right = value_inner(db, scope, *r, registry)?;
            cmp_values(CmpOp::Le, &left, &right, registry, Some(db), expr.span(db))
        }
        ExprData::Gt(l, r) => {
            let left = value_inner(db, scope, *l, registry)?;
            let right = value_inner(db, scope, *r, registry)?;
            cmp_values(CmpOp::Gt, &left, &right, registry, Some(db), expr.span(db))
        }
        ExprData::Ge(l, r) => {
            let left = value_inner(db, scope, *l, registry)?;
            let right = value_inner(db, scope, *r, registry)?;
            cmp_values(CmpOp::Ge, &left, &right, registry, Some(db), expr.span(db))
        }
        ExprData::And(l, r) => {
            let left = value_inner(db, scope, *l, registry)?;
            let right = value_inner(db, scope, *r, registry)?;
            match (&left, &right) {
                (Value::FuzzyBool(f1), Value::FuzzyBool(f2)) => {
                    Ok(Value::FuzzyBool(f1.clone().and_(f2)))
                }
                _ => Err(run_err_with_span(db, expr, RunErrorKind::ExpectedCondition)),
            }
        }
        ExprData::Neg(inner) => {
            let v = value_inner(db, scope, *inner, registry)?;
            neg_value(&v, expr.span(db))
        }
        ExprData::Call(name, args) => eval_call_with(db, scope, name, args, registry, |s, e| value_inner(db, s, e, registry))
            .map_err(|e| with_span_if_missing(e, expr.span(db))),
        ExprData::As(left, right) => {
            let left_val = value_inner(db, scope, *left, registry)?;
            let right_val = value_inner(db, scope, *right, registry)?;
            let sym_reg = crate::symbol_registry::SymbolRegistry::default_registry();
            let target_quantity = right_val.to_quantity(&sym_reg).map_err(|_| {
                RunError::new(RunErrorKind::UnknownUnit(
                    "as: right side must evaluate to a unit (no symbols)".to_string(),
                ))
            })?;
            let target_unit = target_quantity.unit().clone();
            match &left_val {
                Value::FuzzyBool(_) => Err(run_err_with_span(db, expr, RunErrorKind::BooleanResult)),
                Value::Numeric(q) => {
                    let converted = q.clone().convert_to(registry, &target_unit).map_err(|e| {
                        match e {
                            crate::quantity::QuantityError::IncompatibleUnits(left, right) => {
                                RunError::new(RunErrorKind::DimensionMismatch { left, right })
                            }
                            _ => RunError::new(RunErrorKind::DivisionByZero),
                        }
                    })?;
                    Ok(Value::Numeric(converted))
                }
                Value::Symbolic(sq) => {
                    let scaled = scale_expr_to_unit(
                        &left_val,
                        &sq.expr,
                        &sq.unit,
                        &target_unit,
                        registry,
                    )?;
                    Ok(Value::Symbolic(SymbolicQuantity::new(scaled, target_unit)))
                }
                Value::Vector(_) => Err(run_err_with_span(db, expr, RunErrorKind::UnsupportedVectorOperation)),
                Value::Map(_) => Err(run_err_with_span(db, expr, RunErrorKind::UnsupportedVectorOperation)),
                Value::Undefined => Err(run_err_with_span(db, expr, RunErrorKind::UndefinedResult)),
                Value::Function(_) | Value::BuiltinFunction(_) => Err(run_err_with_span(db, expr, RunErrorKind::BindingValueNotSupported(
                    "function value cannot be converted to quantity".to_string(),
                ))),
                Value::Date(_) => Err(run_err_with_span(db, expr, RunErrorKind::InvalidArgument(
                    "date value cannot be converted to quantity".to_string(),
                ))),
            }
        }
        ExprData::VecLiteral(exprs) => {
            let defs = exprs
                .iter()
                .map(|e| expression_to_def(db, *e))
                .collect::<Vec<_>>();
            Ok(Value::Vector(VectorValue::column(
                LazyVector::FromExprsWithEnv {
                    defs,
                    env: scope.env(db).clone(),
                },
            )))
        }
        ExprData::MapLiteral(entries) => {
            let evaluated: Vec<(String, Value)> = entries
                .iter()
                .map(|(k, e)| Ok((k.clone(), value_inner(db, scope, *e, registry)?)))
                .collect::<Result<Vec<_>, RunError>>()?;
            let id = map_registry::register(evaluated);
            Ok(Value::Map(id))
        }
        ExprData::Transpose(inner) => {
            let v = value_inner(db, scope, *inner, registry)?;
            match v {
                Value::Vector(v) => Ok(Value::Vector(v.transpose())),
                _ => Err(run_err_with_span(db, expr, RunErrorKind::ExpectedVector)),
            }
        }
        ExprData::Member(base, name) => {
            let base_val = value_inner(db, scope, *base, registry)?;
            match &base_val {
                Value::Map(id) => {
                    let v = map_registry::get_key(*id, name);
                    Ok(v.unwrap_or(Value::Undefined))
                }
                Value::Vector(v) => {
                    let VectorValue { inner, .. } = v.clone();
                    match name.as_str() {
                        "length" => {
                            let len = count_vector_stream(db, inner);
                            Ok(Value::Numeric(Quantity::from_exact_scalar(len as f64)))
                        }
                        _ => Err(run_err_with_span(db, expr, RunErrorKind::UnknownProperty(name.clone()))),
                    }
                }
                _ => Err(run_err_with_span(db, expr, RunErrorKind::ExpectedVector)),
            }
        }
        ExprData::MethodCall(base, name, args) => {
            let base_val = value_inner(db, scope, *base, registry)?;
            let VectorValue { inner, orientation } = match &base_val {
                Value::Vector(v) => v.clone(),
                _ => return Err(run_err_with_span(db, expr, RunErrorKind::ExpectedVector)),
            };
            match name.as_str() {
                "take" => {
                    let arg_vals: Vec<Value> = args
                        .iter()
                        .map(|(_, e)| value_inner(db, scope, *e, registry))
                        .collect::<Result<Vec<_>, _>>()?;
                    if arg_vals.len() != 2 {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(format!(
                            "take requires 2 arguments (start, length), got {}",
                            arg_vals.len()
                        ))));
                    }
                    let sym_reg = crate::symbol_registry::SymbolRegistry::default_registry();
                    let start_q = arg_vals[0].to_quantity(&sym_reg).map_err(|_| {
                        RunError::new(RunErrorKind::InvalidIndex("take start must be numeric".to_string()))
                    })?;
                    let length_q = arg_vals[1].to_quantity(&sym_reg).map_err(|_| {
                        RunError::new(RunErrorKind::InvalidIndex("take length must be numeric".to_string()))
                    })?;
                    let start_f = start_q.value();
                    let length_f = length_q.value();
                    if !start_f.is_finite() || start_f < 0.0 {
                        return Err(run_err_with_span(db, expr, RunErrorKind::InvalidIndex(
                            "take start must be a non-negative integer".to_string(),
                        )));
                    }
                    if !length_f.is_finite() || length_f < 0.0 {
                        return Err(run_err_with_span(db, expr, RunErrorKind::InvalidIndex(
                            "take length must be a non-negative integer".to_string(),
                        )));
                    }
                    let start_u = start_f as usize;
                    let length_u = length_f as usize;
                    Ok(Value::Vector(VectorValue {
                        inner: LazyVector::Take {
                            source: Box::new(inner),
                            start: start_u,
                            length: length_u,
                        },
                        orientation,
                    }))
                }
                "map" => {
                    if args.len() != 1 {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(format!(
                            "map requires 1 argument (a function), got {}",
                            args.len()
                        ))));
                    }
                    let (_, fn_expr) = &args[0];
                    let fn_val = value_inner(db, scope, *fn_expr, registry)?;
                    match &fn_val {
                        Value::Function(uf) => {
                            if uf.params.len() != 1 {
                                return Err(run_err_with_span(
                                    db,
                                    expr,
                                    RunErrorKind::UnknownFunction(format!(
                                        "map requires a function of one parameter (got {} parameters)",
                                        uf.params.len()
                                    )),
                                ));
                            }
                            Ok(Value::Vector(VectorValue {
                                inner: LazyVector::Map {
                                    source: Box::new(inner),
                                    op: VectorMapOp::UserMap(uf.clone()),
                                },
                                orientation,
                            }))
                        }
                        Value::BuiltinFunction(name) => {
                            let params = functions::param_names(name).ok_or_else(|| {
                                RunError::new(RunErrorKind::UnknownMethod(
                                    "map requires a function (e.g. sqrt or fn (x) => (x+1))"
                                        .to_string(),
                                ))
                            })?;
                            if params.len() != 1 {
                                return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(format!(
                                    "map requires a function of one parameter (e.g. sqrt or fn x => (x+1)), got built-in '{}' which takes {}",
                                    name,
                                    params.len()
                                ))));
                            }
                            Ok(Value::Vector(VectorValue {
                                inner: LazyVector::Map {
                                    source: Box::new(inner),
                                    op: VectorMapOp::UnaryFunc(name.clone()),
                                },
                                orientation,
                            }))
                        }
                        _ => {
                            Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                                "map requires a function (e.g. fn (x) => (x+1) or sqrt)".to_string(),
                            )))
                        }
                    }
                }
                "sum" => {
                    if !args.is_empty() {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                            "sum takes no arguments".to_string(),
                        )));
                    }
                    let (sum_val, _count) = sum_and_count_vector_stream(
                        db,
                        inner,
                        registry,
                        expr.span(db),
                    )
                    .map_err(|e| with_span_if_missing(e, expr.span(db)))?;
                    Ok(sum_val)
                }
                "mean" => {
                    if !args.is_empty() {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                            "mean takes no arguments".to_string(),
                        )));
                    }
                    use futures::stream::StreamExt;
                    let mut stream = vector_into_stream(db, inner);
                    let mut n = 0usize;
                    let mut sum_val = Value::Numeric(Quantity::from_scalar(0.0));
                    futures::executor::block_on(async {
                        while let Some(item) = stream.next().await {
                            let opt = item.map_err(|e| with_span_if_missing(e, expr.span(db)))?;
                            if let Some(v) = opt {
                                n += 1;
                                sum_val = add_values(&sum_val, &v, registry, None, expr.span(db))
                                    .map_err(|e| with_span_if_missing(e, expr.span(db)))?;
                            }
                        }
                        Ok::<(), RunError>(())
                    })?;
                    if n == 0 {
                        return Err(run_err_with_span(
                            db,
                            expr,
                            RunErrorKind::EmptyVectorReduction("mean".to_string()),
                        ));
                    }
                    let len_val = Value::Numeric(Quantity::from_exact_scalar(n as f64));
                    div_values(&sum_val, &len_val, registry, None, expr.span(db))
                }
                "median" => {
                    if !args.is_empty() {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                            "median takes no arguments".to_string(),
                        )));
                    }
                    if matches!(inner, LazyVector::FromInput(_)) {
                        return Err(run_err_with_span(
                            db,
                            expr,
                            RunErrorKind::InvalidArgument(
                                "median on non-replayable stream requires explicit materialization upstream"
                                    .to_string(),
                            ),
                        ));
                    }
                    let collected = collect_vector_stream(db, inner);
                    median_from_collected(&collected, registry)
                        .map_err(|e| with_span_if_missing(e, expr.span(db)))
                }
                "quantile" => {
                    if args.len() != 1 {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(format!(
                            "quantile requires 1 argument (p in [0,1]), got {}",
                            args.len()
                        ))));
                    }
                    let (_, p_expr) = &args[0];
                    let p_val = value_inner(db, scope, *p_expr, registry)?;
                    let sym_reg = crate::symbol_registry::SymbolRegistry::default_registry();
                    let p_q = p_val.to_quantity(&sym_reg).map_err(|_| {
                        RunError::new(RunErrorKind::InvalidArgument(
                            "quantile: p must be numeric".to_string(),
                        ))
                    })?;
                    let p = p_q.value();
                    if matches!(inner, LazyVector::FromInput(_)) {
                        return Err(run_err_with_span(
                            db,
                            expr,
                            RunErrorKind::InvalidArgument(
                                "quantile on non-replayable stream requires explicit materialization upstream"
                                    .to_string(),
                            ),
                        ));
                    }
                    let collected = collect_vector_stream(db, inner);
                    quantile_from_collected(&collected, p, registry)
                        .map_err(|e| with_span_if_missing(e, expr.span(db)))
                }
                "median_approx" => {
                    if !args.is_empty() {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                            "median_approx takes no arguments".to_string(),
                        )));
                    }
                    quantile_approx_from_stream(db, inner, 0.5, registry, "median_approx")
                        .map_err(|e| with_span_if_missing(e, expr.span(db)))
                }
                "quantile_approx" => {
                    if args.len() != 1 {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(format!(
                            "quantile_approx requires 1 argument (p in [0,1]), got {}",
                            args.len()
                        ))));
                    }
                    let (_, p_expr) = &args[0];
                    let p_val = value_inner(db, scope, *p_expr, registry)?;
                    let sym_reg = crate::symbol_registry::SymbolRegistry::default_registry();
                    let p_q = p_val.to_quantity(&sym_reg).map_err(|_| {
                        RunError::new(RunErrorKind::InvalidArgument(
                            "quantile_approx: p must be numeric".to_string(),
                        ))
                    })?;
                    let p = p_q.value();
                    quantile_approx_from_stream(db, inner, p, registry, "quantile_approx")
                        .map_err(|e| with_span_if_missing(e, expr.span(db)))
                }
                "min" => {
                    if !args.is_empty() {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                            "min takes no arguments".to_string(),
                        )));
                    }
                    use futures::stream::StreamExt;
                    let mut stream = vector_into_stream(db, inner);
                    let mut acc: Option<Quantity> = None;
                    let sym_reg = crate::symbol_registry::SymbolRegistry::default_registry();
                    futures::executor::block_on(async {
                        while let Some(item) = stream.next().await {
                            let opt = item.map_err(|e| with_span_if_missing(e, expr.span(db)))?;
                            let Some(v) = opt else { continue };
                            let q = v.to_quantity(&sym_reg).map_err(|_| {
                                run_err_with_span(
                                    db,
                                    expr,
                                    RunErrorKind::UnknownMethod(
                                        "min: elements must be numeric (same dimension)"
                                            .to_string(),
                                    ),
                                )
                            })?;
                            acc = Some(match acc.take() {
                                None => q,
                                Some(prev) => functions::call_builtin("min", &[prev, q], registry)?
                                    .to_quantity(&sym_reg)
                                    .map_err(|_| {
                                        run_err_with_span(
                                            db,
                                            expr,
                                            RunErrorKind::UnknownMethod(
                                                "min: elements must be numeric (same dimension)"
                                                    .to_string(),
                                            ),
                                        )
                                    })?,
                            });
                        }
                        Ok::<(), RunError>(())
                    })?;
                    match acc {
                        Some(q) => Ok(Value::Numeric(q)),
                        None => Err(run_err_with_span(
                            db,
                            expr,
                            RunErrorKind::EmptyVectorReduction("min".to_string()),
                        )),
                    }
                }
                "max" => {
                    if !args.is_empty() {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                            "max takes no arguments".to_string(),
                        )));
                    }
                    use futures::stream::StreamExt;
                    let mut stream = vector_into_stream(db, inner);
                    let mut acc: Option<Quantity> = None;
                    let sym_reg = crate::symbol_registry::SymbolRegistry::default_registry();
                    futures::executor::block_on(async {
                        while let Some(item) = stream.next().await {
                            let opt = item.map_err(|e| with_span_if_missing(e, expr.span(db)))?;
                            let Some(v) = opt else { continue };
                            let q = v.to_quantity(&sym_reg).map_err(|_| {
                                run_err_with_span(
                                    db,
                                    expr,
                                    RunErrorKind::UnknownMethod(
                                        "max: elements must be numeric (same dimension)"
                                            .to_string(),
                                    ),
                                )
                            })?;
                            acc = Some(match acc.take() {
                                None => q,
                                Some(prev) => functions::call_builtin("max", &[prev, q], registry)?
                                    .to_quantity(&sym_reg)
                                    .map_err(|_| {
                                        run_err_with_span(
                                            db,
                                            expr,
                                            RunErrorKind::UnknownMethod(
                                                "max: elements must be numeric (same dimension)"
                                                    .to_string(),
                                            ),
                                        )
                                    })?,
                            });
                        }
                        Ok::<(), RunError>(())
                    })?;
                    match acc {
                        Some(q) => Ok(Value::Numeric(q)),
                        None => Err(run_err_with_span(
                            db,
                            expr,
                            RunErrorKind::EmptyVectorReduction("max".to_string()),
                        )),
                    }
                }
                "dot" => {
                    if args.len() != 1 {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(format!(
                            "dot requires 1 argument (another vector), got {}",
                            args.len()
                        ))));
                    }
                    let (_, other_expr) = &args[0];
                    let other_val = value_inner(db, scope, *other_expr, registry)?;
                    let VectorValue { inner: other_inner, .. } = match &other_val {
                        Value::Vector(v) => v.clone(),
                        _ => {
                            return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                                "dot requires a vector argument".to_string(),
                            )))
                        }
                    };
                    dot_product_stream(db, inner, other_inner, registry, expr.span(db))
                }
                "norm" => {
                    if !args.is_empty() {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                            "norm takes no arguments".to_string(),
                        )));
                    }
                    use futures::stream::StreamExt;
                    let mut stream = vector_into_stream(db, inner);
                    let mut sum_sq = Value::Numeric(Quantity::from_scalar(0.0));
                    futures::executor::block_on(async {
                        while let Some(item) = stream.next().await {
                            let opt = item.map_err(|e| with_span_if_missing(e, expr.span(db)))?;
                            if let Some(v) = opt {
                                let sq = mul_values(&v, &v, registry, None, expr.span(db))
                                    .map_err(|e| with_span_if_missing(e, expr.span(db)))?;
                                sum_sq = add_values(&sum_sq, &sq, registry, None, expr.span(db))
                                    .map_err(|e| with_span_if_missing(e, expr.span(db)))?;
                            }
                        }
                        Ok::<(), RunError>(())
                    })?;
                    let sym_reg = crate::symbol_registry::SymbolRegistry::default_registry();
                    let sum_sq_q = sum_sq.to_quantity(&sym_reg).map_err(|_| {
                        RunError::new(RunErrorKind::UnknownMethod(
                            "norm: elements must be numeric (same dimension)".to_string(),
                        ))
                    })?;
                    functions::call_builtin("sqrt", &[sum_sq_q], registry)
                }
                "product" => {
                    if !args.is_empty() {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                            "product takes no arguments".to_string(),
                        )));
                    }
                    use futures::stream::StreamExt;
                    let mut stream = vector_into_stream(db, inner);
                    let mut acc = Value::Numeric(Quantity::from_scalar(1.0));
                    futures::executor::block_on(async {
                        while let Some(item) = stream.next().await {
                            let opt = item.map_err(|e| with_span_if_missing(e, expr.span(db)))?;
                            if let Some(v) = opt {
                                acc = mul_values(&acc, &v, registry, None, expr.span(db))
                                    .map_err(|e| with_span_if_missing(e, expr.span(db)))?;
                            }
                        }
                        Ok::<(), RunError>(())
                    })?;
                    Ok(acc)
                }
                "variance" => {
                    if !args.is_empty() {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                            "variance takes no arguments".to_string(),
                        )));
                    }
                    use futures::stream::StreamExt;
                    let mut stream = vector_into_stream(db, inner);
                    let mut n = 0usize;
                    let mut mean: Option<Value> = None;
                    let mut m2 = Value::Numeric(Quantity::from_scalar(0.0));
                    futures::executor::block_on(async {
                        while let Some(item) = stream.next().await {
                            let opt = item.map_err(|e| with_span_if_missing(e, expr.span(db)))?;
                            let Some(x) = opt else { continue };
                            n += 1;
                            if n == 1 {
                                mean = Some(x);
                                continue;
                            }
                            let n_val = Value::Numeric(Quantity::from_exact_scalar(n as f64));
                            let mean_val = mean
                                .clone()
                                .ok_or_else(|| run_err_with_span(db, expr, RunErrorKind::UndefinedResult))?;
                            let delta = sub_values(&x, &mean_val, registry, None, expr.span(db))
                                .map_err(|e| with_span_if_missing(e, expr.span(db)))?;
                            let delta_over_n =
                                div_values(&delta, &n_val, registry, None, expr.span(db))
                                    .map_err(|e| with_span_if_missing(e, expr.span(db)))?;
                            let next_mean =
                                add_values(&mean_val, &delta_over_n, registry, None, expr.span(db))
                                    .map_err(|e| with_span_if_missing(e, expr.span(db)))?;
                            let delta2 = sub_values(&x, &next_mean, registry, None, expr.span(db))
                                .map_err(|e| with_span_if_missing(e, expr.span(db)))?;
                            let prod = mul_values(&delta, &delta2, registry, None, expr.span(db))
                                .map_err(|e| with_span_if_missing(e, expr.span(db)))?;
                            m2 = add_values(&m2, &prod, registry, None, expr.span(db))
                                .map_err(|e| with_span_if_missing(e, expr.span(db)))?;
                            mean = Some(next_mean);
                        }
                        Ok::<(), RunError>(())
                    })?;
                    if n == 0 {
                        return Err(run_err_with_span(
                            db,
                            expr,
                            RunErrorKind::EmptyVectorReduction("variance".to_string()),
                        ));
                    }
                    let n_val = Value::Numeric(Quantity::from_exact_scalar(n as f64));
                    div_values(&m2, &n_val, registry, None, expr.span(db))
                }
                "stddev" => {
                    if !args.is_empty() {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                            "stddev takes no arguments".to_string(),
                        )));
                    }
                    let variance_val = {
                        let variance_expr = ExprData::MethodCall(*base, "variance".to_string(), vec![]);
                        let variance_node = Expression::new(db, variance_expr, expr.span(db));
                        value_inner(db, scope, variance_node, registry)?
                    };
                    let sym_reg =
                        crate::symbol_registry::SymbolRegistry::default_registry();
                    let variance_q = variance_val.to_quantity(&sym_reg).map_err(|_| {
                        RunError::new(RunErrorKind::UnknownMethod(
                            "stddev: elements must be numeric (same dimension)"
                                .to_string(),
                        ))
                    })?;
                    functions::call_builtin("sqrt", &[variance_q], registry)
                }
                "all" => {
                    if !args.is_empty() {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                            "all takes no arguments".to_string(),
                        )));
                    }
                    let mut acc = crate::fuzzy::FuzzyBool::True;
                    use futures::stream::StreamExt;
                    let mut stream = vector_into_stream(db, inner);
                    futures::executor::block_on(async {
                        while let Some(item) = stream.next().await {
                            let opt = item.map_err(|e| with_span_if_missing(e, expr.span(db)))?;
                            let Some(v) = opt else { continue };
                            let f = match v {
                                Value::FuzzyBool(f) => f,
                                _ => {
                                    return Err(run_err_with_span(
                                        db,
                                        expr,
                                        RunErrorKind::UnknownMethod(
                                            "all: elements must be boolean (e.g. from comparison)"
                                                .to_string(),
                                        ),
                                    ))
                                }
                            };
                            acc = acc.clone().and_(&f);
                            if matches!(acc, crate::fuzzy::FuzzyBool::False) {
                                break;
                            }
                        }
                        Ok::<(), RunError>(())
                    })?;
                    Ok(Value::FuzzyBool(acc))
                }
                "any" => {
                    if !args.is_empty() {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                            "any takes no arguments".to_string(),
                        )));
                    }
                    let mut acc = crate::fuzzy::FuzzyBool::False;
                    use futures::stream::StreamExt;
                    let mut stream = vector_into_stream(db, inner);
                    futures::executor::block_on(async {
                        while let Some(item) = stream.next().await {
                            let opt = item.map_err(|e| with_span_if_missing(e, expr.span(db)))?;
                            let Some(v) = opt else { continue };
                            let f = match v {
                                Value::FuzzyBool(f) => f,
                                _ => {
                                    return Err(run_err_with_span(
                                        db,
                                        expr,
                                        RunErrorKind::UnknownMethod(
                                            "any: elements must be boolean (e.g. from comparison)"
                                                .to_string(),
                                        ),
                                    ))
                                }
                            };
                            acc = acc.clone().or_(&f);
                            if matches!(acc, crate::fuzzy::FuzzyBool::True) {
                                break;
                            }
                        }
                        Ok::<(), RunError>(())
                    })?;
                    Ok(Value::FuzzyBool(acc))
                }
                _ => Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(name.clone()))),
            }
        }
        ExprData::Index(base, key_string) => {
            let base_val = value_inner(db, scope, *base, registry)?;
            let env = scope.env(db);
            match &base_val {
                Value::Map(id) => {
                    let v = map_registry::get_key(*id, key_string);
                    Ok(v.unwrap_or(Value::Undefined))
                }
                Value::Vector(v) => {
                    let VectorValue { inner, .. } = v.clone();
                    let index_u = parse_index_key(env, key_string)
                        .map_err(|k| run_err_with_span(db, expr, k))?;
                    match vector_index_stream(db, inner, index_u) {
                        Ok(Some(elem)) => Ok(elem),
                        Ok(None) => Ok(Value::Undefined),
                        Err(kind) => Err(run_err_with_span(db, expr, kind)),
                    }
                }
                _ => Err(run_err_with_span(db, expr, RunErrorKind::ExpectedVector)),
            }
        }
        ExprData::WithPrecision(left, right) => {
            let left_val = value_inner(db, scope, *left, registry)?;
            let right_val = value_inner(db, scope, *right, registry)?;
            let left_q = match &left_val {
                Value::Numeric(q) => q.clone(),
                _ => return Err(run_err_with_span(db, expr, RunErrorKind::TildeRequiresNumeric)),
            };
            let right_central = match &right_val {
                Value::Numeric(rq) => rq.value(),
                _ => return Err(run_err_with_span(db, expr, RunErrorKind::TildeRequiresNumeric)),
            };
            if right_central <= 0.0 || !right_central.is_finite() {
                return Err(run_err_with_span(db, expr, RunErrorKind::PrecisionMustBePositive));
            }
            let variance = right_central * right_central;
            let number = crate::quantity::SnaqNumber::new(left_q.value(), variance);
            Ok(Value::Numeric(crate::quantity::Quantity::with_number(
                number,
                left_q.unit().clone(),
            )))
        }
        ExprData::If(cond_expr, then_expr, else_expr) => {
            eval_if_with(db, scope, *cond_expr, *then_expr, *else_expr, registry, |s, e| value_inner(db, s, e, registry))
                .map_err(|e| with_span_if_missing(e, expr.span(db)))
        }
        ExprData::Block(exprs) => {
            if exprs.is_empty() {
                Ok(Value::Undefined)
            } else {
                let mut current_scope = scope;
                let mut seen_input_names: std::collections::HashSet<String> =
                    std::collections::HashSet::new();
                let n = exprs.len();
                for (i, e) in exprs.iter().enumerate() {
                    match e.data(db) {
                        ExprData::InputDecl(name, _param_id, _type_name) => {
                            if !seen_input_names.insert(name.clone()) {
                                return Err(with_span_if_missing(
                                    RunError::new(RunErrorKind::InvalidArgument(format!(
                                        "duplicate input declaration: {name}"
                                    ))),
                                    e.span(db),
                                ));
                            }
                            // Bind declared input names. Vector-typed declarations stay lazy.
                            // Other declarations preserve scalar-friendly native behavior.
                            let handle_id = STREAM_INPUT_REGISTRY.with(|r| {
                                let reg = r.borrow();
                                reg.as_ref().and_then(|registry| registry.inputs(db).get(name).copied())
                            });
                            #[cfg(not(target_arch = "wasm32"))]
                            let input_value = if let Some(handle_id) = handle_id {
                                if _type_name == "Vector" {
                                    Value::Vector(VectorValue::column(LazyVector::FromInput(handle_id)))
                                } else {
                                    stream_input_to_value(handle_id)
                                        .map_err(|err| with_span_if_missing(err, e.span(db)))?
                                }
                            } else {
                                Value::Undefined
                            };
                            #[cfg(target_arch = "wasm32")]
                            let input_value = if let Some(handle_id) = handle_id {
                                Value::Vector(VectorValue::column(LazyVector::FromInput(handle_id)))
                            } else {
                                Value::Undefined
                            };
                            let stored = StoredValue::from_value(&input_value)
                                .map_err(|err| with_span_if_missing(err, e.span(db)))?;
                            let new_env = current_scope.env(db).clone().extend(name.clone(), stored);
                            current_scope = Scope::new(db, new_env);
                            // Declaration item itself does not produce a value.
                            if i == n - 1 {
                                return Ok(Value::Undefined);
                            }
                        }
                        ExprData::Binding(_, _) => {
                            let (v, new_scope) =
                                eval_binding_chain(db, current_scope, *e, registry)?;
                            current_scope = new_scope;
                            if i == n - 1 {
                                return Ok(v);
                            }
                        }
                        _ => {
                            let val = value_inner(db, current_scope, *e, registry)?;
                            if i == n - 1 {
                                return Ok(val);
                            }
                        }
                    }
                }
                Ok(Value::Undefined)
            }
        }
        ExprData::Binding(_, _) => {
            let (v, _) = eval_binding_chain(db, scope, expr, registry)?;
            Ok(v)
        }
        ExprData::Lambda(params, body) => {
            let params_def: Vec<(String, Option<Box<ExprDef>>)> = params
                .iter()
                .map(|(name, opt_expr)| {
                    (
                        name.clone(),
                        opt_expr.map(|e| Box::new(expression_to_def(db, e))),
                    )
                })
                .collect();
            let body_def = Box::new(expression_to_def(db, *body));
            let closure_env = scope.env(db).clone();
            let closure_env_id = closure_env_register(closure_env);
            let uf = user_function::UserFunction::new(params_def, body_def, closure_env_id);
            Ok(Value::Function(Box::new(uf)))
        }
        ExprData::CallExpr(callee, args) => {
            let callee_val = value_inner(db, scope, *callee, registry)?;
            match &callee_val {
                Value::Function(uf) => eval_user_call_with(db, scope, uf, args, registry, |s, e| value_inner(db, s, e, registry))
                    .map_err(|e| with_span_if_missing(e, expr.span(db))),
                _ => Err(run_err_with_span(
                    db,
                    *callee,
                    RunErrorKind::UnknownFunction(
                        "expression is not callable (expected a function)".to_string(),
                    ),
                )),
            }
        }
    }
}

/// Convert a tracked Expression back to ExprDef (inverse of build_expression).
#[allow(dead_code)]
fn expression_to_def(db: &dyn salsa::Database, expr: Expression<'_>) -> ExprDef {
    match expr.data(db) {
        ExprData::Lit(q) => ExprDef::Lit(q.clone()),
        ExprData::LitFuzzyBool(f) => ExprDef::LitFuzzyBool(f.clone()),
        ExprData::LitSymbol(name) => ExprDef::LitSymbol(name.clone()),
        ExprData::LitDate(gd) => ExprDef::LitDate(gd.clone()),
        ExprData::ExternalStream(name) => ExprDef::ExternalStream(name.clone()),
        ExprData::InputDecl(name, param_id, type_name) => {
            ExprDef::InputDecl(name.clone(), param_id.clone(), type_name.clone())
        }
        ExprData::Add(l, r) => ExprDef::Add(
            Box::new(expression_to_def(db, *l)),
            Box::new(expression_to_def(db, *r)),
        ),
        ExprData::Sub(l, r) => ExprDef::Sub(
            Box::new(expression_to_def(db, *l)),
            Box::new(expression_to_def(db, *r)),
        ),
        ExprData::Mul(l, r) => ExprDef::Mul(
            Box::new(expression_to_def(db, *l)),
            Box::new(expression_to_def(db, *r)),
        ),
        ExprData::Div(l, r) => ExprDef::Div(
            Box::new(expression_to_def(db, *l)),
            Box::new(expression_to_def(db, *r)),
        ),
        ExprData::Eq(l, r) => ExprDef::Eq(
            Box::new(expression_to_def(db, *l)),
            Box::new(expression_to_def(db, *r)),
        ),
        ExprData::Ne(l, r) => ExprDef::Ne(
            Box::new(expression_to_def(db, *l)),
            Box::new(expression_to_def(db, *r)),
        ),
        ExprData::Lt(l, r) => ExprDef::Lt(
            Box::new(expression_to_def(db, *l)),
            Box::new(expression_to_def(db, *r)),
        ),
        ExprData::Le(l, r) => ExprDef::Le(
            Box::new(expression_to_def(db, *l)),
            Box::new(expression_to_def(db, *r)),
        ),
        ExprData::Gt(l, r) => ExprDef::Gt(
            Box::new(expression_to_def(db, *l)),
            Box::new(expression_to_def(db, *r)),
        ),
        ExprData::Ge(l, r) => ExprDef::Ge(
            Box::new(expression_to_def(db, *l)),
            Box::new(expression_to_def(db, *r)),
        ),
        ExprData::And(l, r) => ExprDef::And(
            Box::new(expression_to_def(db, *l)),
            Box::new(expression_to_def(db, *r)),
        ),
        ExprData::Neg(inner) => ExprDef::Neg(Box::new(expression_to_def(db, *inner))),
        ExprData::Call(name, args) => ExprDef::Call(
            name.clone(),
            args.iter()
                .map(|(opt_n, e)| {
                    if let Some(n) = opt_n {
                        CallArg::Named(n.clone(), Box::new(expression_to_def(db, *e)))
                    } else {
                        CallArg::Positional(Box::new(expression_to_def(db, *e)))
                    }
                })
                .collect(),
        ),
        ExprData::As(l, r) => ExprDef::As(
            Box::new(expression_to_def(db, *l)),
            Box::new(expression_to_def(db, *r)),
        ),
        ExprData::VecLiteral(elems) => ExprDef::VecLiteral(
            elems
                .iter()
                .map(|e| expression_to_def(db, *e))
                .collect(),
        ),
        ExprData::MapLiteral(entries) => ExprDef::MapLiteral(
            entries
                .iter()
                .map(|(k, e)| (k.clone(), Box::new(expression_to_def(db, *e))))
                .collect(),
        ),
        ExprData::Transpose(inner) => ExprDef::Transpose(Box::new(expression_to_def(db, *inner))),
        ExprData::Index(base, key) => ExprDef::Index(
            Box::new(expression_to_def(db, *base)),
            key.clone(),
        ),
        ExprData::Member(base, name) => ExprDef::Member(
            Box::new(expression_to_def(db, *base)),
            name.clone(),
        ),
        ExprData::MethodCall(base, name, args) => ExprDef::MethodCall(
            Box::new(expression_to_def(db, *base)),
            name.clone(),
            args.iter()
                .map(|(opt_n, e)| {
                    if let Some(n) = opt_n {
                        CallArg::Named(n.clone(), Box::new(expression_to_def(db, *e)))
                    } else {
                        CallArg::Positional(Box::new(expression_to_def(db, *e)))
                    }
                })
                .collect(),
        ),
        ExprData::WithPrecision(l, r) => ExprDef::WithPrecision(
            Box::new(expression_to_def(db, *l)),
            Box::new(expression_to_def(db, *r)),
        ),
        ExprData::If(c, t, e) => ExprDef::If(
            Box::new(expression_to_def(db, *c)),
            Box::new(expression_to_def(db, *t)),
            Box::new(expression_to_def(db, *e)),
        ),
        ExprData::Block(exprs) => ExprDef::Block(
            exprs
                .iter()
                .map(|e| expression_to_def(db, *e))
                .collect(),
        ),
        ExprData::Binding(name, rhs) => ExprDef::Binding(
            name.clone(),
            Box::new(expression_to_def(db, *rhs)),
        ),
        ExprData::Lambda(params, body) => ExprDef::Lambda(
            params
                .iter()
                .map(|(name, opt_expr)| {
                    (
                        name.clone(),
                        opt_expr.map(|e| Box::new(expression_to_def(db, e))),
                    )
                })
                .collect(),
            Box::new(expression_to_def(db, *body)),
        ),
        ExprData::CallExpr(callee, args) => ExprDef::CallExpr(
            Box::new(expression_to_def(db, *callee)),
            args.iter()
                .map(|(opt_n, e)| {
                    if let Some(n) = opt_n {
                        CallArg::Named(n.clone(), Box::new(expression_to_def(db, *e)))
                    } else {
                        CallArg::Positional(Box::new(expression_to_def(db, *e)))
                    }
                })
                .collect(),
        ),
    }
}

/// Evaluate if/then/else: crisp branch when condition is True/False, superposition when Uncertain(p).
/// Numeric blend converts both branches to a common unit before blending mean and variance.
#[allow(dead_code)]
fn eval_if(
    db: &dyn salsa::Database,
    scope: Scope,
    cond_expr: Expression<'_>,
    then_expr: Expression<'_>,
    else_expr: Expression<'_>,
    registry: &UnitRegistry,
) -> Result<Value, RunError> {
    use crate::fuzzy::FuzzyBool;
    use crate::quantity::SnaqNumber;

    let cond_val = value(db, scope, cond_expr)?;
    let fuzzy = match &cond_val {
        Value::FuzzyBool(f) => f.clone(),
        _ => return Err(RunError::new(RunErrorKind::ExpectedCondition)),
    };

    match &fuzzy {
        FuzzyBool::True => return value(db, scope, then_expr),
        FuzzyBool::False => return value(db, scope, else_expr),
        FuzzyBool::Uncertain(_) => {}
    }

    let p = fuzzy.uncertain_probability().unwrap();
    let then_val = value(db, scope, then_expr)?;
    let else_val = value(db, scope, else_expr)?;

    if matches!(&then_val, Value::FuzzyBool(_) | Value::Vector(_) | Value::Map(_) | Value::Undefined | Value::Date(_) | Value::Function(_) | Value::BuiltinFunction(_))
        || matches!(&else_val, Value::FuzzyBool(_) | Value::Vector(_) | Value::Map(_) | Value::Undefined | Value::Date(_) | Value::Function(_) | Value::BuiltinFunction(_))
    {
        return Err(RunError::new(RunErrorKind::IfBranchTypeMismatch));
    }

    if let (Value::Numeric(qa), Value::Numeric(qb)) = (&then_val, &else_val) {
        if !registry.same_dimension(qa.unit(), qb.unit()).unwrap_or(false) {
            return Err(RunError::new(RunErrorKind::DimensionMismatch {
                left: qa.unit().clone(),
                right: qb.unit().clone(),
            }));
        }
        let result_unit = Quantity::smaller_unit(registry, qa.unit(), qb.unit())
            .cloned()
            .unwrap_or_else(|| qa.unit().clone());
        let qa_c = qa.clone().convert_to(registry, &result_unit).map_err(|e| match e {
            crate::quantity::QuantityError::DimensionMismatch { left, right }
            | crate::quantity::QuantityError::IncompatibleUnits(left, right) => {
RunError::new(RunErrorKind::DimensionMismatch { left, right })
                }
            _ => RunError::new(RunErrorKind::DivisionByZero),
        })?;
        let qb_c = qb.clone().convert_to(registry, &result_unit).map_err(|e| match e {
            crate::quantity::QuantityError::DimensionMismatch { left, right }
            | crate::quantity::QuantityError::IncompatibleUnits(left, right) => {
RunError::new(RunErrorKind::DimensionMismatch { left, right })
                }
            _ => RunError::new(RunErrorKind::DivisionByZero),
        })?;
        let mean_a = qa_c.value();
        let var_a = qa_c.variance();
        let mean_b = qb_c.value();
        let var_b = qb_c.variance();
        let blended_mean = p * mean_a + (1.0 - p) * mean_b;
        let inner_var = p * var_a + (1.0 - p) * var_b;
        let between_var = p * (1.0 - p) * (mean_a - mean_b).powi(2);
        let blended_var = inner_var + between_var;
        let q = Quantity::with_number(
            SnaqNumber::new(blended_mean, blended_var),
            result_unit,
        );
        return Ok(Value::Numeric(q));
    }

    // Build weighted sum as SymbolicExpr (cannot create temp DB inside Salsa query).
    let (ea, ua) = value_to_expr_unit(&then_val)?;
    let (eb, ub) = value_to_expr_unit(&else_val)?;
    if !registry.same_dimension(&ua, &ub).unwrap_or(false) {
        return Err(RunError::new(RunErrorKind::DimensionMismatch {
            left: ua.clone(),
            right: ub.clone(),
        }));
    }
    let result_unit = Quantity::smaller_unit(registry, &ua, &ub)
        .cloned()
        .unwrap_or_else(|| ua.clone());
    let ea_scaled = scale_expr_to_unit(&then_val, &ea, &ua, &result_unit, registry)?;
    let eb_scaled = scale_expr_to_unit(&else_val, &eb, &ub, &result_unit, registry)?;
    let weighted = SymbolicExpr::add(
        &SymbolicExpr::mul(&SymbolicExpr::Number(p), &ea_scaled),
        &SymbolicExpr::mul(&SymbolicExpr::Number(1.0 - p), &eb_scaled),
    );
    Ok(Value::Symbolic(SymbolicQuantity::new(weighted, result_unit)))
}

/// Same as [eval_if] but uses the given evaluator instead of [value], to avoid re-entering [with_registry] (WASM stack).
fn eval_if_with<F>(
    _db: &dyn salsa::Database,
    scope: Scope<'_>,
    cond_expr: Expression<'_>,
    then_expr: Expression<'_>,
    else_expr: Expression<'_>,
    registry: &UnitRegistry,
    mut eval: F,
) -> Result<Value, RunError>
where
    F: FnMut(Scope<'_>, Expression<'_>) -> Result<Value, RunError>,
{
    use crate::fuzzy::FuzzyBool;
    use crate::quantity::SnaqNumber;

    let cond_val = eval(scope, cond_expr)?;
    let fuzzy = match &cond_val {
        Value::FuzzyBool(f) => f.clone(),
        _ => return Err(RunError::new(RunErrorKind::ExpectedCondition)),
    };

    match &fuzzy {
        FuzzyBool::True => return eval(scope, then_expr),
        FuzzyBool::False => return eval(scope, else_expr),
        FuzzyBool::Uncertain(_) => {}
    }

    let p = fuzzy.uncertain_probability().unwrap();
    let then_val = eval(scope, then_expr)?;
    let else_val = eval(scope, else_expr)?;

    if matches!(&then_val, Value::FuzzyBool(_) | Value::Vector(_) | Value::Map(_) | Value::Undefined | Value::Date(_) | Value::Function(_) | Value::BuiltinFunction(_))
        || matches!(&else_val, Value::FuzzyBool(_) | Value::Vector(_) | Value::Map(_) | Value::Undefined | Value::Date(_) | Value::Function(_) | Value::BuiltinFunction(_))
    {
        return Err(RunError::new(RunErrorKind::IfBranchTypeMismatch));
    }

    if let (Value::Numeric(qa), Value::Numeric(qb)) = (&then_val, &else_val) {
        if !registry.same_dimension(qa.unit(), qb.unit()).unwrap_or(false) {
            return Err(RunError::new(RunErrorKind::DimensionMismatch {
                left: qa.unit().clone(),
                right: qb.unit().clone(),
            }));
        }
        let result_unit = Quantity::smaller_unit(registry, qa.unit(), qb.unit())
            .cloned()
            .unwrap_or_else(|| qa.unit().clone());
        let qa_c = qa.clone().convert_to(registry, &result_unit).map_err(|e| match e {
            crate::quantity::QuantityError::DimensionMismatch { left, right }
            | crate::quantity::QuantityError::IncompatibleUnits(left, right) => {
                RunError::new(RunErrorKind::DimensionMismatch { left, right })
            }
            _ => RunError::new(RunErrorKind::DivisionByZero),
        })?;
        let qb_c = qb.clone().convert_to(registry, &result_unit).map_err(|e| match e {
            crate::quantity::QuantityError::DimensionMismatch { left, right }
            | crate::quantity::QuantityError::IncompatibleUnits(left, right) => {
                RunError::new(RunErrorKind::DimensionMismatch { left, right })
            }
            _ => RunError::new(RunErrorKind::DivisionByZero),
        })?;
        let mean_a = qa_c.value();
        let var_a = qa_c.variance();
        let mean_b = qb_c.value();
        let var_b = qb_c.variance();
        let blended_mean = p * mean_a + (1.0 - p) * mean_b;
        let inner_var = p * var_a + (1.0 - p) * var_b;
        let between_var = p * (1.0 - p) * (mean_a - mean_b).powi(2);
        let blended_var = inner_var + between_var;
        let q = Quantity::with_number(
            SnaqNumber::new(blended_mean, blended_var),
            result_unit,
        );
        return Ok(Value::Numeric(q));
    }

    let (ea, ua) = value_to_expr_unit(&then_val)?;
    let (eb, ub) = value_to_expr_unit(&else_val)?;
    if !registry.same_dimension(&ua, &ub).unwrap_or(false) {
        return Err(RunError::new(RunErrorKind::DimensionMismatch {
            left: ua.clone(),
            right: ub.clone(),
        }));
    }
    let result_unit = Quantity::smaller_unit(registry, &ua, &ub)
        .cloned()
        .unwrap_or_else(|| ua.clone());
    let ea_scaled = scale_expr_to_unit(&then_val, &ea, &ua, &result_unit, registry)?;
    let eb_scaled = scale_expr_to_unit(&else_val, &eb, &ub, &result_unit, registry)?;
    let weighted = SymbolicExpr::add(
        &SymbolicExpr::mul(&SymbolicExpr::Number(p), &ea_scaled),
        &SymbolicExpr::mul(&SymbolicExpr::Number(1.0 - p), &eb_scaled),
    );
    Ok(Value::Symbolic(SymbolicQuantity::new(weighted, result_unit)))
}

/// Same as [eval_user_call] but uses the given evaluator instead of [value], to avoid re-entering [with_registry] (WASM stack).
fn eval_user_call_with<F>(
    db: &dyn salsa::Database,
    scope: Scope<'_>,
    uf: &user_function::UserFunction,
    args: &[(Option<String>, Expression<'_>)],
    _registry: &UnitRegistry,
    mut eval: F,
) -> Result<Value, RunError>
where
    F: FnMut(Scope<'_>, Expression<'_>) -> Result<Value, RunError>,
{
    let closure_env = closure_env_get(uf.closure_env_id).ok_or_else(|| {
        RunError::new(RunErrorKind::UnknownFunction("closure env not found (wrong thread or stale id)".to_string()))
    })?;
    let param_names: Vec<String> = uf.params.iter().map(|(n, _)| n.clone()).collect();
    let mut bound: HashMap<String, Value> = HashMap::new();
    for (i, (opt_name, expr)) in args.iter().enumerate() {
        let v = eval(scope, *expr)?;
        let param = match opt_name {
            Some(n) => {
                if !param_names.contains(n) {
                    return Err(run_err_with_span(db, *expr, RunErrorKind::UnknownFunction(format!(
                        "unknown parameter name '{n}'"
                    ))));
                }
                if bound.contains_key(n) {
                    return Err(run_err_with_span(db, *expr, RunErrorKind::UnknownFunction(format!("duplicate parameter '{n}'"))));
                }
                n.clone()
            }
            None => param_names.get(i).cloned().ok_or_else(|| {
                RunError::new(RunErrorKind::UnknownFunction(format!("too many arguments (expected {})", param_names.len())))
            })?,
        };
        bound.insert(param, v);
    }
    let closure_scope = Scope::new(db, closure_env.clone());
    for (name, default) in uf.params.iter() {
        if bound.contains_key(name) {
            continue;
        }
        let default_def = default.as_ref().ok_or_else(|| {
            RunError::new(RunErrorKind::UnknownFunction(format!("missing argument for parameter '{name}'")))
        })?;
        let default_expr = build_expression(db, (**default_def).clone(), None);
        let v = eval(closure_scope, default_expr)?;
        bound.insert(name.clone(), v);
    }
    let mut env = closure_env;
    for (name, v) in &bound {
        let stored = StoredValue::from_value(v)?;
        env = env.extend(name.clone(), stored);
    }
    let body_scope = Scope::new(db, env);
    let body_expr = build_expression(db, *uf.body.clone(), None);
    eval(body_scope, body_expr)
}

/// Evaluate a user-defined function: bind args to params, extend closure env, evaluate body.
#[allow(dead_code)]
fn eval_user_call(
    db: &dyn salsa::Database,
    scope: Scope,
    uf: &user_function::UserFunction,
    args: &[(Option<String>, Expression<'_>)],
    _registry: &UnitRegistry,
) -> Result<Value, RunError> {
    eval_user_call_with(db, scope, uf, args, _registry, |s, e| value(db, s, e))
}

/// Same as [eval_call] but uses the given evaluator instead of [value], to avoid re-entering [with_registry] (WASM stack).
fn eval_call_with<F>(
    db: &dyn salsa::Database,
    scope: Scope<'_>,
    name: &str,
    args: &[(Option<String>, Expression<'_>)],
    registry: &UnitRegistry,
    mut eval: F,
) -> Result<Value, RunError>
where
    F: FnMut(Scope<'_>, Expression<'_>) -> Result<Value, RunError>,
{
    let env = scope.env(db);
    if let Some(StoredValue::Function(uf)) = env.get(name) {
        return eval_user_call_with(db, scope, uf, args, registry, eval);
    }
    let param_names = functions::param_names(name)
        .ok_or_else(|| RunError::new(RunErrorKind::UnknownFunction(name.to_string())))?;
    let mut bound: HashMap<String, Value> = HashMap::new();
    for (i, (opt_name, expr)) in args.iter().enumerate() {
        let v = eval(scope, *expr)?;
        let param = match opt_name {
            Some(n) => {
                if !param_names.contains(&n.as_str()) {
                    return Err(run_err_with_span(db, *expr, RunErrorKind::UnknownFunction(format!(
                        "{name}: unknown parameter name '{n}'"
                    ))));
                }
                if bound.contains_key(n) {
                    return Err(run_err_with_span(db, *expr, RunErrorKind::UnknownFunction(format!(
                        "{name}: duplicate parameter '{n}'"
                    ))));
                }
                n.clone()
            }
            None => {
                param_names
                    .get(i)
                    .copied()
                    .map(String::from)
                    .ok_or_else(|| {
                        RunError::new(RunErrorKind::UnknownFunction(format!(
                            "{name}: too many arguments (expected {})",
                            param_names.len()
                        )))
                    })?
            }
        };
        bound.insert(param, v);
    }
    for p in param_names.iter() {
        if !bound.contains_key(*p) {
            return Err(RunError::new(RunErrorKind::UnknownFunction(format!(
                "{name}: missing argument for parameter '{p}'"
            ))));
        }
    }
    // Unary built-ins (sin, cos, tan, sqrt): map over vector when the single argument is a vector.
    if param_names.len() == 1 && matches!(name, "sin" | "cos" | "tan" | "sqrt" | "cbrt" | "abs" | "sign" | "floor" | "ceil" | "round" | "trunc" | "exp" | "ln" | "log" | "log10" | "log2" | "asin" | "acos" | "atan" | "sinh" | "cosh" | "tanh" | "asinh" | "acosh" | "atanh" | "norm_cdf" | "norm_inv" | "factorial") {
        let v = bound.get(param_names[0]).unwrap();
        if let Value::Vector(v) = v {
            return Ok(Value::Vector(VectorValue {
                inner: LazyVector::Map {
                    source: Box::new(v.inner.clone()),
                    op: VectorMapOp::UnaryFunc(name.to_string()),
                },
                orientation: v.orientation,
            }));
        }
    }
    // corr(a, b): two vectors → Pearson correlation (dimensionless).
    if name == "corr" {
        let a_val = bound.get("a").unwrap();
        let b_val = bound.get("b").unwrap();
        let VectorValue { inner: a_inner, .. } = match a_val {
            Value::Vector(v) => v.clone(),
            _ => return Err(RunError::new(RunErrorKind::ExpectedVector)),
        };
        let VectorValue { inner: b_inner, .. } = match b_val {
            Value::Vector(v) => v.clone(),
            _ => return Err(RunError::new(RunErrorKind::ExpectedVector)),
        };
        let r = pearson_correlation_stream(db, a_inner, b_inner, registry)?;
        return Ok(Value::Numeric(Quantity::new(r, Unit::scalar())));
    }
    // take(vector, start, length): first arg is vector, second and third are non-negative integers.
    if name == "take" {
        let vec_val = bound.get("vector").unwrap();
        let start_val = bound.get("start").unwrap();
        let length_val = bound.get("length").unwrap();
        let VectorValue { inner, orientation } = match vec_val {
            Value::Vector(v) => v.clone(),
            _ => return Err(RunError::new(RunErrorKind::ExpectedVector)),
        };
        let sym_reg = crate::symbol_registry::SymbolRegistry::default_registry();
        let start_q = start_val.to_quantity(&sym_reg).map_err(|_| {
            RunError::new(RunErrorKind::InvalidIndex("start must be numeric".to_string()))
        })?;
        let length_q = length_val.to_quantity(&sym_reg).map_err(|_| {
            RunError::new(RunErrorKind::InvalidIndex("length must be numeric".to_string()))
        })?;
        let start_f = start_q.value();
        let length_f = length_q.value();
        if !start_f.is_finite() || start_f < 0.0 {
            return Err(RunError::new(RunErrorKind::InvalidIndex(
                "start must be a non-negative integer".to_string(),
            )));
        }
        if !length_f.is_finite() || length_f < 0.0 {
            return Err(RunError::new(RunErrorKind::InvalidIndex(
                "length must be a non-negative integer".to_string(),
            )));
        }
        let start_u = start_f as usize;
        let length_u = length_f as usize;
        return Ok(Value::Vector(VectorValue {
            inner: LazyVector::Take {
                source: Box::new(inner),
                start: start_u,
                length: length_u,
            },
            orientation,
        }));
    }
    if bound.values().any(|v| matches!(v, Value::Vector(_))) {
        return Err(RunError::new(RunErrorKind::UnsupportedVectorOperation));
    }
    let sym_reg = crate::symbol_registry::SymbolRegistry::default_registry();
    let param_values: Result<Vec<Quantity>, RunError> = param_names
        .iter()
        .map(|p| {
            let v = bound.get(*p).unwrap();
            v.to_quantity(&sym_reg)
        })
        .collect();
    match param_values {
        Ok(qs) => {
            // For trig at well-known angles, return symbolic exact result when possible.
            if matches!(name, "sin" | "cos" | "tan") && qs.len() == 1 {
                let rad_unit = Unit::from_base_unit("rad");
                if let Ok(in_rad) = qs[0].clone().convert_to(registry, &rad_unit) {
                    let angle_rad = in_rad.value();
                    if let Some(m) = functions::known_angle_from_rad(angle_rad) {
                        let exact = match name {
                            "sin" => Some(functions::exact_sin_match(m)),
                            "cos" => Some(functions::exact_cos_match(m)),
                            "tan" => functions::exact_tan_match(m),
                            _ => unreachable!(),
                        };
                        if let Some(expr) = exact {
                            return Ok(Value::Symbolic(SymbolicQuantity::new(
                                expr,
                                Unit::scalar(),
                            )));
                        }
                        // tan(π/2): fall through to call_builtin
                    }
                }
            }
            functions::call_builtin(name, &qs, registry)
        }
        Err(_) => {
            // Symbolic argument: try exact trig for well-known angle.
            if matches!(name, "sin" | "cos" | "tan") && param_names.len() == 1 {
                let v = bound.get(param_names[0]).unwrap();
                if let Value::Symbolic(sq) = v {
                    if let Some(m) =
                        functions::known_angle_from_symbolic(&sq.expr, &sq.unit, registry)
                    {
                        let exact = match name {
                            "sin" => Some(functions::exact_sin_match(m)),
                            "cos" => Some(functions::exact_cos_match(m)),
                            "tan" => functions::exact_tan_match(m),
                            _ => unreachable!(),
                        };
                        if let Some(expr) = exact {
                            return Ok(Value::Symbolic(SymbolicQuantity::new(
                                expr,
                                Unit::scalar(),
                            )));
                        }
                        // tan(π/2): fall through to symbolic_call
                    }
                }
            }
            let sym_args: Vec<SymbolicExpr> = param_names
                .iter()
                .map(|p| {
                    let v = bound.get(*p).unwrap();
                    value_to_symbolic_expr(v)
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(functions::symbolic_call(name, &sym_args, Unit::scalar()))
        }
    }
}

/// Bind call args (positional + named) to param names and evaluate.
#[allow(dead_code)]
fn eval_call(
    db: &dyn salsa::Database,
    scope: Scope,
    name: &str,
    args: &[(Option<String>, Expression<'_>)],
    registry: &UnitRegistry,
) -> Result<Value, RunError> {
    eval_call_with(db, scope, name, args, registry, |s, e| value(db, s, e))
}

fn value_to_symbolic_expr(v: &Value) -> Result<SymbolicExpr, RunError> {
    match v {
        Value::Numeric(q) => Ok(SymbolicExpr::number(q.value())),
        Value::Symbolic(sq) => Ok(sq.expr.clone()),
        Value::FuzzyBool(_) => Err(RunError::new(RunErrorKind::BooleanResult)),
        Value::Vector(_) => Err(RunError::new(RunErrorKind::UnsupportedVectorOperation)),
        Value::Undefined => Err(RunError::new(RunErrorKind::UndefinedResult)),
        Value::Function(_) | Value::BuiltinFunction(_) => Err(RunError::new(
            RunErrorKind::UnknownFunction("function value not supported here".to_string()),
        )),
        Value::Map(_) => Err(RunError::new(RunErrorKind::UnsupportedVectorOperation)),
        Value::Date(_) => Err(RunError::new(RunErrorKind::InvalidArgument(
            "date not supported here".to_string(),
        ))),
    }
}

/// Sum all elements of a collected vector (for row×column add/sub). Skips None (sparse); empty → 0.
#[allow(dead_code)]
fn sum_vector_elements(
    elems: &[Result<Option<Value>, RunError>],
    registry: &UnitRegistry,
) -> Result<Value, RunError> {
    let mut acc = Value::Numeric(Quantity::from_scalar(0.0));
    for r in elems {
        let opt = r.as_ref().map_err(|e| e.clone())?;
        if let Some(v) = opt {
            acc = add_values(&acc, v, registry, None, None)?;
        }
    }
    Ok(acc)
}

fn sum_and_count_vector_stream(
    db: &dyn salsa::Database,
    v: LazyVector,
    registry: &UnitRegistry,
    span: Option<Span>,
) -> Result<(Value, usize), RunError> {
    use futures::stream::StreamExt;
    let mut stream = vector_into_stream(db, v);
    let mut acc = Value::Numeric(Quantity::from_scalar(0.0));
    let mut count = 0usize;
    futures::executor::block_on(async move {
        while let Some(item) = stream.next().await {
            count += 1;
            let opt = item?;
            if let Some(v) = opt {
                acc = add_values(&acc, &v, registry, None, span)?;
            }
        }
        Ok((acc, count))
    })
}

/// Product of all elements of a collected vector. Skips None (sparse); empty → 1.
#[allow(dead_code)]
fn product_vector_elements(
    elems: &[Result<Option<Value>, RunError>],
    registry: &UnitRegistry,
) -> Result<Value, RunError> {
    let mut acc = Value::Numeric(Quantity::from_scalar(1.0));
    for r in elems {
        let opt = r.as_ref().map_err(|e| e.clone())?;
        if let Some(v) = opt {
            acc = mul_values(&acc, v, registry, None, None)?;
        }
    }
    Ok(acc)
}

/// Population variance (mean of squares minus square of mean) over collected vector elements.
/// Empty or all-sparse → EmptyVectorReduction("variance").
#[allow(dead_code)]
fn compute_variance_value(
    collected: &[Result<Option<Value>, RunError>],
    registry: &UnitRegistry,
) -> Result<Value, RunError> {
    let defined_count = collected
        .iter()
        .filter(|r| r.as_ref().is_ok_and(|o| o.is_some()))
        .count();
    if defined_count == 0 {
        return Err(RunError::new(RunErrorKind::EmptyVectorReduction("variance".to_string())));
    }
    let n = defined_count as f64;
    let sum_x = sum_vector_elements(collected, registry)?;
    let mut sum_sq = Value::Numeric(Quantity::from_scalar(0.0));
    for r in collected {
        let opt = r.as_ref().map_err(|e| e.clone())?;
        if let Some(v) = opt {
            let sq = mul_values(v, v, registry, None, None)?;
            sum_sq = add_values(&sum_sq, &sq, registry, None, None)?;
        }
    }
    let len_val = Value::Numeric(Quantity::from_exact_scalar(n));
    let mean_val = div_values(&sum_x, &len_val, registry, None, None)?;
    let mean_sq_val = div_values(&sum_sq, &len_val, registry, None, None)?;
    let mean_sq_mean = mul_values(&mean_val, &mean_val, registry, None, None)?;
    sub_values(&mean_sq_val, &mean_sq_mean, registry, None, None)
}

/// Pearson correlation of two vectors, streamed in lock-step.
/// Requires same vector length; skips sparse pairs where at least one side is undefined.
fn pearson_correlation_stream(
    db: &dyn salsa::Database,
    a: LazyVector,
    b: LazyVector,
    registry: &UnitRegistry,
) -> Result<f64, RunError> {
    use futures::stream::StreamExt;
    let sym_reg = crate::symbol_registry::SymbolRegistry::default_registry();
    let mut a_stream = vector_into_stream(db, a);
    let mut b_stream = vector_into_stream(db, b);
    let mut left_len = 0usize;
    let mut right_len = 0usize;
    let mut n = 0f64;
    let mut mean_x = 0.0f64;
    let mut mean_y = 0.0f64;
    let mut s_xx = 0.0f64;
    let mut s_yy = 0.0f64;
    let mut s_xy = 0.0f64;
    futures::executor::block_on(async {
        loop {
            let la = a_stream.next().await;
            let rb = b_stream.next().await;
            match (la, rb) {
                (Some(Ok(left_opt)), Some(Ok(right_opt))) => {
                    left_len += 1;
                    right_len += 1;
                    let (Some(left), Some(right)) = (left_opt, right_opt) else {
                        continue;
                    };
                    let qa = left.to_quantity(&sym_reg).map_err(|_| {
                        RunError::new(RunErrorKind::InvalidArgument(
                            "corr: elements must be numeric (same dimension)".to_string(),
                        ))
                    })?;
                    let qb = right.to_quantity(&sym_reg).map_err(|_| {
                        RunError::new(RunErrorKind::InvalidArgument(
                            "corr: elements must be numeric (same dimension)".to_string(),
                        ))
                    })?;
                    if !registry.same_dimension(qa.unit(), qb.unit()).unwrap_or(false) {
                        return Err(RunError::new(RunErrorKind::DimensionMismatch {
                            left: qa.unit().clone(),
                            right: qb.unit().clone(),
                        }));
                    }
                    let common = Quantity::smaller_unit(registry, qa.unit(), qb.unit())
                        .cloned()
                        .unwrap_or_else(|| qa.unit().clone());
                    let x = qa
                        .convert_to(registry, &common)
                        .map_err(|_| {
                            RunError::new(RunErrorKind::DimensionMismatch {
                                left: qa.unit().clone(),
                                right: common.clone(),
                            })
                        })?
                        .value();
                    let y = qb
                        .convert_to(registry, &common)
                        .map_err(|_| {
                            RunError::new(RunErrorKind::DimensionMismatch {
                                left: qb.unit().clone(),
                                right: common.clone(),
                            })
                        })?
                        .value();
                    n += 1.0;
                    let dx = x - mean_x;
                    mean_x += dx / n;
                    let dy = y - mean_y;
                    mean_y += dy / n;
                    s_xx += dx * (x - mean_x);
                    s_yy += dy * (y - mean_y);
                    s_xy += dx * (y - mean_y);
                }
                (Some(Err(e)), _) | (_, Some(Err(e))) => return Err(e),
                (None, None) => break,
                (None, Some(_)) => {
                    return Err(RunError::new(RunErrorKind::VectorLengthMismatch {
                        left_len,
                        right_len: right_len + 1,
                    }));
                }
                (Some(_), None) => {
                    return Err(RunError::new(RunErrorKind::VectorLengthMismatch {
                        left_len: left_len + 1,
                        right_len,
                    }));
                }
            }
        }
        Ok::<(), RunError>(())
    })?;
    if n < 2.0 {
        return Err(RunError::new(RunErrorKind::InvalidArgument(
            "corr: need at least 2 pairs".to_string(),
        )));
    }
    let den = (s_xx * s_yy).sqrt();
    let r = if den > 0.0 { s_xy / den } else { 0.0 };
    Ok(r.clamp(-1.0, 1.0))
}

/// Sorted numeric values from collected vector (same dimension). Errors on non-numeric or dimension mismatch.
fn collected_to_sorted_quantities(
    collected: &[Result<Option<Value>, RunError>],
    registry: &UnitRegistry,
    method: &str,
) -> Result<Vec<Quantity>, RunError> {
    let sym_reg = crate::symbol_registry::SymbolRegistry::default_registry();
    let mut qs: Vec<Quantity> = Vec::new();
    for r in collected {
        let opt = r.as_ref().map_err(|e| e.clone())?;
        let Some(v) = opt else { continue };
        let q = v.to_quantity(&sym_reg).map_err(|_| {
            RunError::new(RunErrorKind::EmptyVectorReduction(format!(
                "{method}: elements must be numeric"
            )))
        })?;
        qs.push(q);
    }
    if qs.is_empty() {
        return Err(RunError::new(RunErrorKind::EmptyVectorReduction(method.to_string())));
    }
    let ref_unit = qs[0].unit().clone();
    for q in &mut qs {
        *q = q.clone().convert_to(registry, &ref_unit).map_err(|_| {
            RunError::new(RunErrorKind::DimensionMismatch {
                left: q.unit().clone(),
                right: ref_unit.clone(),
            })
        })?;
    }
    qs.sort_by(|a, b| a.value().partial_cmp(&b.value()).unwrap_or(std::cmp::Ordering::Equal));
    Ok(qs)
}

/// Median of collected vector (middle value or average of two middles). Same dimension as elements.
fn median_from_collected(
    collected: &[Result<Option<Value>, RunError>],
    registry: &UnitRegistry,
) -> Result<Value, RunError> {
    let qs = collected_to_sorted_quantities(collected, registry, "median")?;
    let n = qs.len();
    let result_q = if n % 2 == 1 {
        qs[n / 2].clone()
    } else {
        let a = qs[n / 2 - 1].value();
        let b = qs[n / 2].value();
        Quantity::new((a + b) / 2.0, qs[0].unit().clone())
    };
    Ok(Value::Numeric(result_q))
}

/// Quantile at p (0 <= p <= 1). Linear interpolation between order statistics.
fn quantile_from_collected(
    collected: &[Result<Option<Value>, RunError>],
    p: f64,
    registry: &UnitRegistry,
) -> Result<Value, RunError> {
    if !(0.0..=1.0).contains(&p) {
        return Err(RunError::new(RunErrorKind::InvalidArgument(
            "quantile: p must be in [0, 1]".to_string(),
        )));
    }
    let qs = collected_to_sorted_quantities(collected, registry, "quantile")?;
    let n = qs.len();
    if n == 1 {
        return Ok(Value::Numeric(qs[0].clone()));
    }
    let idx = p * (n - 1) as f64;
    let lo = idx.floor() as usize;
    let hi = idx.ceil() as usize;
    let lo = lo.min(n - 1);
    let hi = hi.min(n - 1);
    let frac = idx - lo as f64;
    let val = (1.0 - frac) * qs[lo].value() + frac * qs[hi].value();
    Ok(Value::Numeric(Quantity::new(val, qs[0].unit().clone())))
}

fn quantile_approx_from_stream(
    db: &dyn salsa::Database,
    inner: LazyVector,
    p: f64,
    registry: &UnitRegistry,
    method_name: &str,
) -> Result<Value, RunError> {
    if !(0.0..=1.0).contains(&p) {
        return Err(RunError::new(RunErrorKind::InvalidArgument(format!(
            "{method_name}: p must be in [0, 1]"
        ))));
    }
    use futures::stream::StreamExt;
    const RESERVOIR_SIZE: usize = 1024;
    let mut stream = vector_into_stream(db, inner);
    let sym_reg = crate::symbol_registry::SymbolRegistry::default_registry();
    let mut count: u64 = 0;
    let mut rng_state: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut ref_unit: Option<Unit> = None;
    let mut sample: Vec<Quantity> = Vec::with_capacity(RESERVOIR_SIZE);
    futures::executor::block_on(async {
        while let Some(item) = stream.next().await {
            let opt = item?;
            let Some(v) = opt else { continue };
            let mut q = v.to_quantity(&sym_reg).map_err(|_| {
                RunError::new(RunErrorKind::UnknownMethod(format!(
                    "{method_name}: elements must be numeric (same dimension)"
                )))
            })?;
            if let Some(unit) = &ref_unit {
                q = q.convert_to(registry, unit).map_err(|_| {
                    RunError::new(RunErrorKind::DimensionMismatch {
                        left: q.unit().clone(),
                        right: unit.clone(),
                    })
                })?;
            } else {
                ref_unit = Some(q.unit().clone());
            }
            count = count.saturating_add(1);
            if sample.len() < RESERVOIR_SIZE {
                sample.push(q);
            } else {
                // Deterministic xorshift-based reservoir sampling.
                rng_state ^= rng_state << 13;
                rng_state ^= rng_state >> 7;
                rng_state ^= rng_state << 17;
                let j = (rng_state % count.max(1)) as usize;
                if j < RESERVOIR_SIZE {
                    sample[j] = q;
                }
            }
        }
        Ok::<(), RunError>(())
    })?;
    if sample.is_empty() {
        return Err(RunError::new(RunErrorKind::EmptyVectorReduction(
            method_name.to_string(),
        )));
    }
    sample.sort_by(|a, b| a.value().partial_cmp(&b.value()).unwrap_or(std::cmp::Ordering::Equal));
    let n = sample.len();
    let idx = p * (n.saturating_sub(1)) as f64;
    let lo = idx.floor() as usize;
    let hi = idx.ceil() as usize;
    let lo = lo.min(n - 1);
    let hi = hi.min(n - 1);
    let frac = idx - lo as f64;
    let val = (1.0 - frac) * sample[lo].value() + frac * sample[hi].value();
    Ok(Value::Numeric(Quantity::new(
        val,
        sample[0].unit().clone(),
    )))
}

/// Min or max over collected vector elements (numeric only). Empty → EmptyVectorReduction.
#[allow(dead_code)]
fn reduce_min_max(
    elems: &[Result<Option<Value>, RunError>],
    registry: &UnitRegistry,
    is_max: bool,
    method_name: &str,
) -> Result<Value, RunError> {
    let sym_reg = crate::symbol_registry::SymbolRegistry::default_registry();
    let values: Vec<Value> = elems
        .iter()
        .filter_map(|r| r.as_ref().ok().and_then(|o| o.clone()))
        .collect();
    if values.is_empty() {
        return Err(RunError::new(RunErrorKind::EmptyVectorReduction(method_name.to_string())));
    }
    let name = if is_max { "max" } else { "min" };
    let mut acc_q = values[0].clone().to_quantity(&sym_reg).map_err(|_| {
        RunError::new(RunErrorKind::UnknownMethod(format!(
            "{method_name}: elements must be numeric (same dimension)"
        )))
    })?;
    for v in values.iter().skip(1) {
        let q = v.to_quantity(&sym_reg).map_err(|_| {
            RunError::new(RunErrorKind::UnknownMethod(format!(
                "{method_name}: elements must be numeric (same dimension)"
            )))
        })?;
        let result = functions::call_builtin(name, &[acc_q, q], registry)?;
        acc_q = result.to_quantity(&sym_reg).map_err(|_| {
            RunError::new(RunErrorKind::UnknownMethod(format!(
                "{method_name}: elements must be numeric (same dimension)"
            )))
        })?;
    }
    Ok(Value::Numeric(acc_q))
}

/// Comparison operator used by [cmp_values].
#[derive(Clone, Copy, Debug)]
enum CmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

fn cmp_op_to_map_op(op: CmpOp, scalar: &Value) -> VectorMapOp {
    match op {
        CmpOp::Eq => VectorMapOp::Eq(Box::new(scalar.clone())),
        CmpOp::Ne => VectorMapOp::Ne(Box::new(scalar.clone())),
        CmpOp::Lt => VectorMapOp::Lt(Box::new(scalar.clone())),
        CmpOp::Le => VectorMapOp::Le(Box::new(scalar.clone())),
        CmpOp::Gt => VectorMapOp::Gt(Box::new(scalar.clone())),
        CmpOp::Ge => VectorMapOp::Ge(Box::new(scalar.clone())),
    }
}

fn cmp_op_to_binary_op(op: CmpOp) -> VectorBinaryOp {
    match op {
        CmpOp::Eq => VectorBinaryOp::Eq,
        CmpOp::Ne => VectorBinaryOp::Ne,
        CmpOp::Lt => VectorBinaryOp::Lt,
        CmpOp::Le => VectorBinaryOp::Le,
        CmpOp::Gt => VectorBinaryOp::Gt,
        CmpOp::Ge => VectorBinaryOp::Ge,
    }
}

/// Compare two values with the same dimension; returns `Value::FuzzyBool`.
/// Vector×scalar → broadcast (Map); vector×vector → element-wise (ZipMap), outer (Outer), or
/// row×column reduce-then-compare; scalar×scalar → Bool or Symbolic comparison expr.
fn cmp_values(
    op: CmpOp,
    a: &Value,
    b: &Value,
    registry: &UnitRegistry,
    db: Option<&dyn salsa::Database>,
    span: Option<Span>,
) -> Result<Value, RunError> {
    let err = |kind: RunErrorKind| match span {
        Some(s) => RunError::at(s, kind),
        None => RunError::new(kind),
    };
    match (a, b) {
        (Value::Vector(v), scalar) | (scalar, Value::Vector(v))
            if !matches!(scalar, Value::Vector(_)) =>
        {
            Ok(Value::Vector(VectorValue {
                inner: LazyVector::Map {
                    source: Box::new(v.inner.clone()),
                    op: cmp_op_to_map_op(op, scalar),
                },
                orientation: v.orientation,
            }))
        }
        (Value::Vector(left), Value::Vector(right)) => {
            let db = db.ok_or(err(RunErrorKind::UnsupportedVectorOperation))?;
            let bin_op = cmp_op_to_binary_op(op);
            match (left.orientation, right.orientation) {
                (VectorOrientation::Column, VectorOrientation::Column) => Ok(Value::Vector(
                    VectorValue {
                        inner: LazyVector::ZipMap {
                            left: Box::new(left.inner.clone()),
                            right: Box::new(right.inner.clone()),
                            op: bin_op,
                        },
                        orientation: VectorOrientation::Column,
                    },
                )),
                (VectorOrientation::Row, VectorOrientation::Row) => Ok(Value::Vector(
                    VectorValue {
                        inner: LazyVector::ZipMap {
                            left: Box::new(left.inner.clone()),
                            right: Box::new(right.inner.clone()),
                            op: bin_op,
                        },
                        orientation: VectorOrientation::Row,
                    },
                )),
                (VectorOrientation::Column, VectorOrientation::Row) => Ok(Value::Vector(
                    VectorValue {
                        inner: LazyVector::Outer {
                            left: Box::new(left.inner.clone()),
                            right: Box::new(right.inner.clone()),
                            op: bin_op,
                        },
                        orientation: VectorOrientation::Column,
                    },
                )),
                (VectorOrientation::Row, VectorOrientation::Column) => {
                    let (sum_left, left_len) =
                        sum_and_count_vector_stream(db, left.inner.clone(), registry, span)?;
                    let (sum_right, right_len) =
                        sum_and_count_vector_stream(db, right.inner.clone(), registry, span)?;
                    if left_len != right_len {
                        return Err(err(RunErrorKind::VectorLengthMismatch {
                            left_len,
                            right_len,
                        }));
                    }
                    cmp_values(op, &sum_left, &sum_right, registry, None, span)
                }
            }
        }
        (Value::Date(a), Value::Date(b)) => {
            let a_min = a.min_epoch_sec();
            let a_max = a.max_epoch_sec();
            let b_min = b.min_epoch_sec();
            let b_max = b.max_epoch_sec();
            let fuzzy = if a_max < b_min {
                // A strictly before B
                match op {
                    CmpOp::Lt | CmpOp::Le => crate::fuzzy::FuzzyBool::True,
                    CmpOp::Gt | CmpOp::Ge | CmpOp::Eq => crate::fuzzy::FuzzyBool::False,
                    CmpOp::Ne => crate::fuzzy::FuzzyBool::True,
                }
            } else if a_min > b_max {
                // A strictly after B
                match op {
                    CmpOp::Gt | CmpOp::Ge => crate::fuzzy::FuzzyBool::True,
                    CmpOp::Lt | CmpOp::Le | CmpOp::Eq => crate::fuzzy::FuzzyBool::False,
                    CmpOp::Ne => crate::fuzzy::FuzzyBool::True,
                }
            } else {
                // Intervals overlap → uncertain
                crate::fuzzy::FuzzyBool::Uncertain(ordered_float::OrderedFloat::from(0.5))
            };
            Ok(Value::FuzzyBool(fuzzy))
        }
        (Value::Numeric(qa), Value::Numeric(qb)) => {
            if !registry.same_dimension(qa.unit(), qb.unit()).unwrap_or(false) {
                return Err(err(RunErrorKind::DimensionMismatch {
                    left: qa.unit().clone(),
                    right: qb.unit().clone(),
                }));
            }
            let result_unit = Quantity::smaller_unit(registry, qa.unit(), qb.unit())
                .cloned()
                .unwrap_or_else(|| qa.unit().clone());
            let qa_c = qa.clone().convert_to(registry, &result_unit).map_err(|e| match e {
                crate::quantity::QuantityError::DimensionMismatch { left, right } => {
                    err(RunErrorKind::DimensionMismatch { left, right })
                }
                _ => err(RunErrorKind::DivisionByZero),
            })?;
            let qb_c = qb.clone().convert_to(registry, &result_unit).map_err(|e| match e {
                crate::quantity::QuantityError::DimensionMismatch { left, right } => {
                    err(RunErrorKind::DimensionMismatch { left, right })
                }
                _ => err(RunErrorKind::DivisionByZero),
            })?;
            let na = qa_c.number;
            let nb = qb_c.number;
            let kind = match op {
                CmpOp::Eq => ComparisonKind::Eq,
                CmpOp::Ne => ComparisonKind::Ne,
                CmpOp::Lt => ComparisonKind::Lt,
                CmpOp::Le => ComparisonKind::Le,
                CmpOp::Gt => ComparisonKind::Gt,
                CmpOp::Ge => ComparisonKind::Ge,
            };
            let prob = comparison_probability(kind, na, nb);
            let fuzzy = probability_to_fuzzy_bool(prob, CONFIDENCE_THRESHOLD);
            Ok(Value::FuzzyBool(fuzzy))
        }
        (Value::Date(_), _) | (_, Value::Date(_)) => Err(err(RunErrorKind::InvalidArgument(
            "comparison with date requires both operands to be dates".to_string(),
        ))),
        (Value::FuzzyBool(_), _) | (_, Value::FuzzyBool(_)) => Err(err(RunErrorKind::BooleanResult)),
        (Value::Function(_), _) | (_, Value::Function(_)) | (Value::BuiltinFunction(_), _) | (_, Value::BuiltinFunction(_)) => {
            Err(err(RunErrorKind::UnknownFunction("function value cannot be used in comparison".to_string())))
        }
        (Value::Map(_), _) | (_, Value::Map(_)) => Err(err(RunErrorKind::UnsupportedVectorOperation)),
        (Value::Undefined, _) | (_, Value::Undefined) => Err(err(RunErrorKind::UndefinedResult)),
        _ => {
            let (ea, ua) = value_to_expr_unit(a)?;
            let (eb, ub) = value_to_expr_unit(b)?;
            if !registry.same_dimension(&ua, &ub).unwrap_or(false) {
                return Err(err(RunErrorKind::DimensionMismatch {
                    left: ua.clone(),
                    right: ub.clone(),
                }));
            }
            let result_unit = Quantity::smaller_unit(registry, &ua, &ub)
                .cloned()
                .unwrap_or_else(|| ua.clone());
            let ea_scaled = scale_expr_to_unit(a, &ea, &ua, &result_unit, registry)
                .map_err(|e| with_span_if_missing(e, span))?;
            let eb_scaled = scale_expr_to_unit(b, &eb, &ub, &result_unit, registry)
                .map_err(|e| with_span_if_missing(e, span))?;
            let cmp_expr = match op {
                CmpOp::Eq => SymbolicExpr::Eq(Box::new(ea_scaled), Box::new(eb_scaled)),
                CmpOp::Ne => SymbolicExpr::Ne(Box::new(ea_scaled), Box::new(eb_scaled)),
                CmpOp::Lt => SymbolicExpr::Lt(Box::new(ea_scaled), Box::new(eb_scaled)),
                CmpOp::Le => SymbolicExpr::Le(Box::new(ea_scaled), Box::new(eb_scaled)),
                CmpOp::Gt => SymbolicExpr::Gt(Box::new(ea_scaled), Box::new(eb_scaled)),
                CmpOp::Ge => SymbolicExpr::Ge(Box::new(ea_scaled), Box::new(eb_scaled)),
            };
            Ok(Value::Symbolic(SymbolicQuantity::new(
                cmp_expr,
                Unit::scalar(),
            )))
        }
    }
}

fn dot_product_stream(
    db: &dyn salsa::Database,
    left: LazyVector,
    right: LazyVector,
    registry: &UnitRegistry,
    span: Option<Span>,
) -> Result<Value, RunError> {
    use futures::stream::StreamExt;
    let err = |kind: RunErrorKind| match span {
        Some(s) => RunError::at(s, kind),
        None => RunError::new(kind),
    };
    let mut left_stream = vector_into_stream(db, left);
    let mut right_stream = vector_into_stream(db, right);
    let mut left_len = 0usize;
    let mut right_len = 0usize;
    let mut acc = Value::Numeric(Quantity::from_scalar(0.0));
    futures::executor::block_on(async move {
        loop {
            let l = left_stream.next().await;
            let r = right_stream.next().await;
            match (l, r) {
                (Some(Ok(la)), Some(Ok(rb))) => {
                    left_len += 1;
                    right_len += 1;
                    if let (Some(a), Some(b)) = (la, rb) {
                        let product = mul_values(&a, &b, registry, None, span)?;
                        acc = add_values(&acc, &product, registry, None, span)?;
                    }
                }
                (Some(Err(e)), _) | (_, Some(Err(e))) => return Err(e),
                (None, None) => return Ok(acc),
                (None, Some(_)) => {
                    return Err(err(RunErrorKind::VectorLengthMismatch {
                        left_len,
                        right_len: right_len + 1,
                    }))
                }
                (Some(_), None) => {
                    return Err(err(RunErrorKind::VectorLengthMismatch {
                        left_len: left_len + 1,
                        right_len,
                    }))
                }
            }
        }
    })
}

fn add_values(
    a: &Value,
    b: &Value,
    registry: &UnitRegistry,
    db: Option<&dyn salsa::Database>,
    span: Option<Span>,
) -> Result<Value, RunError> {
    let err = |kind: RunErrorKind| match span {
        Some(s) => RunError::at(s, kind),
        None => RunError::new(kind),
    };
    match (a, b) {
        (Value::Vector(v), scalar) | (scalar, Value::Vector(v))
            if !matches!(scalar, Value::Vector(_)) =>
        {
            Ok(Value::Vector(VectorValue {
                inner: LazyVector::Map {
                    source: Box::new(v.inner.clone()),
                    op: VectorMapOp::Add(Box::new(scalar.clone())),
                },
                orientation: v.orientation,
            }))
        }
        (Value::Vector(left), Value::Vector(right)) => {
            let db = db.ok_or(err(RunErrorKind::UnsupportedVectorOperation))?;
            match (left.orientation, right.orientation) {
                (VectorOrientation::Column, VectorOrientation::Column) => Ok(Value::Vector(
                    VectorValue {
                        inner: LazyVector::ZipMap {
                            left: Box::new(left.inner.clone()),
                            right: Box::new(right.inner.clone()),
                            op: VectorBinaryOp::Add,
                        },
                        orientation: VectorOrientation::Column,
                    },
                )),
                (VectorOrientation::Row, VectorOrientation::Row) => Ok(Value::Vector(
                    VectorValue {
                        inner: LazyVector::ZipMap {
                            left: Box::new(left.inner.clone()),
                            right: Box::new(right.inner.clone()),
                            op: VectorBinaryOp::Add,
                        },
                        orientation: VectorOrientation::Row,
                    },
                )),
                (VectorOrientation::Column, VectorOrientation::Row) => Ok(Value::Vector(
                    VectorValue {
                        inner: LazyVector::Outer {
                            left: Box::new(left.inner.clone()),
                            right: Box::new(right.inner.clone()),
                            op: VectorBinaryOp::Add,
                        },
                        orientation: VectorOrientation::Column,
                    },
                )),
                (VectorOrientation::Row, VectorOrientation::Column) => {
                    let (sum_left, left_len) =
                        sum_and_count_vector_stream(db, left.inner.clone(), registry, span)?;
                    let (sum_right, right_len) =
                        sum_and_count_vector_stream(db, right.inner.clone(), registry, span)?;
                    if left_len != right_len {
                        return Err(err(RunErrorKind::VectorLengthMismatch {
                            left_len,
                            right_len,
                        }));
                    }
                    add_values(&sum_left, &sum_right, registry, None, span)
                }
            }
        }
        (Value::Date(d), Value::Numeric(q)) | (Value::Numeric(q), Value::Date(d)) => {
            let sec_unit = Unit::from_base_unit("s");
            if !registry.same_dimension(q.unit(), &sec_unit).unwrap_or(false) {
                return Err(err(RunErrorKind::DimensionMismatch {
                    left: q.unit().clone(),
                    right: sec_unit,
                }));
            }
            let duration_grain = d.grain();
            let unit_grain = q.unit().iter()
                .filter_map(|f| crate::date::grain_for_time_unit_name(&f.unit_name))
                .max_by(|a, b| a.strictness().cmp(&b.strictness()));
            let Some(dur_grain) = unit_grain else {
                return Err(err(RunErrorKind::IncompatibleDateGrain(
                    "duration unit could not be mapped to a grain".to_string(),
                )));
            };
            if !duration_grain.at_least_as_fine_as(dur_grain) {
                return Err(err(RunErrorKind::IncompatibleDateGrain(
                    format!("date grain {duration_grain:?} is coarser than duration grain {dur_grain:?}"),
                )));
            }
            let (_, factor) = registry.to_base_unit_representation(q.unit()).ok_or_else(|| {
                err(RunErrorKind::DimensionMismatch {
                    left: q.unit().clone(),
                    right: sec_unit,
                })
            })?;
            let secs = q.value() * factor;
            // Truncate to i64 for second-scale arithmetic; sub-second duration is not used with current grains.
            let new_anchor = d.anchor_epoch_sec() + secs as i64;
            Ok(Value::Date(d.clone().with_anchor_epoch_sec(new_anchor)))
        }
        (Value::Numeric(qa), Value::Numeric(qb)) => qa
            .clone()
            .add(qb, registry)
            .map(Value::Numeric)
            .map_err(|e| match e {
                crate::quantity::QuantityError::DimensionMismatch { left, right } => {
                    err(RunErrorKind::DimensionMismatch { left, right })
                }
                _ => err(RunErrorKind::DivisionByZero),
            }),
        (Value::FuzzyBool(_), _) | (_, Value::FuzzyBool(_)) => Err(err(RunErrorKind::BooleanResult)),
        (Value::Function(_), _) | (_, Value::Function(_)) | (Value::BuiltinFunction(_), _) | (_, Value::BuiltinFunction(_)) => {
            Err(err(RunErrorKind::UnknownFunction("function value cannot be used in arithmetic".to_string())))
        }
        (Value::Map(_), _) | (_, Value::Map(_)) => Err(err(RunErrorKind::UnsupportedVectorOperation)),
        (Value::Undefined, _) | (_, Value::Undefined) => Err(err(RunErrorKind::UndefinedResult)),
        (Value::Date(_), _) | (_, Value::Date(_)) => Err(err(RunErrorKind::InvalidArgument(
            "date only supports + duration, - duration, or date - date".to_string(),
        ))),
        _ => {
            let (ea, ua) = value_to_expr_unit(a)?;
            let (eb, ub) = value_to_expr_unit(b)?;
            if !registry.same_dimension(&ua, &ub).unwrap_or(false) {
                return Err(err(RunErrorKind::DimensionMismatch {
                    left: ua.clone(),
                    right: ub.clone(),
                }));
            }
            let result_unit = Quantity::smaller_unit(registry, &ua, &ub)
                .cloned()
                .unwrap_or_else(|| ua.clone());
            let ea_scaled = scale_expr_to_unit(a, &ea, &ua, &result_unit, registry)
                .map_err(|e| with_span_if_missing(e, span))?;
            let eb_scaled = scale_expr_to_unit(b, &eb, &ub, &result_unit, registry)
                .map_err(|e| with_span_if_missing(e, span))?;
            Ok(Value::Symbolic(SymbolicQuantity::new(
                SymbolicExpr::add(&ea_scaled, &eb_scaled),
                result_unit,
            )))
        }
    }
}

fn sub_values(
    a: &Value,
    b: &Value,
    registry: &UnitRegistry,
    db: Option<&dyn salsa::Database>,
    span: Option<Span>,
) -> Result<Value, RunError> {
    let err = |kind: RunErrorKind| match span {
        Some(s) => RunError::at(s, kind),
        None => RunError::new(kind),
    };
    match (a, b) {
        (Value::Vector(v), scalar) if !matches!(scalar, Value::Vector(_)) => {
            Ok(Value::Vector(VectorValue {
                inner: LazyVector::Map {
                    source: Box::new(v.inner.clone()),
                    op: VectorMapOp::SubRhs(Box::new(scalar.clone())),
                },
                orientation: v.orientation,
            }))
        }
        (scalar, Value::Vector(v)) if !matches!(scalar, Value::Vector(_)) => {
            Ok(Value::Vector(VectorValue {
                inner: LazyVector::Map {
                    source: Box::new(v.inner.clone()),
                    op: VectorMapOp::SubLhs(Box::new(scalar.clone())),
                },
                orientation: v.orientation,
            }))
        }
        (Value::Vector(left), Value::Vector(right)) => {
            let db = db.ok_or(err(RunErrorKind::UnsupportedVectorOperation))?;
            match (left.orientation, right.orientation) {
                (VectorOrientation::Column, VectorOrientation::Column) => Ok(Value::Vector(
                    VectorValue {
                        inner: LazyVector::ZipMap {
                            left: Box::new(left.inner.clone()),
                            right: Box::new(right.inner.clone()),
                            op: VectorBinaryOp::Sub,
                        },
                        orientation: VectorOrientation::Column,
                    },
                )),
                (VectorOrientation::Row, VectorOrientation::Row) => Ok(Value::Vector(
                    VectorValue {
                        inner: LazyVector::ZipMap {
                            left: Box::new(left.inner.clone()),
                            right: Box::new(right.inner.clone()),
                            op: VectorBinaryOp::Sub,
                        },
                        orientation: VectorOrientation::Row,
                    },
                )),
                (VectorOrientation::Column, VectorOrientation::Row) => Ok(Value::Vector(
                    VectorValue {
                        inner: LazyVector::Outer {
                            left: Box::new(left.inner.clone()),
                            right: Box::new(right.inner.clone()),
                            op: VectorBinaryOp::Sub,
                        },
                        orientation: VectorOrientation::Column,
                    },
                )),
                (VectorOrientation::Row, VectorOrientation::Column) => {
                    let (sum_left, left_len) =
                        sum_and_count_vector_stream(db, left.inner.clone(), registry, span)?;
                    let (sum_right, right_len) =
                        sum_and_count_vector_stream(db, right.inner.clone(), registry, span)?;
                    if left_len != right_len {
                        return Err(err(RunErrorKind::VectorLengthMismatch {
                            left_len,
                            right_len,
                        }));
                    }
                    sub_values(&sum_left, &sum_right, registry, None, span)
                }
            }
        }
        (Value::Date(da), Value::Date(db)) => {
            let span_sec = da.anchor_epoch_sec() - db.anchor_epoch_sec();
            Ok(Value::Numeric(Quantity::new(
                span_sec as f64,
                Unit::from_base_unit("s"),
            )))
        }
        (Value::Date(_d), Value::Numeric(q)) => {
            add_values(a, &Value::Numeric(q.clone().neg()), registry, db, span)
        }
        (Value::Numeric(qa), Value::Numeric(qb)) => qa
            .clone()
            .sub(qb, registry)
            .map(Value::Numeric)
            .map_err(|e| match e {
                crate::quantity::QuantityError::DimensionMismatch { left, right } => {
                    err(RunErrorKind::DimensionMismatch { left, right })
                }
                _ => err(RunErrorKind::DivisionByZero),
            }),
        (Value::FuzzyBool(_), _) | (_, Value::FuzzyBool(_)) => Err(err(RunErrorKind::BooleanResult)),
        (Value::Function(_), _) | (_, Value::Function(_)) | (Value::BuiltinFunction(_), _) | (_, Value::BuiltinFunction(_)) => {
            Err(err(RunErrorKind::UnknownFunction("function value cannot be used in arithmetic".to_string())))
        }
        (Value::Map(_), _) | (_, Value::Map(_)) => Err(err(RunErrorKind::UnsupportedVectorOperation)),
        (Value::Undefined, _) | (_, Value::Undefined) => Err(err(RunErrorKind::UndefinedResult)),
        (Value::Date(_), _) | (_, Value::Date(_)) => Err(err(RunErrorKind::InvalidArgument(
            "date only supports + duration, - duration, or date - date".to_string(),
        ))),
        _ => {
            let (ea, ua) = value_to_expr_unit(a)?;
            let (eb, ub) = value_to_expr_unit(b)?;
            if !registry.same_dimension(&ua, &ub).unwrap_or(false) {
                return Err(err(RunErrorKind::DimensionMismatch {
                    left: ua.clone(),
                    right: ub.clone(),
                }));
            }
            let result_unit = Quantity::smaller_unit(registry, &ua, &ub)
                .cloned()
                .unwrap_or_else(|| ua.clone());
            let ea_scaled = scale_expr_to_unit(a, &ea, &ua, &result_unit, registry)
                .map_err(|e| with_span_if_missing(e, span))?;
            let eb_scaled = scale_expr_to_unit(b, &eb, &ub, &result_unit, registry)
                .map_err(|e| with_span_if_missing(e, span))?;
            Ok(Value::Symbolic(SymbolicQuantity::new(
                SymbolicExpr::sub(&ea_scaled, &eb_scaled),
                result_unit,
            )))
        }
    }
}

fn mul_values(
    a: &Value,
    b: &Value,
    registry: &UnitRegistry,
    db: Option<&dyn salsa::Database>,
    span: Option<Span>,
) -> Result<Value, RunError> {
    let err = |kind: RunErrorKind| match span {
        Some(s) => RunError::at(s, kind),
        None => RunError::new(kind),
    };
    match (a, b) {
        (Value::Vector(v), scalar) | (scalar, Value::Vector(v))
            if !matches!(scalar, Value::Vector(_)) =>
        {
            Ok(Value::Vector(VectorValue {
                inner: LazyVector::Map {
                    source: Box::new(v.inner.clone()),
                    op: VectorMapOp::Mul(Box::new(scalar.clone())),
                },
                orientation: v.orientation,
            }))
        }
        (Value::Vector(left), Value::Vector(right)) => {
            let db = db.ok_or(err(RunErrorKind::UnsupportedVectorOperation))?;
            match (left.orientation, right.orientation) {
                (VectorOrientation::Column, VectorOrientation::Column) => Ok(Value::Vector(
                    VectorValue {
                        inner: LazyVector::ZipMap {
                            left: Box::new(left.inner.clone()),
                            right: Box::new(right.inner.clone()),
                            op: VectorBinaryOp::Mul,
                        },
                        orientation: VectorOrientation::Column,
                    },
                )),
                (VectorOrientation::Row, VectorOrientation::Row) => Ok(Value::Vector(
                    VectorValue {
                        inner: LazyVector::ZipMap {
                            left: Box::new(left.inner.clone()),
                            right: Box::new(right.inner.clone()),
                            op: VectorBinaryOp::Mul,
                        },
                        orientation: VectorOrientation::Row,
                    },
                )),
                (VectorOrientation::Column, VectorOrientation::Row) => Ok(Value::Vector(
                    VectorValue {
                        inner: LazyVector::Outer {
                            left: Box::new(left.inner.clone()),
                            right: Box::new(right.inner.clone()),
                            op: VectorBinaryOp::Mul,
                        },
                        orientation: VectorOrientation::Column,
                    },
                )),
                (VectorOrientation::Row, VectorOrientation::Column) => {
                    dot_product_stream(db, left.inner.clone(), right.inner.clone(), registry, span)
                }
            }
        }
        (Value::Numeric(qa), Value::Numeric(qb)) => Ok(Value::Numeric(qa.clone() * qb.clone())),
        (Value::FuzzyBool(_), _) | (_, Value::FuzzyBool(_)) => Err(err(RunErrorKind::BooleanResult)),
        (Value::Function(_), _) | (_, Value::Function(_)) | (Value::BuiltinFunction(_), _) | (_, Value::BuiltinFunction(_)) => {
            Err(err(RunErrorKind::UnknownFunction("function value cannot be used in arithmetic".to_string())))
        }
        (Value::Map(_), _) | (_, Value::Map(_)) => Err(err(RunErrorKind::UnsupportedVectorOperation)),
        (Value::Undefined, _) | (_, Value::Undefined) => Err(err(RunErrorKind::UndefinedResult)),
        (Value::Date(_), _) | (_, Value::Date(_)) => Err(err(RunErrorKind::InvalidArgument(
            "date cannot be used in multiplication".to_string(),
        ))),
        _ => {
            let (ea, ua) = value_to_expr_unit(a)?;
            let (eb, ub) = value_to_expr_unit(b)?;
            let unit = ua.clone().mul(&ub);
            Ok(Value::Symbolic(SymbolicQuantity::new(
                SymbolicExpr::mul(&ea, &eb),
                unit,
            )))
        }
    }
}

/// Builds a runtime error with source location when the expression has a span in the DB.
fn run_err_with_span(db: &dyn salsa::Database, expr: Expression<'_>, kind: RunErrorKind) -> RunError {
    match expr.span(db) {
        Some(s) => RunError::at(s, kind),
        None => RunError::new(kind),
    }
}

/// Attach span to an error only when the error has no span and we have one (keeps child spans intact).
/// Attaches a span to a runtime error only when the error has no span yet (e.g. from a subcall).
fn with_span_if_missing(e: RunError, span: Option<Span>) -> RunError {
    if e.span.is_some() {
        e
    } else if let Some(s) = span {
        e.with_span(s)
    } else {
        e
    }
}

fn div_values(
    a: &Value,
    b: &Value,
    registry: &UnitRegistry,
    db: Option<&dyn salsa::Database>,
    span: Option<Span>,
) -> Result<Value, RunError> {
    let err = |kind: RunErrorKind| match span {
        Some(s) => RunError::at(s, kind),
        None => RunError::new(kind),
    };
    match (a, b) {
        (Value::Vector(v), scalar) if !matches!(scalar, Value::Vector(_)) => {
            Ok(Value::Vector(VectorValue {
                inner: LazyVector::Map {
                    source: Box::new(v.inner.clone()),
                    op: VectorMapOp::DivRhs(Box::new(scalar.clone())),
                },
                orientation: v.orientation,
            }))
        }
        (scalar, Value::Vector(v)) if !matches!(scalar, Value::Vector(_)) => {
            Ok(Value::Vector(VectorValue {
                inner: LazyVector::Map {
                    source: Box::new(v.inner.clone()),
                    op: VectorMapOp::DivLhs(Box::new(scalar.clone())),
                },
                orientation: v.orientation,
            }))
        }
        (Value::Vector(left), Value::Vector(right)) => {
            let _db = db.ok_or(err(RunErrorKind::UnsupportedVectorOperation))?;
            match (left.orientation, right.orientation) {
                (VectorOrientation::Column, VectorOrientation::Column) => Ok(Value::Vector(
                    VectorValue {
                        inner: LazyVector::ZipMap {
                            left: Box::new(left.inner.clone()),
                            right: Box::new(right.inner.clone()),
                            op: VectorBinaryOp::Div,
                        },
                        orientation: VectorOrientation::Column,
                    },
                )),
                (VectorOrientation::Row, VectorOrientation::Row) => Ok(Value::Vector(
                    VectorValue {
                        inner: LazyVector::ZipMap {
                            left: Box::new(left.inner.clone()),
                            right: Box::new(right.inner.clone()),
                            op: VectorBinaryOp::Div,
                        },
                        orientation: VectorOrientation::Row,
                    },
                )),
                (VectorOrientation::Column, VectorOrientation::Row) => Ok(Value::Vector(
                    VectorValue {
                        inner: LazyVector::Outer {
                            left: Box::new(left.inner.clone()),
                            right: Box::new(right.inner.clone()),
                            op: VectorBinaryOp::Div,
                        },
                        orientation: VectorOrientation::Column,
                    },
                )),
                (VectorOrientation::Row, VectorOrientation::Column) => {
                    let _ = registry;
                    Err(err(RunErrorKind::UnsupportedVectorOperation))
                }
            }
        }
        (Value::Numeric(qa), Value::Numeric(qb)) => (qa.clone() / qb.clone())
            .map(Value::Numeric)
            .map_err(|_| err(RunErrorKind::DivisionByZero)),
        (Value::FuzzyBool(_), _) | (_, Value::FuzzyBool(_)) => Err(err(RunErrorKind::BooleanResult)),
        (Value::Function(_), _) | (_, Value::Function(_)) | (Value::BuiltinFunction(_), _) | (_, Value::BuiltinFunction(_)) => {
            Err(err(RunErrorKind::UnknownFunction("function value cannot be used in arithmetic".to_string())))
        }
        (Value::Map(_), _) | (_, Value::Map(_)) => Err(err(RunErrorKind::UnsupportedVectorOperation)),
        (Value::Undefined, _) | (_, Value::Undefined) => Err(err(RunErrorKind::UndefinedResult)),
        (Value::Date(_), _) | (_, Value::Date(_)) => Err(err(RunErrorKind::InvalidArgument(
            "date cannot be used in division".to_string(),
        ))),
        _ => {
            let (ea, ua) = value_to_expr_unit(a)?;
            let (eb, ub) = value_to_expr_unit(b)?;
            let unit = ua.clone().div(&ub);
            Ok(Value::Symbolic(SymbolicQuantity::new(
                SymbolicExpr::div(&ea, &eb),
                unit,
            )))
        }
    }
}

fn neg_value(v: &Value, span: Option<Span>) -> Result<Value, RunError> {
    let err = |kind: RunErrorKind| match span {
        Some(s) => RunError::at(s, kind),
        None => RunError::new(kind),
    };
    match v {
        Value::FuzzyBool(_) => Err(err(RunErrorKind::BooleanResult)),
        Value::Function(_) | Value::BuiltinFunction(_) => {
            Err(err(RunErrorKind::UnknownFunction("function value cannot be negated".to_string())))
        }
        Value::Undefined => Err(err(RunErrorKind::UndefinedResult)),
        Value::Vector(v) => Ok(Value::Vector(VectorValue {
            inner: LazyVector::Map {
                source: Box::new(v.inner.clone()),
                op: VectorMapOp::Neg,
            },
            orientation: v.orientation,
        })),
        Value::Numeric(q) => Ok(Value::Numeric(Neg::neg(q.clone()))),
        Value::Symbolic(sq) => Ok(Value::Symbolic(SymbolicQuantity::new(
            SymbolicExpr::neg(&sq.expr),
            sq.unit.clone(),
        ))),
        Value::Map(_) => Err(err(RunErrorKind::UnsupportedVectorOperation)),
        Value::Date(_) => Err(err(RunErrorKind::InvalidArgument(
            "date value cannot be negated".to_string(),
        ))),
    }
}

fn value_to_expr_unit(v: &Value) -> Result<(SymbolicExpr, Unit), RunError> {
    match v {
        Value::Numeric(q) => Ok((SymbolicExpr::number(q.value()), q.unit().clone())),
        Value::Symbolic(sq) => Ok((sq.expr.clone(), sq.unit.clone())),
        Value::FuzzyBool(_) => Err(RunError::new(RunErrorKind::BooleanResult)),
        Value::Vector(_) => Err(RunError::new(RunErrorKind::UnsupportedVectorOperation)),
        Value::Undefined => Err(RunError::new(RunErrorKind::UndefinedResult)),
        Value::Function(_) | Value::BuiltinFunction(_) => Err(RunError::new(
            RunErrorKind::UnknownFunction("function value not supported here".to_string()),
        )),
        Value::Map(_) => Err(RunError::new(RunErrorKind::UnsupportedVectorOperation)),
        Value::Date(_) => Err(RunError::new(RunErrorKind::InvalidArgument(
            "date not supported here".to_string(),
        ))),
    }
}

/// Scale an expression from `from_unit` to `to_unit`. For Numeric, converts the quantity and
/// returns its value as expr; for Symbolic, multiplies expr by the conversion ratio.
fn scale_expr_to_unit(
    v: &Value,
    expr: &SymbolicExpr,
    from_unit: &Unit,
    to_unit: &Unit,
    registry: &UnitRegistry,
) -> Result<SymbolicExpr, RunError> {
    if from_unit == to_unit {
        return Ok(expr.clone());
    }
    let (_, from_factor) = registry
        .to_base_unit_representation(from_unit)
        .ok_or_else(|| RunError::new(RunErrorKind::DimensionMismatch {
            left: from_unit.clone(),
            right: to_unit.clone(),
        }))?;
    let (_, to_factor) = registry
        .to_base_unit_representation(to_unit)
        .ok_or_else(|| RunError::new(RunErrorKind::DimensionMismatch {
            left: from_unit.clone(),
            right: to_unit.clone(),
        }))?;
    let ratio = from_factor / to_factor;
    match v {
        Value::Numeric(q) => {
            let converted = q
                .clone()
                .convert_to(registry, to_unit)
                .map_err(|e| match e {
                    crate::quantity::QuantityError::DimensionMismatch { left, right } => {
RunError::new(RunErrorKind::DimensionMismatch { left, right })
                }
                    _ => RunError::new(RunErrorKind::DivisionByZero),
                })?;
            Ok(SymbolicExpr::number(converted.value()))
        }
        Value::Symbolic(_) => Ok(SymbolicExpr::mul(expr, &SymbolicExpr::number(ratio))),
        Value::FuzzyBool(_) => Err(RunError::new(RunErrorKind::BooleanResult)),
        Value::Vector(_) => Err(RunError::new(RunErrorKind::UnsupportedVectorOperation)),
        Value::Undefined => Err(RunError::new(RunErrorKind::UndefinedResult)),
        Value::Function(_) | Value::BuiltinFunction(_) => Err(RunError::new(RunErrorKind::UnsupportedVectorOperation)),
        Value::Map(_) => Err(RunError::new(RunErrorKind::UnsupportedVectorOperation)),
        Value::Date(_) => Err(RunError::new(RunErrorKind::InvalidArgument(
            "scale_expr_to_unit: date not supported".to_string(),
        ))),
    }
}
