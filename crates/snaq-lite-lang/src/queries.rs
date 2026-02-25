//! Query group: build expression graph and evaluate.
//!
//! When inputs (`ProgramDef`) change, Salsa invalidates only the memoized
//! results that depended on them, so recomputation is incremental.
//! Evaluation returns Value (Numeric or Symbolic).

use crate::error::{RunError, RunErrorKind, Span};
use crate::functions;
use crate::ir::{CallArg, ExprData, ExprDef, Expression, ProgramDef, SpannedExprDef, SpannedExprDefKind};
use crate::scope::{closure_env_get, closure_env_register, Scope, StoredValue};
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
use std::task::{Context, Poll};

thread_local! {
    /// Registry used during evaluation (set by run()).
    static EVAL_REGISTRY: RefCell<Option<UnitRegistry>> = const { RefCell::new(None) };
}

/// Set the unit registry for the current thread (used by run() before evaluation).
pub fn set_eval_registry(registry: UnitRegistry) {
    EVAL_REGISTRY.with(|r| *r.borrow_mut() = Some(registry));
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
/// Collects the source stream in [poll_next] (no blocking), then yields columns if every element was a vector, else yields the same elements (1D identity).
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

/// Unified stream type for vector elements (literal, mapped, empty, transposed, zipped, outer, or take).
pub enum VectorStream<'a> {
    Literal(LiteralVectorStream),
    Mapped(MappedVectorStream<'a>),
    Empty(EmptyVectorStream),
    Transposed(TransposedVectorStream<'a>),
    Zipped(ZippedVectorStream<'a>),
    OuterProduct(OuterProductVectorStream<'a>),
    Take(TakeVectorStream<'a>),
}

impl<'a> futures::stream::Stream for VectorStream<'a> {
    type Item = Result<Option<Value>, RunError>;

    fn poll_next(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Option<Self::Item>> {
        match self.get_mut() {
            VectorStream::Literal(s) => Pin::new(s).poll_next(cx),
            VectorStream::Mapped(s) => Pin::new(s).poll_next(cx),
            VectorStream::Empty(s) => Pin::new(s).poll_next(cx),
            VectorStream::Transposed(s) => Pin::new(s).poll_next(cx),
            VectorStream::Zipped(s) => Pin::new(s).poll_next(cx),
            VectorStream::OuterProduct(s) => Pin::new(s).poll_next(cx),
            VectorStream::Take(s) => Pin::new(s).poll_next(cx),
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
    let scope = Scope::new(db, env);
    let body_expr = build_expression(db, *uf.body.clone(), None);
    value(db, scope, body_expr)
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
    let sym_args = vec![value_to_symbolic_expr(v)];
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
        LazyVector::Map { source, op } => {
            let inner = vector_into_stream(db, *source);
            VectorStream::Mapped(MappedVectorStream {
                inner: Box::new(inner),
                op,
                db: Some(db),
            })
        }
        LazyVector::FromExprs(_) | LazyVector::Transform { .. } => {
            VectorStream::Empty(EmptyVectorStream)
        }
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
fn collect_vector_stream(
    db: &dyn salsa::Database,
    v: LazyVector,
) -> Vec<Result<Option<Value>, RunError>> {
    use futures::stream::StreamExt;
    let stream = vector_into_stream(db, v);
    futures::executor::block_on(async move { stream.collect().await })
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
        ExprDef::Index(base, index) => {
            let (bs, is) = children2(&spanned, |s| {
                if let SpannedExprDefKind::Index(b, i) = &s.value {
                    Some((*b.clone(), *i.clone()))
                } else {
                    None
                }
            });
            let base_expr = build_expression(db, *base, bs);
            let index_expr = build_expression(db, *index, is);
            ExprData::Index(base_expr, index_expr)
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
) -> Result<(Value, Scope<'db>), RunError> {
    match expr.data(db) {
        ExprData::Binding(name, rhs) => {
            if functions::param_names(name).is_some() {
                return Err(run_err_with_span(db, expr, RunErrorKind::CannotObfuscateBuiltin(name.clone())));
            }
            let (v, inner_scope) = eval_binding_chain(db, scope, *rhs)?;
            let stored = StoredValue::from_value(&v)?;
            let new_env = inner_scope.env(db).clone().extend(name.clone(), stored);
            let new_scope = Scope::new(db, new_env);
            Ok((v, new_scope))
        }
        _ => {
            let v = value(db, scope, expr)?;
            Ok((v, scope))
        }
    }
}

/// Evaluate an expression to a Value (Numeric or Symbolic). Uses the registry set by run() (thread-local).
/// Scope is passed so variable lookups and block bindings are memoized per (scope, expr).
#[salsa::tracked]
pub fn value<'db>(
    db: &'db dyn salsa::Database,
    scope: Scope<'db>,
    expr: Expression<'db>,
) -> Result<Value, RunError> {
    let data = expr.data(db);
    let env = scope.env(db);
    with_registry(|registry| match data {
        ExprData::Lit(q) => Ok(Value::Numeric(q.clone())),
        ExprData::LitFuzzyBool(f) => Ok(Value::FuzzyBool(f.clone())),
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
        ExprData::Add(l, r) => {
            let left = value(db, scope, *l)?;
            let right = value(db, scope, *r)?;
            add_values(&left, &right, registry, Some(db), expr.span(db))
        }
        ExprData::Sub(l, r) => {
            let left = value(db, scope, *l)?;
            let right = value(db, scope, *r)?;
            sub_values(&left, &right, registry, Some(db), expr.span(db))
        }
        ExprData::Mul(l, r) => {
            let left = value(db, scope, *l)?;
            let right = value(db, scope, *r)?;
            mul_values(&left, &right, registry, Some(db), expr.span(db))
        }
        ExprData::Div(l, r) => {
            let left = value(db, scope, *l)?;
            let right = value(db, scope, *r)?;
            match div_values(&left, &right, registry, Some(db), expr.span(db)) {
                Ok(v) => Ok(v),
                Err(e) if matches!(e.kind, RunErrorKind::DivisionByZero) => Ok(Value::Undefined),
                Err(e) => Err(e),
            }
        }
        ExprData::Eq(l, r) => {
            let left = value(db, scope, *l)?;
            let right = value(db, scope, *r)?;
            cmp_values(CmpOp::Eq, &left, &right, registry, Some(db), expr.span(db))
        }
        ExprData::Ne(l, r) => {
            let left = value(db, scope, *l)?;
            let right = value(db, scope, *r)?;
            cmp_values(CmpOp::Ne, &left, &right, registry, Some(db), expr.span(db))
        }
        ExprData::Lt(l, r) => {
            let left = value(db, scope, *l)?;
            let right = value(db, scope, *r)?;
            cmp_values(CmpOp::Lt, &left, &right, registry, Some(db), expr.span(db))
        }
        ExprData::Le(l, r) => {
            let left = value(db, scope, *l)?;
            let right = value(db, scope, *r)?;
            cmp_values(CmpOp::Le, &left, &right, registry, Some(db), expr.span(db))
        }
        ExprData::Gt(l, r) => {
            let left = value(db, scope, *l)?;
            let right = value(db, scope, *r)?;
            cmp_values(CmpOp::Gt, &left, &right, registry, Some(db), expr.span(db))
        }
        ExprData::Ge(l, r) => {
            let left = value(db, scope, *l)?;
            let right = value(db, scope, *r)?;
            cmp_values(CmpOp::Ge, &left, &right, registry, Some(db), expr.span(db))
        }
        ExprData::Neg(inner) => {
            let v = value(db, scope, *inner)?;
            neg_value(&v, expr.span(db))
        }
        ExprData::Call(name, args) => eval_call(db, scope, name, args, registry)
            .map_err(|e| with_span_if_missing(e, expr.span(db))),
        ExprData::As(left, right) => {
            let left_val = value(db, scope, *left)?;
            let right_val = value(db, scope, *right)?;
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
                Value::Undefined => Err(run_err_with_span(db, expr, RunErrorKind::UndefinedResult)),
                Value::Function(_) | Value::BuiltinFunction(_) => Err(run_err_with_span(db, expr, RunErrorKind::BindingValueNotSupported(
                    "function value cannot be converted to quantity".to_string(),
                ))),
            }
        }
        ExprData::VecLiteral(exprs) => {
            // Evaluate all elements while we're inside this tracked query (Salsa does not allow
            // creating tracked structs from outside). Store results for lazy streaming.
            let results: Vec<Result<Option<Value>, RunError>> = exprs
                .iter()
                .map(|e| value(db, scope, *e).map(Some))
                .collect();
            Ok(Value::Vector(VectorValue::column(LazyVector::from_evaluated(
                results,
            ))))
        }
        ExprData::Transpose(inner) => {
            let v = value(db, scope, *inner)?;
            match v {
                Value::Vector(v) => Ok(Value::Vector(v.transpose())),
                _ => Err(run_err_with_span(db, expr, RunErrorKind::ExpectedVector)),
            }
        }
        ExprData::Member(base, name) => {
            let base_val = value(db, scope, *base)?;
            let VectorValue { inner, .. } = match &base_val {
                Value::Vector(v) => v.clone(),
                _ => return Err(run_err_with_span(db, expr, RunErrorKind::ExpectedVector)),
            };
            match name.as_str() {
                "length" => {
                    let collected = collect_vector_stream(db, inner);
                    let len = collected.len();
                    Ok(Value::Numeric(Quantity::from_exact_scalar(len as f64)))
                }
                _ => Err(run_err_with_span(db, expr, RunErrorKind::UnknownProperty(name.clone()))),
            }
        }
        ExprData::MethodCall(base, name, args) => {
            let base_val = value(db, scope, *base)?;
            let VectorValue { inner, orientation } = match &base_val {
                Value::Vector(v) => v.clone(),
                _ => return Err(run_err_with_span(db, expr, RunErrorKind::ExpectedVector)),
            };
            match name.as_str() {
                "take" => {
                    let arg_vals: Vec<Value> = args
                        .iter()
                        .map(|(_, e)| value(db, scope, *e))
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
                    let fn_val = value(db, scope, *fn_expr)?;
                    let collected = collect_vector_stream(db, inner);
                    let results: Vec<Result<Option<Value>, RunError>> = match &fn_val {
                        Value::Function(uf) => {
                            // Eager evaluation: we're inside a Salsa query, so we can call value() for each element.
                            collected
                                .into_iter()
                                .map(|r| {
                                    r.and_then(|opt| {
                                        opt.map(|elem| {
                                            apply_user_map_element(db, uf, elem, registry)
                                                .map(Some)
                                        })
                                        .unwrap_or(Ok(None))
                                    })
                                })
                                .collect()
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
                            collected
                                .into_iter()
                                .map(|r| {
                                    r.and_then(|opt| {
                                        opt.map(|elem| {
                                            apply_unary_builtin(name, &elem, registry).map(Some)
                                        })
                                        .unwrap_or(Ok(None))
                                    })
                                })
                                .collect()
                        }
                        _ => {
                            return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                                "map requires a function (e.g. fn (x) => (x+1) or sqrt)".to_string(),
                            )))
                        }
                    };
                    let ok_results: Vec<Option<Value>> = results
                        .into_iter()
                        .collect::<Result<Vec<_>, _>>()
                        .map_err(|e| with_span_if_missing(e, expr.span(db)))?;
                    let results = ok_results.into_iter().map(Ok).collect();
                    Ok(Value::Vector(VectorValue {
                        inner: LazyVector::FromEvaluated(results),
                        orientation,
                    }))
                }
                "sum" => {
                    if !args.is_empty() {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                            "sum takes no arguments".to_string(),
                        )));
                    }
                    let collected = collect_vector_stream(db, inner);
                    let sum_val = sum_vector_elements(&collected, registry)
                        .map_err(|e| with_span_if_missing(e, expr.span(db)))?;
                    Ok(sum_val)
                }
                "mean" => {
                    if !args.is_empty() {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                            "mean takes no arguments".to_string(),
                        )));
                    }
                    let collected = collect_vector_stream(db, inner);
                    let n = collected
                        .iter()
                        .filter(|r| r.as_ref().is_ok_and(|o| o.is_some()))
                        .count();
                    if n == 0 {
                        return Err(run_err_with_span(db, expr, RunErrorKind::EmptyVectorReduction("mean".to_string())));
                    }
                    let sum_val = sum_vector_elements(&collected, registry)
                        .map_err(|e| with_span_if_missing(e, expr.span(db)))?;
                    let len_val = Value::Numeric(Quantity::from_exact_scalar(n as f64));
                    div_values(&sum_val, &len_val, registry, None, expr.span(db))
                }
                "min" => {
                    if !args.is_empty() {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                            "min takes no arguments".to_string(),
                        )));
                    }
                    let collected = collect_vector_stream(db, inner);
                    reduce_min_max(&collected, registry, false, "min")
                        .map_err(|e| with_span_if_missing(e, expr.span(db)))
                }
                "max" => {
                    if !args.is_empty() {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                            "max takes no arguments".to_string(),
                        )));
                    }
                    let collected = collect_vector_stream(db, inner);
                    reduce_min_max(&collected, registry, true, "max")
                        .map_err(|e| with_span_if_missing(e, expr.span(db)))
                }
                "dot" => {
                    if args.len() != 1 {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(format!(
                            "dot requires 1 argument (another vector), got {}",
                            args.len()
                        ))));
                    }
                    let (_, other_expr) = &args[0];
                    let other_val = value(db, scope, *other_expr)?;
                    let VectorValue { inner: other_inner, .. } = match &other_val {
                        Value::Vector(v) => v.clone(),
                        _ => {
                            return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                                "dot requires a vector argument".to_string(),
                            )))
                        }
                    };
                    let left_elems = collect_vector_stream(db, inner);
                    let right_elems = collect_vector_stream(db, other_inner);
                    dot_product(&left_elems, &right_elems, registry, expr.span(db))
                }
                "norm" => {
                    if !args.is_empty() {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                            "norm takes no arguments".to_string(),
                        )));
                    }
                    let collected = collect_vector_stream(db, inner);
                    let mut sum_sq = Value::Numeric(Quantity::from_scalar(0.0));
                    for r in &collected {
                        let opt = r.as_ref().map_err(|e| e.clone())?;
                        if let Some(v) = opt {
                            let sq = mul_values(v, v, registry, None, None)?;
                            sum_sq = add_values(&sum_sq, &sq, registry, None, None)?;
                        }
                    }
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
                    let collected = collect_vector_stream(db, inner);
                    product_vector_elements(&collected, registry)
                        .map_err(|e| with_span_if_missing(e, expr.span(db)))
                }
                "variance" => {
                    if !args.is_empty() {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                            "variance takes no arguments".to_string(),
                        )));
                    }
                    let collected = collect_vector_stream(db, inner);
                    compute_variance_value(&collected, registry)
                        .map_err(|e| with_span_if_missing(e, expr.span(db)))
                }
                "stddev" => {
                    if !args.is_empty() {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                            "stddev takes no arguments".to_string(),
                        )));
                    }
                    let collected = collect_vector_stream(db, inner);
                    let variance_val = compute_variance_value(&collected, registry)
                        .map_err(|e| with_span_if_missing(e, expr.span(db)))?;
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
                    let collected = collect_vector_stream(db, inner);
                    let defined: Vec<Value> = collected
                        .iter()
                        .filter_map(|r| r.as_ref().ok().and_then(|o| o.clone()))
                        .collect();
                    let mut acc = crate::fuzzy::FuzzyBool::True;
                    for v in &defined {
                        let f = match v {
                            Value::FuzzyBool(f) => f.clone(),
                            _ => {
                                return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                                    "all: elements must be boolean (e.g. from comparison)"
                                        .to_string(),
                                )))
                            }
                        };
                        acc = acc.and_(&f);
                    }
                    Ok(Value::FuzzyBool(acc))
                }
                "any" => {
                    if !args.is_empty() {
                        return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                            "any takes no arguments".to_string(),
                        )));
                    }
                    let collected = collect_vector_stream(db, inner);
                    let defined: Vec<Value> = collected
                        .iter()
                        .filter_map(|r| r.as_ref().ok().and_then(|o| o.clone()))
                        .collect();
                    let mut acc = crate::fuzzy::FuzzyBool::False;
                    for v in &defined {
                        let f = match v {
                            Value::FuzzyBool(f) => f.clone(),
                            _ => {
                                return Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(
                                    "any: elements must be boolean (e.g. from comparison)"
                                        .to_string(),
                                )))
                            }
                        };
                        acc = acc.or_(&f);
                    }
                    Ok(Value::FuzzyBool(acc))
                }
                _ => Err(run_err_with_span(db, expr, RunErrorKind::UnknownMethod(name.clone()))),
            }
        }
        ExprData::Index(base, index_expr) => {
            let base_val = value(db, scope, *base)?;
            let VectorValue { inner, .. } = match &base_val {
                Value::Vector(v) => v.clone(),
                _ => return Err(run_err_with_span(db, expr, RunErrorKind::ExpectedVector)),
            };
            let index_val = value(db, scope, *index_expr)?;
            let sym_reg = crate::symbol_registry::SymbolRegistry::default_registry();
            let index_q = index_val.to_quantity(&sym_reg).map_err(|_| {
                RunError::new(RunErrorKind::InvalidIndex("index must be numeric".to_string()))
            })?;
            let index_f = index_q.value();
            if !index_f.is_finite() || index_f < 0.0 {
                return Err(run_err_with_span(db, expr, RunErrorKind::InvalidIndex(
                    "index must be a non-negative integer".to_string(),
                )));
            }
            if index_f.fract() != 0.0 {
                return Err(run_err_with_span(db, expr, RunErrorKind::InvalidIndex(
                    "index must be an integer".to_string(),
                )));
            }
            let index_u = index_f as usize;
            let slice = LazyVector::Take {
                source: Box::new(inner),
                start: index_u,
                length: 1,
            };
            let collected = collect_vector_stream(db, slice);
            if collected.is_empty() {
                return Err(run_err_with_span(db, expr, RunErrorKind::IndexOutOfBounds {
                    index: index_u,
                    length: index_u,
                }));
            }
            match &collected[0] {
                Ok(Some(elem)) => Ok(elem.clone()),
                Ok(None) => Ok(Value::Undefined),
                Err(e) => Err(e.clone()),
            }
        }
        ExprData::WithPrecision(left, right) => {
            let left_val = value(db, scope, *left)?;
            let right_val = value(db, scope, *right)?;
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
            eval_if(db, scope, *cond_expr, *then_expr, *else_expr, registry)
                .map_err(|e| with_span_if_missing(e, expr.span(db)))
        }
        ExprData::Block(exprs) => {
            if exprs.is_empty() {
                Ok(Value::Undefined)
            } else {
                let mut current_scope = scope;
                let n = exprs.len();
                for (i, e) in exprs.iter().enumerate() {
                    match e.data(db) {
                        ExprData::Binding(_, _) => {
                            let (v, new_scope) =
                                eval_binding_chain(db, current_scope, *e)?;
                            current_scope = new_scope;
                            if i == n - 1 {
                                return Ok(v);
                            }
                        }
                        _ => {
                            let val = value(db, current_scope, *e)?;
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
            let (v, _) = eval_binding_chain(db, scope, expr)?;
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
            let callee_val = value(db, scope, *callee)?;
            match &callee_val {
                Value::Function(uf) => eval_user_call(db, scope, uf, args, registry)
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
    })
}

/// Convert a tracked Expression back to ExprDef (inverse of build_expression).
#[allow(dead_code)]
fn expression_to_def(db: &dyn salsa::Database, expr: Expression<'_>) -> ExprDef {
    match expr.data(db) {
        ExprData::Lit(q) => ExprDef::Lit(q.clone()),
        ExprData::LitFuzzyBool(f) => ExprDef::LitFuzzyBool(f.clone()),
        ExprData::LitSymbol(name) => ExprDef::LitSymbol(name.clone()),
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
        ExprData::Transpose(inner) => ExprDef::Transpose(Box::new(expression_to_def(db, *inner))),
        ExprData::Index(base, index) => ExprDef::Index(
            Box::new(expression_to_def(db, *base)),
            Box::new(expression_to_def(db, *index)),
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

    if matches!(&then_val, Value::FuzzyBool(_) | Value::Vector(_))
        || matches!(&else_val, Value::FuzzyBool(_) | Value::Vector(_))
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
    let (ea, ua) = value_to_expr_unit(&then_val);
    let (eb, ub) = value_to_expr_unit(&else_val);
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

/// Evaluate a user-defined function: bind args to params, extend closure env, evaluate body.
fn eval_user_call(
    db: &dyn salsa::Database,
    scope: Scope,
    uf: &user_function::UserFunction,
    args: &[(Option<String>, Expression<'_>)],
    _registry: &UnitRegistry,
) -> Result<Value, RunError> {
    let closure_env = closure_env_get(uf.closure_env_id).ok_or_else(|| {
        RunError::new(RunErrorKind::UnknownFunction("closure env not found (wrong thread or stale id)".to_string()))
    })?;
    let param_names: Vec<String> = uf.params.iter().map(|(n, _)| n.clone()).collect();
    let mut bound: HashMap<String, Value> = HashMap::new();
    for (i, (opt_name, expr)) in args.iter().enumerate() {
        let v = value(db, scope, *expr)?;
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
        let v = value(db, closure_scope, default_expr)?;
        bound.insert(name.clone(), v);
    }
    let mut env = closure_env;
    // Param values must be storable; from_value rejects only Symbolic (Vector is stored via registry).
    for (name, v) in &bound {
        let stored = StoredValue::from_value(v)?;
        env = env.extend(name.clone(), stored);
    }
    let body_scope = Scope::new(db, env);
    let body_expr = build_expression(db, *uf.body.clone(), None);
    value(db, body_scope, body_expr)
}

/// Bind call args (positional + named) to param names and evaluate.
fn eval_call(
    db: &dyn salsa::Database,
    scope: Scope,
    name: &str,
    args: &[(Option<String>, Expression<'_>)],
    registry: &UnitRegistry,
) -> Result<Value, RunError> {
    // Scope first: user-defined function shadows built-in.
    let env = scope.env(db);
    if let Some(StoredValue::Function(uf)) = env.get(name) {
        return eval_user_call(db, scope, uf, args, registry);
    }
    let param_names = functions::param_names(name)
        .ok_or_else(|| RunError::new(RunErrorKind::UnknownFunction(name.to_string())))?;
    let mut bound: HashMap<String, Value> = HashMap::new();
    for (i, (opt_name, expr)) in args.iter().enumerate() {
        let v = value(db, scope, *expr)?;
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
    if param_names.len() == 1 && matches!(name, "sin" | "cos" | "tan" | "sqrt") {
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
                .collect();
            Ok(functions::symbolic_call(name, &sym_args, Unit::scalar()))
        }
    }
}

fn value_to_symbolic_expr(v: &Value) -> SymbolicExpr {
    match v {
        Value::Numeric(q) => SymbolicExpr::number(q.value()),
        Value::Symbolic(sq) => sq.expr.clone(),
        Value::FuzzyBool(_) => panic!("value_to_symbolic_expr: fuzzy boolean not supported"),
        Value::Vector(_) => panic!("value_to_symbolic_expr: vector not supported"),
        Value::Undefined => panic!("value_to_symbolic_expr: undefined not supported"),
        Value::Function(_) | Value::BuiltinFunction(_) => panic!("value_to_symbolic_expr: function not supported"),
    }
}

/// Sum all elements of a collected vector (for row×column add/sub). Skips None (sparse); empty → 0.
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

/// Product of all elements of a collected vector. Skips None (sparse); empty → 1.
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

/// Min or max over collected vector elements (numeric only). Empty → EmptyVectorReduction.
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
                    let left_elems = collect_vector_stream(db, left.inner.clone());
                    let right_elems = collect_vector_stream(db, right.inner.clone());
                    if left_elems.len() != right_elems.len() {
                        return Err(err(RunErrorKind::VectorLengthMismatch {
                            left_len: left_elems.len(),
                            right_len: right_elems.len(),
                        }));
                    }
                    let sum_left = sum_vector_elements(&left_elems, registry)?;
                    let sum_right = sum_vector_elements(&right_elems, registry)?;
                    cmp_values(op, &sum_left, &sum_right, registry, None, span)
                }
            }
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
        (Value::FuzzyBool(_), _) | (_, Value::FuzzyBool(_)) => Err(err(RunErrorKind::BooleanResult)),
        (Value::Function(_), _) | (_, Value::Function(_)) | (Value::BuiltinFunction(_), _) | (_, Value::BuiltinFunction(_)) => {
            Err(err(RunErrorKind::UnknownFunction("function value cannot be used in comparison".to_string())))
        }
        _ => {
            let (ea, ua) = value_to_expr_unit(a);
            let (eb, ub) = value_to_expr_unit(b);
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

/// Dot product of two collected vectors (row×column mul). Returns scalar.
fn dot_product(
    left_elems: &[Result<Option<Value>, RunError>],
    right_elems: &[Result<Option<Value>, RunError>],
    registry: &UnitRegistry,
    span: Option<Span>,
) -> Result<Value, RunError> {
    let err = |kind: RunErrorKind| match span {
        Some(s) => RunError::at(s, kind),
        None => RunError::new(kind),
    };
    if left_elems.len() != right_elems.len() {
        return Err(err(RunErrorKind::VectorLengthMismatch {
            left_len: left_elems.len(),
            right_len: right_elems.len(),
        }));
    }
    let mut acc = Value::Numeric(Quantity::from_scalar(0.0));
    for (l, r) in left_elems.iter().zip(right_elems.iter()) {
        let l_opt = l.as_ref().map_err(|e| e.clone())?;
        let r_opt = r.as_ref().map_err(|e| e.clone())?;
        if let (Some(a), Some(b)) = (l_opt, r_opt) {
            let product = mul_values(a, b, registry, None, span)?;
            acc = add_values(&acc, &product, registry, None, span)?;
        }
    }
    Ok(acc)
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
                    let left_elems = collect_vector_stream(db, left.inner.clone());
                    let right_elems = collect_vector_stream(db, right.inner.clone());
                    if left_elems.len() != right_elems.len() {
                        return Err(err(RunErrorKind::VectorLengthMismatch {
                            left_len: left_elems.len(),
                            right_len: right_elems.len(),
                        }));
                    }
                    let sum_left = sum_vector_elements(&left_elems, registry)?;
                    let sum_right = sum_vector_elements(&right_elems, registry)?;
                    add_values(&sum_left, &sum_right, registry, None, span)
                }
            }
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
        _ => {
            let (ea, ua) = value_to_expr_unit(a);
            let (eb, ub) = value_to_expr_unit(b);
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
                    let left_elems = collect_vector_stream(db, left.inner.clone());
                    let right_elems = collect_vector_stream(db, right.inner.clone());
                    if left_elems.len() != right_elems.len() {
                        return Err(err(RunErrorKind::VectorLengthMismatch {
                            left_len: left_elems.len(),
                            right_len: right_elems.len(),
                        }));
                    }
                    let sum_left = sum_vector_elements(&left_elems, registry)?;
                    let sum_right = sum_vector_elements(&right_elems, registry)?;
                    sub_values(&sum_left, &sum_right, registry, None, span)
                }
            }
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
        _ => {
            let (ea, ua) = value_to_expr_unit(a);
            let (eb, ub) = value_to_expr_unit(b);
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
                    let left_elems = collect_vector_stream(db, left.inner.clone());
                    let right_elems = collect_vector_stream(db, right.inner.clone());
                    dot_product(&left_elems, &right_elems, registry, span)
                }
            }
        }
        (Value::Numeric(qa), Value::Numeric(qb)) => Ok(Value::Numeric(qa.clone() * qb.clone())),
        (Value::FuzzyBool(_), _) | (_, Value::FuzzyBool(_)) => Err(err(RunErrorKind::BooleanResult)),
        (Value::Function(_), _) | (_, Value::Function(_)) | (Value::BuiltinFunction(_), _) | (_, Value::BuiltinFunction(_)) => {
            Err(err(RunErrorKind::UnknownFunction("function value cannot be used in arithmetic".to_string())))
        }
        _ => {
            let (ea, ua) = value_to_expr_unit(a);
            let (eb, ub) = value_to_expr_unit(b);
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
        _ => {
            let (ea, ua) = value_to_expr_unit(a);
            let (eb, ub) = value_to_expr_unit(b);
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
    }
}

fn value_to_expr_unit(v: &Value) -> (SymbolicExpr, Unit) {
    match v {
        Value::Numeric(q) => (SymbolicExpr::number(q.value()), q.unit().clone()),
        Value::Symbolic(sq) => (sq.expr.clone(), sq.unit.clone()),
        Value::FuzzyBool(_) => panic!("value_to_expr_unit: fuzzy boolean not supported"),
        Value::Vector(_) => panic!("value_to_expr_unit: vector not supported"),
        Value::Undefined => panic!("value_to_expr_unit: undefined not supported"),
        Value::Function(_) | Value::BuiltinFunction(_) => panic!("value_to_expr_unit: function not supported"),
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
    }
}
