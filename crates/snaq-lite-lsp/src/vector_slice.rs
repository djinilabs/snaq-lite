use snaq_lite_lang::{LazyVector, RunError, Value};

fn known_lazy_vector_len(inner: &LazyVector) -> Option<usize> {
    match inner {
        LazyVector::FromEvaluated(collected) => Some(collected.len()),
        LazyVector::FromExprs(defs) => Some(defs.len()),
        LazyVector::FromExprsWithEnv { defs, .. } => Some(defs.len()),
        LazyVector::Map { source, .. } => known_lazy_vector_len(source),
        LazyVector::Take {
            source,
            start,
            length,
        } => {
            let source_len = known_lazy_vector_len(source)?;
            let available = source_len.saturating_sub(*start);
            Some(available.min(*length))
        }
        _ => None,
    }
}

pub(crate) fn collect_vector_slice_window(
    db: &salsa::DatabaseImpl,
    inner: LazyVector,
    offset: usize,
    limit: usize,
) -> (u64, Vec<Result<Option<Value>, RunError>>) {
    let known_total = known_lazy_vector_len(&inner).map(|len| len as u64);
    snaq_lite_lang::collect_vector_slice_window_streaming(db, inner, offset, limit, known_total)
}
