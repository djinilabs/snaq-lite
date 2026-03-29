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
    use futures::stream::StreamExt;
    let known_total = known_lazy_vector_len(&inner).map(|len| len as u64);
    let end = offset.saturating_add(limit);
    let mut stream = snaq_lite_lang::vector_into_stream(db, inner);
    futures::executor::block_on(async move {
        let mut total = 0u64;
        let mut out: Vec<Result<Option<Value>, RunError>> = Vec::with_capacity(limit);
        while let Some(item) = stream.next().await {
            let idx = total as usize;
            if idx >= offset && idx < end {
                out.push(item);
            }
            total += 1;
            if known_total.is_some() && idx + 1 >= end {
                break;
            }
        }
        let effective_total = known_total.unwrap_or(total);
        (effective_total, out)
    })
}
