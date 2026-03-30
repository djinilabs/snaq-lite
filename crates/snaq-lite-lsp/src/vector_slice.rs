use snaq_lite_lang::LazyVector;

pub(crate) fn known_lazy_vector_len(inner: &LazyVector) -> Option<usize> {
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

