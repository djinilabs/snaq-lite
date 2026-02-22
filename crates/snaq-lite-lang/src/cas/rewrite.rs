//! Term rewriting: identity/annihilation, constant folding, like-term collection.

use crate::cas::{ExprId, ExprInterner, ExprNode};
use crate::error::RunError;
use crate::quantity::{Quantity, QuantityError};
use crate::unit_registry::UnitRegistry;
use std::collections::BTreeMap;
use std::ops::Neg;

/// Bottom-up rewrite: simplify children first, then apply rules. Returns new pool and new root.
/// Uses registry for constant folding (add/sub with units).
pub fn rewrite(
    pool: &ExprInterner,
    root: ExprId,
    registry: &UnitRegistry,
) -> Result<(ExprInterner, ExprId), RunError> {
    let mut out = ExprInterner::new();
    let new_root = rewrite_rec(pool, &mut out, root, registry)?;
    Ok((out, new_root))
}

fn rewrite_rec(
    pool: &ExprInterner,
    out: &mut ExprInterner,
    id: ExprId,
    registry: &UnitRegistry,
) -> Result<ExprId, RunError> {
    match pool.get(id) {
        ExprNode::Lit(q) => Ok(out.intern(ExprNode::Lit(q.clone()))),
        ExprNode::LitSymbol(s) => Ok(out.intern(ExprNode::LitSymbol(s.clone()))),
        ExprNode::Neg(inner) => {
            let new_inner = rewrite_rec(pool, out, *inner, registry)?;
            // Neg(Neg(x)) -> x
            if let ExprNode::Neg(inner2) = out.get(new_inner) {
                return Ok(*inner2);
            }
            // Constant fold: Neg(Lit(q)) -> Lit(-q)
            if let ExprNode::Lit(q) = out.get(new_inner) {
                return Ok(out.intern(ExprNode::Lit(q.clone().neg())));
            }
            Ok(out.intern(ExprNode::Neg(new_inner)))
        }
        ExprNode::Add(ids) => rewrite_add(pool, out, ids, registry),
        ExprNode::Mul(ids) => rewrite_mul(pool, out, ids, registry),
        ExprNode::Sub(l, r) => {
            let new_l = rewrite_rec(pool, out, *l, registry)?;
            let new_r = rewrite_rec(pool, out, *r, registry)?;
            // Sub(x, 0) -> x
            if let ExprNode::Lit(q) = out.get(new_r) {
                if q.is_zero() {
                    return Ok(new_l);
                }
            }
            // Constant fold
            if let (ExprNode::Lit(ql), ExprNode::Lit(qr)) = (out.get(new_l), out.get(new_r)) {
                let result = ql
                    .clone()
                    .sub(qr, registry)
                    .map_err(quantity_to_run_error)?;
                return Ok(out.intern(ExprNode::Lit(result)));
            }
            Ok(out.intern(ExprNode::Sub(new_l, new_r)))
        }
        ExprNode::Div(l, r) => {
            let new_l = rewrite_rec(pool, out, *l, registry)?;
            let new_r = rewrite_rec(pool, out, *r, registry)?;
            // Div(x, 1) -> x when denominator is scalar 1
            if let ExprNode::Lit(q) = out.get(new_r) {
                if q.value() == 1.0 && q.unit().is_scalar() {
                    return Ok(new_l);
                }
            }
            // Constant fold; any division by zero in CAS yields DivisionByZero (plan: fail the rewrite step).
            if let (ExprNode::Lit(ql), ExprNode::Lit(qr)) = (out.get(new_l), out.get(new_r)) {
                if qr.is_zero() {
                    return Err(RunError::DivisionByZero);
                }
                let result = (ql.clone() / qr.clone()).map_err(quantity_to_run_error)?;
                return Ok(out.intern(ExprNode::Lit(result)));
            }
            // Push Neg out of numerator: Div(Neg(inner), r) -> Neg(Div(inner, r)) so value() can simplify Div to product form.
            if let ExprNode::Neg(inner_id) = out.get(new_l) {
                let div_id = out.intern(ExprNode::Div(*inner_id, new_r));
                return Ok(out.intern(ExprNode::Neg(div_id)));
            }
            Ok(out.intern(ExprNode::Div(new_l, new_r)))
        }
        ExprNode::Call(name, args) => {
            let new_args: Vec<(Option<String>, ExprId)> = args
                .iter()
                .map(|(n, id)| {
                    let new_id = rewrite_rec(pool, out, *id, registry)?;
                    Ok((n.clone(), new_id))
                })
                .collect::<Result<Vec<_>, RunError>>()?;
            Ok(out.intern(ExprNode::Call(name.clone(), new_args)))
        }
        ExprNode::As(l, r) => {
            let new_l = rewrite_rec(pool, out, *l, registry)?;
            let new_r = rewrite_rec(pool, out, *r, registry)?;
            Ok(out.intern(ExprNode::As(new_l, new_r)))
        }
        ExprNode::VecLiteral(ids) => {
            let new_ids: Vec<ExprId> = ids
                .iter()
                .map(|&id| rewrite_rec(pool, out, id, registry))
                .collect::<Result<Vec<_>, RunError>>()?;
            Ok(out.intern(ExprNode::VecLiteral(new_ids)))
        }
    }
}

fn quantity_to_run_error(e: QuantityError) -> RunError {
    match e {
        QuantityError::DivisionByZero => RunError::DivisionByZero,
        QuantityError::DimensionMismatch { left, right } => RunError::DimensionMismatch {
            left,
            right,
        },
        QuantityError::IncompatibleUnits(left, right) => RunError::DimensionMismatch {
            left,
            right,
        },
    }
}

fn rewrite_add(
    pool: &ExprInterner,
    out: &mut ExprInterner,
    ids: &[ExprId],
    registry: &UnitRegistry,
) -> Result<ExprId, RunError> {
    let simplified: Vec<ExprId> = {
        let mut v = Vec::with_capacity(ids.len());
        for &i in ids {
            v.push(rewrite_rec(pool, out, i, registry)?);
        }
        v
    };

    // Identity: Add([x]) -> x
    if simplified.len() == 1 {
        return Ok(simplified[0]);
    }

    // Partition into constants (Lit) and rest; constant-fold constants; like-term collect rest
    let mut constant: Option<Quantity> = None;
    let mut terms: Vec<ExprId> = Vec::new();
    for &id in &simplified {
        if let ExprNode::Lit(q) = out.get(id) {
            constant = Some(match constant.take() {
                None => q.clone(),
                Some(c) => c.add(q, registry).map_err(quantity_to_run_error)?,
            });
        } else {
            terms.push(id);
        }
    }

    // Like-term collection: group by structural equality (same ExprId) and sum coefficients
    let mut coef_by_term: BTreeMap<ExprId, f64> = BTreeMap::new();
    let mut rest: Vec<ExprId> = Vec::new();
    for id in terms {
        match extract_monomial(out, id) {
            Ok((coef, term_id)) => *coef_by_term.entry(term_id).or_insert(0.0) += coef,
            Err(non_monomial_id) => rest.push(non_monomial_id),
        }
    }

    let mut add_operands: Vec<ExprId> = Vec::new();
    if let Some(c) = constant {
        if !c.is_zero() {
            add_operands.push(out.intern(ExprNode::Lit(c)));
        }
    }
    for (term_id, coef) in coef_by_term {
        if (coef - 0.0).abs() < 1e-15 {
            continue;
        }
        if (coef - 1.0).abs() < 1e-15 {
            add_operands.push(term_id);
        } else {
            let lit = out.intern(ExprNode::Lit(Quantity::from_scalar(coef)));
            add_operands.push(out.intern(ExprNode::Mul(vec![lit, term_id])));
        }
    }
    for id in rest {
        add_operands.push(id);
    }

    if add_operands.is_empty() {
        return Ok(out.intern(ExprNode::Lit(Quantity::from_scalar(0.0))));
    }
    if add_operands.len() == 1 {
        return Ok(add_operands[0]);
    }
    Ok(out.intern(ExprNode::Add(add_operands)))
}

/// Extract (coefficient, term_id) for a "monomial" view. Returns Ok for simple monomials, Err(id) for non-monomial (e.g. Div).
fn extract_monomial(out: &mut ExprInterner, id: ExprId) -> Result<(f64, ExprId), ExprId> {
    match out.get(id) {
        ExprNode::LitSymbol(_) => Ok((1.0, id)),
        ExprNode::Lit(q) => {
            // Treat as coef * 1 (unit term); we don't use this for constants in like-term, so this path shouldn't be hit for Add partition
            Ok((q.value(), id))
        }
        ExprNode::Mul(ids) => {
            let mut coef = 1.0;
            let mut rest: Vec<ExprId> = Vec::new();
            for &i in ids {
                if let ExprNode::Lit(q) = out.get(i) {
                    if q.unit().is_scalar() {
                        coef *= q.value();
                    } else {
                        rest.push(i);
                    }
                } else {
                    rest.push(i);
                }
            }
            if rest.is_empty() {
                Ok((coef, out.intern(ExprNode::Lit(Quantity::from_scalar(1.0)))))
            } else if rest.len() == 1 {
                Ok((coef, rest[0]))
            } else {
                Ok((coef, out.intern(ExprNode::Mul(rest))))
            }
        }
        _ => Err(id),
    }
}

fn rewrite_mul(
    pool: &ExprInterner,
    out: &mut ExprInterner,
    ids: &[ExprId],
    registry: &UnitRegistry,
) -> Result<ExprId, RunError> {
    let simplified: Vec<ExprId> = {
        let mut v = Vec::with_capacity(ids.len());
        for &i in ids {
            v.push(rewrite_rec(pool, out, i, registry)?);
        }
        v
    };

    // Identity: Mul([x]) -> x
    if simplified.len() == 1 {
        return Ok(simplified[0]);
    }

    // Annihilation: any 0 -> 0
    for &id in &simplified {
        if let ExprNode::Lit(q) = out.get(id) {
            if q.is_zero() {
                return Ok(out.intern(ExprNode::Lit(Quantity::from_scalar(0.0))));
            }
        }
    }

    // Drop 1s (identity for Mul)
    let operands: Vec<ExprId> = simplified
        .into_iter()
        .filter(|&id| {
            if let ExprNode::Lit(q) = out.get(id) {
                !(q.value() == 1.0 && q.unit().is_scalar())
            } else {
                true
            }
        })
        .collect();

    // Constant fold: all Lits
    if operands.iter().all(|&id| matches!(out.get(id), ExprNode::Lit(_))) {
        let mut acc = None;
        for &id in &operands {
            let q = match out.get(id) {
                ExprNode::Lit(q) => q.clone(),
                _ => unreachable!(),
            };
            acc = Some(match acc.take() {
                None => q,
                Some(c) => c * q,
            });
        }
        if let Some(q) = acc {
            return Ok(out.intern(ExprNode::Lit(q)));
        }
    }

    if operands.is_empty() {
        return Ok(out.intern(ExprNode::Lit(Quantity::from_scalar(1.0))));
    }
    if operands.len() == 1 {
        return Ok(operands[0]);
    }
    Ok(out.intern(ExprNode::Mul(operands)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cas::{canonicalize, expr_def_to_interned, interned_to_expr_def};
    use crate::ir::ExprDef;
    use crate::quantity::Quantity;
    use crate::unit_registry::default_si_registry;

    fn lit(v: f64) -> ExprDef {
        ExprDef::Lit(Quantity::from_scalar(v))
    }

    #[test]
    fn rewrite_add_identity_zero() {
        // x + 0 -> x
        let def = ExprDef::Add(Box::new(ExprDef::LitSymbol("x".to_string())), Box::new(lit(0.0)));
        let mut pool = ExprInterner::new();
        let id = expr_def_to_interned(&def, &mut pool);
        let (cpool, croot) = canonicalize(&pool, id);
        let registry = default_si_registry();
        let (rpool, rroot) = rewrite(&cpool, croot, &registry).unwrap();
        let back = interned_to_expr_def(&rpool, rroot);
        assert!(matches!(back, ExprDef::LitSymbol(_)));
    }

    #[test]
    fn rewrite_mul_annihilation_zero() {
        // x * 0 -> 0
        let def = ExprDef::Mul(Box::new(ExprDef::LitSymbol("x".to_string())), Box::new(lit(0.0)));
        let mut pool = ExprInterner::new();
        let id = expr_def_to_interned(&def, &mut pool);
        let (cpool, croot) = canonicalize(&pool, id);
        let registry = default_si_registry();
        let (rpool, rroot) = rewrite(&cpool, croot, &registry).unwrap();
        let back = interned_to_expr_def(&rpool, rroot);
        if let ExprDef::Lit(q) = back {
            assert!(q.is_zero());
        } else {
            panic!("expected Lit(0)");
        }
    }

    #[test]
    fn rewrite_constant_fold_add() {
        let def = ExprDef::Add(Box::new(lit(1.0)), Box::new(lit(2.0)));
        let mut pool = ExprInterner::new();
        let id = expr_def_to_interned(&def, &mut pool);
        let (cpool, croot) = canonicalize(&pool, id);
        let registry = default_si_registry();
        let (rpool, rroot) = rewrite(&cpool, croot, &registry).unwrap();
        let back = interned_to_expr_def(&rpool, rroot);
        if let ExprDef::Lit(q) = back {
            assert!((q.value() - 3.0).abs() < 1e-10);
        } else {
            panic!("expected Lit(3)");
        }
    }

    #[test]
    fn rewrite_like_terms_symbol_plus_symbol() {
        // pi + pi -> 2*pi (after canonicalize, we have [pi, pi]; like-term gives 2*pi)
        let def = ExprDef::Add(
            Box::new(ExprDef::LitSymbol("pi".to_string())),
            Box::new(ExprDef::LitSymbol("pi".to_string())),
        );
        let mut pool = ExprInterner::new();
        let id = expr_def_to_interned(&def, &mut pool);
        let (cpool, croot) = canonicalize(&pool, id);
        let registry = default_si_registry();
        let (rpool, rroot) = rewrite(&cpool, croot, &registry).unwrap();
        let back = interned_to_expr_def(&rpool, rroot);
        // Should be Mul(Lit(2), LitSymbol("pi"))
        match &back {
            ExprDef::Mul(l, r) => {
                let (lit_side, sym_side) = if matches!(l.as_ref(), ExprDef::Lit(_)) {
                    (l.as_ref(), r.as_ref())
                } else {
                    (r.as_ref(), l.as_ref())
                };
                if let ExprDef::Lit(q) = lit_side {
                    assert!((q.value() - 2.0).abs() < 1e-10);
                }
                assert!(matches!(sym_side, ExprDef::LitSymbol(_)));
            }
            _ => panic!("expected Mul(2, pi), got {:?}", back),
        }
    }
}
