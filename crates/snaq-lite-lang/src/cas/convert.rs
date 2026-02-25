//! Conversion between ExprDef (binary tree) and interned CAS representation.

use crate::cas::{ExprId, ExprInterner, ExprNode};
use crate::ir::{CallArg, ExprDef};

/// Build interned nodes from a resolved ExprDef. Only resolved variants are supported.
/// Binary Add/Mul become two-child nodes (flattened in canonicalization).
pub fn expr_def_to_interned(def: &ExprDef, pool: &mut ExprInterner) -> ExprId {
    match def {
        ExprDef::Lit(q) => pool.intern(ExprNode::Lit(q.clone())),
        ExprDef::LitFuzzyBool(f) => pool.intern(ExprNode::LitFuzzyBool(f.clone())),
        ExprDef::LitSymbol(s) => pool.intern(ExprNode::LitSymbol(s.clone())),
        ExprDef::Add(l, r) => {
            let lid = expr_def_to_interned(l, pool);
            let rid = expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Add(vec![lid, rid]))
        }
        ExprDef::Sub(l, r) => {
            let lid = expr_def_to_interned(l, pool);
            let rid = expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Sub(lid, rid))
        }
        ExprDef::Mul(l, r) => {
            let lid = expr_def_to_interned(l, pool);
            let rid = expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Mul(vec![lid, rid]))
        }
        ExprDef::Div(l, r) => {
            let lid = expr_def_to_interned(l, pool);
            let rid = expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Div(lid, rid))
        }
        ExprDef::Neg(inner) => {
            let id = expr_def_to_interned(inner, pool);
            pool.intern(ExprNode::Neg(id))
        }
        ExprDef::Call(name, args) => {
            let arg_ids: Vec<(Option<String>, ExprId)> = args
                .iter()
                .map(|arg| {
                    let (name_opt, def) = match arg {
                        CallArg::Positional(e) => (None, e.as_ref()),
                        CallArg::Named(n, e) => (Some(n.clone()), e.as_ref()),
                    };
                    (name_opt, expr_def_to_interned(def, pool))
                })
                .collect();
            pool.intern(ExprNode::Call(name.clone(), arg_ids))
        }
        ExprDef::As(l, r) => {
            let lid = expr_def_to_interned(l, pool);
            let rid = expr_def_to_interned(r, pool);
            pool.intern(ExprNode::As(lid, rid))
        }
        ExprDef::VecLiteral(elems) => {
            let ids: Vec<_> = elems.iter().map(|e| expr_def_to_interned(e, pool)).collect();
            pool.intern(ExprNode::VecLiteral(ids))
        }
        ExprDef::Transpose(inner) => {
            let id = expr_def_to_interned(inner, pool);
            pool.intern(ExprNode::Transpose(id))
        }
        ExprDef::Index(base, index) => {
            let base_id = expr_def_to_interned(base, pool);
            let index_id = expr_def_to_interned(index, pool);
            pool.intern(ExprNode::Index(base_id, index_id))
        }
        ExprDef::Eq(l, r) => {
            let lid = expr_def_to_interned(l, pool);
            let rid = expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Eq(lid, rid))
        }
        ExprDef::Ne(l, r) => {
            let lid = expr_def_to_interned(l, pool);
            let rid = expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Ne(lid, rid))
        }
        ExprDef::Lt(l, r) => {
            let lid = expr_def_to_interned(l, pool);
            let rid = expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Lt(lid, rid))
        }
        ExprDef::Le(l, r) => {
            let lid = expr_def_to_interned(l, pool);
            let rid = expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Le(lid, rid))
        }
        ExprDef::Gt(l, r) => {
            let lid = expr_def_to_interned(l, pool);
            let rid = expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Gt(lid, rid))
        }
        ExprDef::Ge(l, r) => {
            let lid = expr_def_to_interned(l, pool);
            let rid = expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Ge(lid, rid))
        }
        ExprDef::If(cond, then_b, else_b) => {
            let cid = expr_def_to_interned(cond, pool);
            let tid = expr_def_to_interned(then_b, pool);
            let eid = expr_def_to_interned(else_b, pool);
            pool.intern(ExprNode::If(cid, tid, eid))
        }
        ExprDef::WithPrecision(l, r) => {
            let lid = expr_def_to_interned(l, pool);
            let rid = expr_def_to_interned(r, pool);
            pool.intern(ExprNode::WithPrecision(lid, rid))
        }
        ExprDef::Block(exprs) => {
            let ids: Vec<ExprId> = exprs.iter().map(|e| expr_def_to_interned(e, pool)).collect();
            pool.intern(ExprNode::Block(ids))
        }
        ExprDef::Binding(name, rhs) => {
            let rid = expr_def_to_interned(rhs, pool);
            pool.intern(ExprNode::Binding(name.clone(), rid))
        }
        ExprDef::Lambda(params, body) => {
            let param_ids: Vec<(String, Option<ExprId>)> = params
                .iter()
                .map(|(name, default)| {
                    (
                        name.clone(),
                        default.as_ref().map(|d| expr_def_to_interned(d, pool)),
                    )
                })
                .collect();
            let body_id = expr_def_to_interned(body, pool);
            pool.intern(ExprNode::Lambda(param_ids, body_id))
        }
        ExprDef::CallExpr(callee, args) => {
            let callee_id = expr_def_to_interned(callee, pool);
            let arg_ids: Vec<(Option<String>, ExprId)> = args
                .iter()
                .map(|arg| {
                    let (name_opt, def) = match arg {
                        CallArg::Positional(e) => (None, e.as_ref()),
                        CallArg::Named(n, e) => (Some(n.clone()), e.as_ref()),
                    };
                    (name_opt, expr_def_to_interned(def, pool))
                })
                .collect();
            pool.intern(ExprNode::CallExpr(callee_id, arg_ids))
        }
        ExprDef::LitScalar(..) | ExprDef::LitWithUnit(..) | ExprDef::LitUnit(..) => {
            panic!("unresolved ExprDef: resolve() must be called before CAS")
        }
    }
}

/// Convert an interned expression back to ExprDef. N-ary Add/Mul are re-binaryized left-associatively.
pub fn interned_to_expr_def(pool: &ExprInterner, id: ExprId) -> ExprDef {
    match pool.get(id) {
        ExprNode::Lit(q) => ExprDef::Lit(q.clone()),
        ExprNode::LitFuzzyBool(f) => ExprDef::LitFuzzyBool(f.clone()),
        ExprNode::LitSymbol(s) => ExprDef::LitSymbol(s.clone()),
        ExprNode::Add(ids) => binaryize_add(pool, ids),
        ExprNode::Mul(ids) => binaryize_mul(pool, ids),
        ExprNode::Sub(l, r) => ExprDef::Sub(
            Box::new(interned_to_expr_def(pool, *l)),
            Box::new(interned_to_expr_def(pool, *r)),
        ),
        ExprNode::Div(l, r) => ExprDef::Div(
            Box::new(interned_to_expr_def(pool, *l)),
            Box::new(interned_to_expr_def(pool, *r)),
        ),
        ExprNode::Neg(inner) => ExprDef::Neg(Box::new(interned_to_expr_def(pool, *inner))),
        ExprNode::Call(name, args) => {
            let args: Vec<CallArg> = args
                .iter()
                .map(|(name_opt, id)| {
                    let e = interned_to_expr_def(pool, *id);
                    match name_opt {
                        None => CallArg::Positional(Box::new(e)),
                        Some(n) => CallArg::Named(n.clone(), Box::new(e)),
                    }
                })
                .collect();
            ExprDef::Call(name.clone(), args)
        }
        ExprNode::As(l, r) => ExprDef::As(
            Box::new(interned_to_expr_def(pool, *l)),
            Box::new(interned_to_expr_def(pool, *r)),
        ),
        ExprNode::VecLiteral(ids) => ExprDef::VecLiteral(
            ids.iter()
                .map(|&id| interned_to_expr_def(pool, id))
                .collect(),
        ),
        ExprNode::Transpose(inner) => ExprDef::Transpose(Box::new(interned_to_expr_def(pool, *inner))),
        ExprNode::Index(base, index) => ExprDef::Index(
            Box::new(interned_to_expr_def(pool, *base)),
            Box::new(interned_to_expr_def(pool, *index)),
        ),
        ExprNode::Eq(l, r) => ExprDef::Eq(
            Box::new(interned_to_expr_def(pool, *l)),
            Box::new(interned_to_expr_def(pool, *r)),
        ),
        ExprNode::Ne(l, r) => ExprDef::Ne(
            Box::new(interned_to_expr_def(pool, *l)),
            Box::new(interned_to_expr_def(pool, *r)),
        ),
        ExprNode::Lt(l, r) => ExprDef::Lt(
            Box::new(interned_to_expr_def(pool, *l)),
            Box::new(interned_to_expr_def(pool, *r)),
        ),
        ExprNode::Le(l, r) => ExprDef::Le(
            Box::new(interned_to_expr_def(pool, *l)),
            Box::new(interned_to_expr_def(pool, *r)),
        ),
        ExprNode::Gt(l, r) => ExprDef::Gt(
            Box::new(interned_to_expr_def(pool, *l)),
            Box::new(interned_to_expr_def(pool, *r)),
        ),
        ExprNode::Ge(l, r) => ExprDef::Ge(
            Box::new(interned_to_expr_def(pool, *l)),
            Box::new(interned_to_expr_def(pool, *r)),
        ),
        ExprNode::If(c, t, e) => ExprDef::If(
            Box::new(interned_to_expr_def(pool, *c)),
            Box::new(interned_to_expr_def(pool, *t)),
            Box::new(interned_to_expr_def(pool, *e)),
        ),
        ExprNode::WithPrecision(l, r) => ExprDef::WithPrecision(
            Box::new(interned_to_expr_def(pool, *l)),
            Box::new(interned_to_expr_def(pool, *r)),
        ),
        ExprNode::Block(ids) => ExprDef::Block(
            ids.iter()
                .map(|&id| interned_to_expr_def(pool, id))
                .collect(),
        ),
        ExprNode::Binding(name, rhs_id) => ExprDef::Binding(
            name.clone(),
            Box::new(interned_to_expr_def(pool, *rhs_id)),
        ),
        ExprNode::Lambda(params, body_id) => {
            let params: Vec<(String, Option<Box<ExprDef>>)> = params
                .iter()
                .map(|(name, default_id)| {
                    (
                        name.clone(),
                        default_id.map(|id| Box::new(interned_to_expr_def(pool, id))),
                    )
                })
                .collect();
            ExprDef::Lambda(params, Box::new(interned_to_expr_def(pool, *body_id)))
        }
        ExprNode::CallExpr(callee_id, args) => {
            let callee = interned_to_expr_def(pool, *callee_id);
            let args: Vec<CallArg> = args
                .iter()
                .map(|(name_opt, id)| {
                    let e = interned_to_expr_def(pool, *id);
                    match name_opt {
                        None => CallArg::Positional(Box::new(e)),
                        Some(n) => CallArg::Named(n.clone(), Box::new(e)),
                    }
                })
                .collect();
            ExprDef::CallExpr(Box::new(callee), args)
        }
    }
}

fn binaryize_add(pool: &ExprInterner, ids: &[ExprId]) -> ExprDef {
    match ids {
        [] => ExprDef::Lit(crate::quantity::Quantity::from_scalar(0.0)),
        [id] => interned_to_expr_def(pool, *id),
        [first, rest @ ..] => {
            let mut acc = interned_to_expr_def(pool, *first);
            for id in rest {
                acc = ExprDef::Add(Box::new(acc), Box::new(interned_to_expr_def(pool, *id)));
            }
            acc
        }
    }
}

fn binaryize_mul(pool: &ExprInterner, ids: &[ExprId]) -> ExprDef {
    match ids {
        [] => ExprDef::Lit(crate::quantity::Quantity::from_scalar(1.0)),
        [id] => interned_to_expr_def(pool, *id),
        [first, rest @ ..] => {
            let mut acc = interned_to_expr_def(pool, *first);
            for id in rest {
                acc = ExprDef::Mul(Box::new(acc), Box::new(interned_to_expr_def(pool, *id)));
            }
            acc
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::CallArg;
    use crate::quantity::Quantity;

    fn lit(v: f64) -> ExprDef {
        ExprDef::Lit(Quantity::from_scalar(v))
    }

    #[test]
    fn round_trip_lit() {
        let def = lit(42.0);
        let mut pool = ExprInterner::new();
        let id = expr_def_to_interned(&def, &mut pool);
        let back = interned_to_expr_def(&pool, id);
        assert_eq!(back, def);
    }

    #[test]
    fn round_trip_add() {
        let def = ExprDef::Add(Box::new(lit(1.0)), Box::new(lit(2.0)));
        let mut pool = ExprInterner::new();
        let id = expr_def_to_interned(&def, &mut pool);
        let back = interned_to_expr_def(&pool, id);
        assert_eq!(back, def);
    }

    #[test]
    fn round_trip_nested_add() {
        // (1 + 2) + 3
        let def = ExprDef::Add(
            Box::new(ExprDef::Add(Box::new(lit(1.0)), Box::new(lit(2.0)))),
            Box::new(lit(3.0)),
        );
        let mut pool = ExprInterner::new();
        let id = expr_def_to_interned(&def, &mut pool);
        let back = interned_to_expr_def(&pool, id);
        // Back is left-associative: Add(Add(1, 2), 3)
        assert!(matches!(back, ExprDef::Add(..)));
        if let ExprDef::Add(l, r) = &back {
            assert!(matches!(r.as_ref(), ExprDef::Lit(_)));
            if let ExprDef::Add(ll, lr) = l.as_ref() {
                assert!(matches!(ll.as_ref(), ExprDef::Lit(_)));
                assert!(matches!(lr.as_ref(), ExprDef::Lit(_)));
            }
        }
    }

    #[test]
    fn round_trip_lit_symbol() {
        let def = ExprDef::LitSymbol("pi".to_string());
        let mut pool = ExprInterner::new();
        let id = expr_def_to_interned(&def, &mut pool);
        let back = interned_to_expr_def(&pool, id);
        assert_eq!(back, def);
    }

    #[test]
    fn round_trip_call() {
        let def = ExprDef::Call(
            "sin".to_string(),
            vec![CallArg::Positional(Box::new(lit(1.0)))],
        );
        let mut pool = ExprInterner::new();
        let id = expr_def_to_interned(&def, &mut pool);
        let back = interned_to_expr_def(&pool, id);
        assert_eq!(back, def);
    }

    #[test]
    fn dedup_same_lit_returns_same_id() {
        let def = lit(7.0);
        let mut pool = ExprInterner::new();
        let id1 = expr_def_to_interned(&def, &mut pool);
        let id2 = expr_def_to_interned(&def, &mut pool);
        assert_eq!(id1, id2);
    }

    #[test]
    fn dedup_same_add_structure_returns_same_id() {
        let def = ExprDef::Add(Box::new(lit(1.0)), Box::new(lit(2.0)));
        let mut pool = ExprInterner::new();
        let id1 = expr_def_to_interned(&def, &mut pool);
        let id2 = expr_def_to_interned(&def, &mut pool);
        assert_eq!(id1, id2);
    }

    #[test]
    fn different_structure_returns_different_id() {
        let mut pool = ExprInterner::new();
        let id1 = expr_def_to_interned(&lit(1.0), &mut pool);
        let id2 = expr_def_to_interned(&lit(2.0), &mut pool);
        let id3 = expr_def_to_interned(
            &ExprDef::Add(Box::new(lit(1.0)), Box::new(lit(2.0))),
            &mut pool,
        );
        assert_ne!(id1, id2);
        assert_ne!(id1, id3);
        assert_ne!(id2, id3);
    }
}
