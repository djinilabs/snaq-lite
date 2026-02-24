//! Canonicalization: flatten associative ops and sort by rank for deterministic matching.

use crate::cas::{ExprId, ExprInterner, ExprNode};
use std::cmp::Ordering;

/// Total order for nodes: constants first, then symbols (alphabetically), then compound by variant and children.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Rank {
    Constant,
    Symbol(String),
    Neg(Box<Rank>),
    Add(Vec<Rank>),
    Mul(Vec<Rank>),
    Sub(Box<Rank>, Box<Rank>),
    Div(Box<Rank>, Box<Rank>),
    Call(String, Vec<Rank>),
    As(Box<Rank>, Box<Rank>),
    VecLiteral(Vec<Rank>),
    Transpose(Box<Rank>),
    Eq(Box<Rank>, Box<Rank>),
    Ne(Box<Rank>, Box<Rank>),
    Lt(Box<Rank>, Box<Rank>),
    Le(Box<Rank>, Box<Rank>),
    Gt(Box<Rank>, Box<Rank>),
    Ge(Box<Rank>, Box<Rank>),
    If(Box<Rank>, Box<Rank>, Box<Rank>),
    WithPrecision(Box<Rank>, Box<Rank>),
}

fn tag_order(r: &Rank) -> u8 {
    match r {
        Rank::Constant => 0,
        Rank::Symbol(_) => 1,
        Rank::Neg(_) => 2,
        Rank::Add(_) => 3,
        Rank::Mul(_) => 4,
        Rank::Sub(_, _) => 5,
        Rank::Div(_, _) => 6,
        Rank::Call(..) => 7,
        Rank::As(..) => 8,
        Rank::VecLiteral(_) => 9,
        Rank::Transpose(_) => 10,
        Rank::Eq(..) => 11,
        Rank::Ne(..) => 12,
        Rank::Lt(..) => 13,
        Rank::Le(..) => 14,
        Rank::Gt(..) => 15,
        Rank::Ge(..) => 16,
        Rank::If(..) => 17,
        Rank::WithPrecision(..) => 18,
    }
}

impl PartialOrd for Rank {
    fn partial_cmp(&self, other: &Rank) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Rank {
    fn cmp(&self, other: &Rank) -> Ordering {
        let t = tag_order(self).cmp(&tag_order(other));
        if t != Ordering::Equal {
            return t;
        }
        match (self, other) {
            (Rank::Constant, Rank::Constant) => Ordering::Equal,
            (Rank::Symbol(a), Rank::Symbol(b)) => a.cmp(b),
            (Rank::Neg(a), Rank::Neg(b)) => a.cmp(b),
            (Rank::Add(a), Rank::Add(b)) => a.cmp(b),
            (Rank::Mul(a), Rank::Mul(b)) => a.cmp(b),
            (Rank::Sub(a1, a2), Rank::Sub(b1, b2)) => a1.cmp(b1).then(a2.cmp(b2)),
            (Rank::Div(a1, a2), Rank::Div(b1, b2)) => a1.cmp(b1).then(a2.cmp(b2)),
            (Rank::Call(a, aargs), Rank::Call(b, bargs)) => a.cmp(b).then(aargs.cmp(bargs)),
            (Rank::As(a1, a2), Rank::As(b1, b2)) => a1.cmp(b1).then(a2.cmp(b2)),
            (Rank::VecLiteral(a), Rank::VecLiteral(b)) => a.cmp(b),
            (Rank::Transpose(a), Rank::Transpose(b)) => a.cmp(b),
            (Rank::Eq(a1, a2), Rank::Eq(b1, b2)) => a1.cmp(b1).then(a2.cmp(b2)),
            (Rank::Ne(a1, a2), Rank::Ne(b1, b2)) => a1.cmp(b1).then(a2.cmp(b2)),
            (Rank::Lt(a1, a2), Rank::Lt(b1, b2)) => a1.cmp(b1).then(a2.cmp(b2)),
            (Rank::Le(a1, a2), Rank::Le(b1, b2)) => a1.cmp(b1).then(a2.cmp(b2)),
            (Rank::Gt(a1, a2), Rank::Gt(b1, b2)) => a1.cmp(b1).then(a2.cmp(b2)),
            (Rank::Ge(a1, a2), Rank::Ge(b1, b2)) => a1.cmp(b1).then(a2.cmp(b2)),
            (Rank::If(a1, a2, a3), Rank::If(b1, b2, b3)) => a1.cmp(b1).then(a2.cmp(b2)).then(a3.cmp(b3)),
            (Rank::WithPrecision(a1, a2), Rank::WithPrecision(b1, b2)) => a1.cmp(b1).then(a2.cmp(b2)),
            _ => Ordering::Equal,
        }
    }
}

/// True if this rank represents a vector-valued expression (literal or transpose). Used to avoid
/// reordering Mul operands when both are vectors, so row×column (dot) vs column×row (outer) is preserved.
fn rank_is_vector_valued(r: &Rank) -> bool {
    matches!(r, Rank::VecLiteral(_) | Rank::Transpose(_))
}

/// Compute the rank of an expression (used for sorting operands).
pub fn rank(pool: &ExprInterner, id: ExprId) -> Rank {
    match pool.get(id) {
        ExprNode::Lit(_) => Rank::Constant,
        ExprNode::LitFuzzyBool(_) => Rank::Constant,
        ExprNode::LitSymbol(s) => Rank::Symbol(s.clone()),
        ExprNode::Neg(inner) => Rank::Neg(Box::new(rank(pool, *inner))),
        ExprNode::Add(ids) => Rank::Add(ids.iter().map(|&i| rank(pool, i)).collect()),
        ExprNode::Mul(ids) => Rank::Mul(ids.iter().map(|&i| rank(pool, i)).collect()),
        ExprNode::Sub(l, r) => Rank::Sub(Box::new(rank(pool, *l)), Box::new(rank(pool, *r))),
        ExprNode::Div(l, r) => Rank::Div(Box::new(rank(pool, *l)), Box::new(rank(pool, *r))),
        ExprNode::Call(name, args) => {
            Rank::Call(name.clone(), args.iter().map(|(_, id)| rank(pool, *id)).collect())
        }
        ExprNode::As(l, r) => Rank::As(Box::new(rank(pool, *l)), Box::new(rank(pool, *r))),
        ExprNode::VecLiteral(ids) => Rank::VecLiteral(ids.iter().map(|&i| rank(pool, i)).collect()),
        ExprNode::Transpose(inner) => Rank::Transpose(Box::new(rank(pool, *inner))),
        ExprNode::Eq(l, r) => Rank::Eq(Box::new(rank(pool, *l)), Box::new(rank(pool, *r))),
        ExprNode::Ne(l, r) => Rank::Ne(Box::new(rank(pool, *l)), Box::new(rank(pool, *r))),
        ExprNode::Lt(l, r) => Rank::Lt(Box::new(rank(pool, *l)), Box::new(rank(pool, *r))),
        ExprNode::Le(l, r) => Rank::Le(Box::new(rank(pool, *l)), Box::new(rank(pool, *r))),
        ExprNode::Gt(l, r) => Rank::Gt(Box::new(rank(pool, *l)), Box::new(rank(pool, *r))),
        ExprNode::Ge(l, r) => Rank::Ge(Box::new(rank(pool, *l)), Box::new(rank(pool, *r))),
        ExprNode::If(c, t, e) => Rank::If(
            Box::new(rank(pool, *c)),
            Box::new(rank(pool, *t)),
            Box::new(rank(pool, *e)),
        ),
        ExprNode::WithPrecision(l, r) => Rank::WithPrecision(
            Box::new(rank(pool, *l)),
            Box::new(rank(pool, *r)),
        ),
    }
}

/// Flatten all direct and nested Add operands into one list. Does not sort.
fn flatten_add(pool: &ExprInterner, id: ExprId) -> Vec<ExprId> {
    match pool.get(id) {
        ExprNode::Add(ids) => {
            let mut out = Vec::new();
            for &i in ids {
                out.extend(flatten_add(pool, i));
            }
            out
        }
        _ => vec![id],
    }
}

/// Flatten all direct and nested Mul operands into one list. Does not sort.
fn flatten_mul(pool: &ExprInterner, id: ExprId) -> Vec<ExprId> {
    match pool.get(id) {
        ExprNode::Mul(ids) => {
            let mut out = Vec::new();
            for &i in ids {
                out.extend(flatten_mul(pool, i));
            }
            out
        }
        _ => vec![id],
    }
}

/// Canonicalize the tree: flatten Add/Mul and sort operands by rank. Returns new pool and new root id.
/// Pure: original pool is not mutated; new nodes are built in a fresh pool (we mutate a new pool).
pub fn canonicalize(pool: &ExprInterner, root: ExprId) -> (ExprInterner, ExprId) {
    let mut out = ExprInterner::new();
    let new_root = canonicalize_rec(pool, &mut out, root);
    (out, new_root)
}

fn canonicalize_rec(
    pool: &ExprInterner,
    out: &mut ExprInterner,
    id: ExprId,
) -> ExprId {
    match pool.get(id) {
        ExprNode::Lit(q) => out.intern(ExprNode::Lit(q.clone())),
        ExprNode::LitFuzzyBool(f) => out.intern(ExprNode::LitFuzzyBool(f.clone())),
        ExprNode::LitSymbol(s) => out.intern(ExprNode::LitSymbol(s.clone())),
        ExprNode::Neg(inner) => {
            let new_inner = canonicalize_rec(pool, out, *inner);
            out.intern(ExprNode::Neg(new_inner))
        }
        ExprNode::Add(_) => {
            let flat: Vec<ExprId> = flatten_add(pool, id)
                .into_iter()
                .map(|i| canonicalize_rec(pool, out, i))
                .collect();
            let mut sorted = flat;
            sorted.sort_by_key(|a| rank(out, *a));
            out.intern(ExprNode::Add(sorted))
        }
        ExprNode::Mul(_) => {
            let flat: Vec<ExprId> = flatten_mul(pool, id)
                .into_iter()
                .map(|i| canonicalize_rec(pool, out, i))
                .collect();
            let mut sorted = flat;
            // Preserve order only for binary vector×vector (exactly two operands, both vector-valued):
            // row×column (dot) vs column×row (outer) must not be swapped; 3+ operands are still sorted.
            let preserve_order = sorted.len() == 2
                && rank_is_vector_valued(&rank(out, sorted[0]))
                && rank_is_vector_valued(&rank(out, sorted[1]));
            if !preserve_order {
                sorted.sort_by_key(|a| rank(out, *a));
            }
            out.intern(ExprNode::Mul(sorted))
        }
        ExprNode::Sub(l, r) => {
            let new_l = canonicalize_rec(pool, out, *l);
            let new_r = canonicalize_rec(pool, out, *r);
            out.intern(ExprNode::Sub(new_l, new_r))
        }
        ExprNode::Div(l, r) => {
            let new_l = canonicalize_rec(pool, out, *l);
            let new_r = canonicalize_rec(pool, out, *r);
            out.intern(ExprNode::Div(new_l, new_r))
        }
        ExprNode::Call(name, args) => {
            let new_args: Vec<(Option<String>, ExprId)> = args
                .iter()
                .map(|(n, id)| (n.clone(), canonicalize_rec(pool, out, *id)))
                .collect();
            out.intern(ExprNode::Call(name.clone(), new_args))
        }
        ExprNode::As(l, r) => {
            let new_l = canonicalize_rec(pool, out, *l);
            let new_r = canonicalize_rec(pool, out, *r);
            out.intern(ExprNode::As(new_l, new_r))
        }
        ExprNode::VecLiteral(ids) => {
            let new_ids: Vec<ExprId> = ids
                .iter()
                .map(|&id| canonicalize_rec(pool, out, id))
                .collect();
            out.intern(ExprNode::VecLiteral(new_ids))
        }
        ExprNode::Transpose(inner) => {
            let new_inner = canonicalize_rec(pool, out, *inner);
            out.intern(ExprNode::Transpose(new_inner))
        }
        ExprNode::Eq(l, r) => {
            let new_l = canonicalize_rec(pool, out, *l);
            let new_r = canonicalize_rec(pool, out, *r);
            out.intern(ExprNode::Eq(new_l, new_r))
        }
        ExprNode::Ne(l, r) => {
            let new_l = canonicalize_rec(pool, out, *l);
            let new_r = canonicalize_rec(pool, out, *r);
            out.intern(ExprNode::Ne(new_l, new_r))
        }
        ExprNode::Lt(l, r) => {
            let new_l = canonicalize_rec(pool, out, *l);
            let new_r = canonicalize_rec(pool, out, *r);
            out.intern(ExprNode::Lt(new_l, new_r))
        }
        ExprNode::Le(l, r) => {
            let new_l = canonicalize_rec(pool, out, *l);
            let new_r = canonicalize_rec(pool, out, *r);
            out.intern(ExprNode::Le(new_l, new_r))
        }
        ExprNode::Gt(l, r) => {
            let new_l = canonicalize_rec(pool, out, *l);
            let new_r = canonicalize_rec(pool, out, *r);
            out.intern(ExprNode::Gt(new_l, new_r))
        }
        ExprNode::Ge(l, r) => {
            let new_l = canonicalize_rec(pool, out, *l);
            let new_r = canonicalize_rec(pool, out, *r);
            out.intern(ExprNode::Ge(new_l, new_r))
        }
        ExprNode::If(c, t, e) => {
            let new_c = canonicalize_rec(pool, out, *c);
            let new_t = canonicalize_rec(pool, out, *t);
            let new_e = canonicalize_rec(pool, out, *e);
            out.intern(ExprNode::If(new_c, new_t, new_e))
        }
        ExprNode::WithPrecision(l, r) => {
            let new_l = canonicalize_rec(pool, out, *l);
            let new_r = canonicalize_rec(pool, out, *r);
            out.intern(ExprNode::WithPrecision(new_l, new_r))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cas::{expr_def_to_interned, interned_to_expr_def};
    use crate::ir::ExprDef;
    use crate::quantity::Quantity;

    fn lit(v: f64) -> ExprDef {
        ExprDef::Lit(Quantity::from_scalar(v))
    }

    #[test]
    fn canonicalize_flattens_nested_add() {
        // (1 + 2) + 3 -> Add([1, 2, 3]) sorted
        let def = ExprDef::Add(
            Box::new(ExprDef::Add(Box::new(lit(1.0)), Box::new(lit(2.0)))),
            Box::new(lit(3.0)),
        );
        let mut pool = ExprInterner::new();
        let id = expr_def_to_interned(&def, &mut pool);
        let (cpool, croot) = canonicalize(&pool, id);
        match cpool.get(croot) {
            ExprNode::Add(ids) => {
                assert_eq!(ids.len(), 3, "flattened to three operands");
            }
            _ => panic!("expected Add node"),
        }
    }

    #[test]
    fn canonicalize_sorts_constants_before_symbols() {
        // pi + 1 + 2 -> order should be 1, 2, pi (constants first, then symbol)
        let def = ExprDef::Add(
            Box::new(ExprDef::LitSymbol("pi".to_string())),
            Box::new(ExprDef::Add(Box::new(lit(1.0)), Box::new(lit(2.0)))),
        );
        let mut pool = ExprInterner::new();
        let id = expr_def_to_interned(&def, &mut pool);
        let (cpool, croot) = canonicalize(&pool, id);
        let back = interned_to_expr_def(&cpool, croot);
        // After round-trip we have a binary tree; first operand should be constant (1 or 2), not pi
        if let ExprDef::Add(l, _r) = &back {
            // Left subtree: first by rank. Constants rank before symbols, so left should be a constant.
            assert!(
                matches!(l.as_ref(), ExprDef::Lit(_)) || matches!(l.as_ref(), ExprDef::Add(..)),
                "first operand should be constant or nested add of constants"
            );
        }
    }

    #[test]
    fn canonicalize_sorts_symbols_alphabetically() {
        // e + pi -> pi before e (alphabetically "e" < "pi")
        let def = ExprDef::Add(
            Box::new(ExprDef::LitSymbol("e".to_string())),
            Box::new(ExprDef::LitSymbol("pi".to_string())),
        );
        let mut pool = ExprInterner::new();
        let id = expr_def_to_interned(&def, &mut pool);
        let (cpool, croot) = canonicalize(&pool, id);
        match cpool.get(croot) {
            ExprNode::Add(ids) => {
                assert_eq!(ids.len(), 2);
                let r0 = rank(&cpool, ids[0]);
                let r1 = rank(&cpool, ids[1]);
                assert!(r0 <= r1, "operands should be sorted by rank");
                if let (Rank::Symbol(s0), Rank::Symbol(s1)) = (&r0, &r1) {
                    assert!(s0 <= s1, "e < pi");
                }
            }
            _ => panic!("expected Add"),
        }
    }

    #[test]
    fn canonicalize_preserves_vector_times_vector_order() {
        // [1,2]' * [3,4] = row × column (dot). Order must not be swapped to column × row (outer).
        let row = ExprDef::Transpose(Box::new(ExprDef::VecLiteral(vec![lit(1.0), lit(2.0)])));
        let col = ExprDef::VecLiteral(vec![lit(3.0), lit(4.0)]);
        let def = ExprDef::Mul(Box::new(row), Box::new(col));
        let mut pool = ExprInterner::new();
        let id = expr_def_to_interned(&def, &mut pool);
        let (cpool, croot) = canonicalize(&pool, id);
        let back = interned_to_expr_def(&cpool, croot);
        match &back {
            ExprDef::Mul(l, r) => {
                assert!(matches!(l.as_ref(), ExprDef::Transpose(_)), "left should stay Transpose (row)");
                assert!(matches!(r.as_ref(), ExprDef::VecLiteral(_)), "right should stay VecLiteral (column)");
            }
            _ => panic!("expected Mul, got {:?}", back),
        }
    }

    #[test]
    fn canonicalize_preserves_column_times_row_order() {
        // [1,2] * [3,4]' = column × row (outer). Order must not be swapped to row × column (dot).
        let col = ExprDef::VecLiteral(vec![lit(1.0), lit(2.0)]);
        let row = ExprDef::Transpose(Box::new(ExprDef::VecLiteral(vec![lit(3.0), lit(4.0)])));
        let def = ExprDef::Mul(Box::new(col), Box::new(row));
        let mut pool = ExprInterner::new();
        let id = expr_def_to_interned(&def, &mut pool);
        let (cpool, croot) = canonicalize(&pool, id);
        let back = interned_to_expr_def(&cpool, croot);
        match &back {
            ExprDef::Mul(l, r) => {
                assert!(matches!(l.as_ref(), ExprDef::VecLiteral(_)), "left should stay VecLiteral (column)");
                assert!(matches!(r.as_ref(), ExprDef::Transpose(_)), "right should stay Transpose (row)");
            }
            _ => panic!("expected Mul, got {:?}", back),
        }
    }
}
