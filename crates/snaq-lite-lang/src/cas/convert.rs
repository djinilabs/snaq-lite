//! Conversion between ExprDef (binary tree) and interned CAS representation.

use crate::cas::{ExprId, ExprInterner, ExprNode};
use crate::error::Span;
use crate::ir::{CallArg, ExprDef, SpannedCallArg, SpannedExprDef, SpannedExprDefKind};

/// Build interned nodes from a resolved SpannedExprDef. Only resolved variants are supported.
/// Binary Add/Mul become two-child nodes (flattened in canonicalization). Spans are stored per node.
pub fn spanned_expr_def_to_interned(def: &SpannedExprDef, pool: &mut ExprInterner) -> ExprId {
    let span = def.span;
    match &def.value {
        SpannedExprDefKind::Lit(q) => pool.intern(ExprNode::Lit(q.clone()), span),
        SpannedExprDefKind::LitFuzzyBool(f) => pool.intern(ExprNode::LitFuzzyBool(f.clone()), span),
        SpannedExprDefKind::LitSymbol(s) => pool.intern(ExprNode::LitSymbol(s.clone()), span),
        SpannedExprDefKind::LitDate(gd) => pool.intern(ExprNode::LitDate(gd.clone()), span),
        SpannedExprDefKind::LitTemporal(_) => {
            panic!("unresolved LitTemporal: resolve() must convert to LitDate before CAS")
        }
        SpannedExprDefKind::Add(l, r) => {
            let lid = spanned_expr_def_to_interned(l, pool);
            let rid = spanned_expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Add(vec![lid, rid]), span)
        }
        SpannedExprDefKind::Sub(l, r) => {
            let lid = spanned_expr_def_to_interned(l, pool);
            let rid = spanned_expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Sub(lid, rid), span)
        }
        SpannedExprDefKind::Mul(l, r) => {
            let lid = spanned_expr_def_to_interned(l, pool);
            let rid = spanned_expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Mul(vec![lid, rid]), span)
        }
        SpannedExprDefKind::Div(l, r) => {
            let lid = spanned_expr_def_to_interned(l, pool);
            let rid = spanned_expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Div(lid, rid), span)
        }
        SpannedExprDefKind::Neg(inner) => {
            let id = spanned_expr_def_to_interned(inner, pool);
            pool.intern(ExprNode::Neg(id), span)
        }
        SpannedExprDefKind::Call(name, args) => {
            let arg_ids: Vec<(Option<String>, ExprId)> = args
                .iter()
                .map(|arg| {
                    let (name_opt, def) = match arg {
                        SpannedCallArg::Positional(e) => (None, e.as_ref()),
                        SpannedCallArg::Named(n, e) => (Some(n.clone()), e.as_ref()),
                    };
                    (name_opt, spanned_expr_def_to_interned(def, pool))
                })
                .collect();
            pool.intern(ExprNode::Call(name.clone(), arg_ids), span)
        }
        SpannedExprDefKind::As(l, r) => {
            let lid = spanned_expr_def_to_interned(l, pool);
            let rid = spanned_expr_def_to_interned(r, pool);
            pool.intern(ExprNode::As(lid, rid), span)
        }
        SpannedExprDefKind::VecLiteral(elems) => {
            let ids: Vec<_> = elems.iter().map(|e| spanned_expr_def_to_interned(e, pool)).collect();
            pool.intern(ExprNode::VecLiteral(ids), span)
        }
        SpannedExprDefKind::MapLiteral(entries) => {
            let ids: Vec<(String, ExprId)> = entries
                .iter()
                .map(|(k, v)| (k.clone(), spanned_expr_def_to_interned(v, pool)))
                .collect();
            pool.intern(ExprNode::MapLiteral(ids), span)
        }
        SpannedExprDefKind::Transpose(inner) => {
            let id = spanned_expr_def_to_interned(inner, pool);
            pool.intern(ExprNode::Transpose(id), span)
        }
        SpannedExprDefKind::Index(base, key) => {
            let base_id = spanned_expr_def_to_interned(base, pool);
            pool.intern(ExprNode::Index(base_id, key.clone()), span)
        }
        SpannedExprDefKind::Member(base, name) => {
            let base_id = spanned_expr_def_to_interned(base, pool);
            pool.intern(ExprNode::Member(base_id, name.clone()), span)
        }
        SpannedExprDefKind::MethodCall(base, name, args) => {
            let base_id = spanned_expr_def_to_interned(base, pool);
            let arg_ids: Vec<(Option<String>, ExprId)> = args
                .iter()
                .map(|arg| {
                    let (name_opt, def) = match arg {
                        SpannedCallArg::Positional(e) => (None, e.as_ref()),
                        SpannedCallArg::Named(n, e) => (Some(n.clone()), e.as_ref()),
                    };
                    (name_opt, spanned_expr_def_to_interned(def, pool))
                })
                .collect();
            pool.intern(ExprNode::MethodCall(base_id, name.clone(), arg_ids), span)
        }
        SpannedExprDefKind::Eq(l, r) => {
            let lid = spanned_expr_def_to_interned(l, pool);
            let rid = spanned_expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Eq(lid, rid), span)
        }
        SpannedExprDefKind::Ne(l, r) => {
            let lid = spanned_expr_def_to_interned(l, pool);
            let rid = spanned_expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Ne(lid, rid), span)
        }
        SpannedExprDefKind::Lt(l, r) => {
            let lid = spanned_expr_def_to_interned(l, pool);
            let rid = spanned_expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Lt(lid, rid), span)
        }
        SpannedExprDefKind::Le(l, r) => {
            let lid = spanned_expr_def_to_interned(l, pool);
            let rid = spanned_expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Le(lid, rid), span)
        }
        SpannedExprDefKind::Gt(l, r) => {
            let lid = spanned_expr_def_to_interned(l, pool);
            let rid = spanned_expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Gt(lid, rid), span)
        }
        SpannedExprDefKind::Ge(l, r) => {
            let lid = spanned_expr_def_to_interned(l, pool);
            let rid = spanned_expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Ge(lid, rid), span)
        }
        SpannedExprDefKind::And(l, r) => {
            let lid = spanned_expr_def_to_interned(l, pool);
            let rid = spanned_expr_def_to_interned(r, pool);
            pool.intern(ExprNode::And(lid, rid), span)
        }
        SpannedExprDefKind::If(cond, then_b, else_b) => {
            let cid = spanned_expr_def_to_interned(cond, pool);
            let tid = spanned_expr_def_to_interned(then_b, pool);
            let eid = spanned_expr_def_to_interned(else_b, pool);
            pool.intern(ExprNode::If(cid, tid, eid), span)
        }
        SpannedExprDefKind::WithPrecision(l, r) => {
            let lid = spanned_expr_def_to_interned(l, pool);
            let rid = spanned_expr_def_to_interned(r, pool);
            pool.intern(ExprNode::WithPrecision(lid, rid), span)
        }
        SpannedExprDefKind::Block(exprs) => {
            let ids: Vec<ExprId> = exprs.iter().map(|e| spanned_expr_def_to_interned(e, pool)).collect();
            pool.intern(ExprNode::Block(ids), span)
        }
        SpannedExprDefKind::Binding(name, rhs) => {
            let rid = spanned_expr_def_to_interned(rhs, pool);
            pool.intern(ExprNode::Binding(name.clone(), rid), span)
        }
        SpannedExprDefKind::Lambda(params, body) => {
            let param_ids: Vec<(String, Option<ExprId>)> = params
                .iter()
                .map(|(name, default)| {
                    (
                        name.clone(),
                        default.as_ref().map(|d| spanned_expr_def_to_interned(d, pool)),
                    )
                })
                .collect();
            let body_id = spanned_expr_def_to_interned(body, pool);
            pool.intern(ExprNode::Lambda(param_ids, body_id), span)
        }
        SpannedExprDefKind::CallExpr(callee, args) => {
            let callee_id = spanned_expr_def_to_interned(callee, pool);
            let arg_ids: Vec<(Option<String>, ExprId)> = args
                .iter()
                .map(|arg| {
                    let (name_opt, def) = match arg {
                        SpannedCallArg::Positional(e) => (None, e.as_ref()),
                        SpannedCallArg::Named(n, e) => (Some(n.clone()), e.as_ref()),
                    };
                    (name_opt, spanned_expr_def_to_interned(def, pool))
                })
                .collect();
            pool.intern(ExprNode::CallExpr(callee_id, arg_ids), span)
        }
        SpannedExprDefKind::ExternalStream(name) => pool.intern(ExprNode::ExternalStream(name.clone()), span),
        SpannedExprDefKind::InputDecl(name, param_id, type_name) => pool.intern(
            ExprNode::InputDecl(name.clone(), param_id.clone(), type_name.clone()),
            span,
        ),
        SpannedExprDefKind::LitScalar(..)
        | SpannedExprDefKind::LitWithUnit(..)
        | SpannedExprDefKind::LitUnit(..) => {
            panic!("unresolved SpannedExprDef: resolve() must be called before CAS")
        }
    }
}

/// Build interned nodes from a resolved ExprDef (no spans). Uses default span for all nodes. For tests or legacy paths.
pub fn expr_def_to_interned(def: &ExprDef, pool: &mut ExprInterner) -> ExprId {
    let span = Span::default();
    match def {
        ExprDef::Lit(q) => pool.intern(ExprNode::Lit(q.clone()), span),
        ExprDef::LitFuzzyBool(f) => pool.intern(ExprNode::LitFuzzyBool(f.clone()), span),
        ExprDef::LitSymbol(s) => pool.intern(ExprNode::LitSymbol(s.clone()), span),
        ExprDef::LitDate(gd) => pool.intern(ExprNode::LitDate(gd.clone()), span),
        ExprDef::LitTemporal(_) => panic!("unresolved LitTemporal: resolve() must convert to LitDate before CAS"),
        ExprDef::Add(l, r) => {
            let lid = expr_def_to_interned(l, pool);
            let rid = expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Add(vec![lid, rid]), span)
        }
        ExprDef::Sub(l, r) => {
            let lid = expr_def_to_interned(l, pool);
            let rid = expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Sub(lid, rid), span)
        }
        ExprDef::Mul(l, r) => {
            let lid = expr_def_to_interned(l, pool);
            let rid = expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Mul(vec![lid, rid]), span)
        }
        ExprDef::Div(l, r) => {
            let lid = expr_def_to_interned(l, pool);
            let rid = expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Div(lid, rid), span)
        }
        ExprDef::Neg(inner) => {
            let id = expr_def_to_interned(inner, pool);
            pool.intern(ExprNode::Neg(id), span)
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
            pool.intern(ExprNode::Call(name.clone(), arg_ids), span)
        }
        ExprDef::As(l, r) => {
            let lid = expr_def_to_interned(l, pool);
            let rid = expr_def_to_interned(r, pool);
            pool.intern(ExprNode::As(lid, rid), span)
        }
        ExprDef::VecLiteral(elems) => {
            let ids: Vec<_> = elems.iter().map(|e| expr_def_to_interned(e, pool)).collect();
            pool.intern(ExprNode::VecLiteral(ids), span)
        }
        ExprDef::Transpose(inner) => {
            let id = expr_def_to_interned(inner, pool);
            pool.intern(ExprNode::Transpose(id), span)
        }
        ExprDef::Index(base, key) => {
            let base_id = expr_def_to_interned(base, pool);
            pool.intern(ExprNode::Index(base_id, key.clone()), span)
        }
        ExprDef::Member(base, name) => {
            let base_id = expr_def_to_interned(base, pool);
            pool.intern(ExprNode::Member(base_id, name.clone()), span)
        }
        ExprDef::MethodCall(base, name, args) => {
            let base_id = expr_def_to_interned(base, pool);
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
            pool.intern(ExprNode::MethodCall(base_id, name.clone(), arg_ids), span)
        }
        ExprDef::Eq(l, r) => {
            let lid = expr_def_to_interned(l, pool);
            let rid = expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Eq(lid, rid), span)
        }
        ExprDef::Ne(l, r) => {
            let lid = expr_def_to_interned(l, pool);
            let rid = expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Ne(lid, rid), span)
        }
        ExprDef::Lt(l, r) => {
            let lid = expr_def_to_interned(l, pool);
            let rid = expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Lt(lid, rid), span)
        }
        ExprDef::Le(l, r) => {
            let lid = expr_def_to_interned(l, pool);
            let rid = expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Le(lid, rid), span)
        }
        ExprDef::Gt(l, r) => {
            let lid = expr_def_to_interned(l, pool);
            let rid = expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Gt(lid, rid), span)
        }
        ExprDef::Ge(l, r) => {
            let lid = expr_def_to_interned(l, pool);
            let rid = expr_def_to_interned(r, pool);
            pool.intern(ExprNode::Ge(lid, rid), span)
        }
        ExprDef::And(l, r) => {
            let lid = expr_def_to_interned(l, pool);
            let rid = expr_def_to_interned(r, pool);
            pool.intern(ExprNode::And(lid, rid), span)
        }
        ExprDef::If(cond, then_b, else_b) => {
            let cid = expr_def_to_interned(cond, pool);
            let tid = expr_def_to_interned(then_b, pool);
            let eid = expr_def_to_interned(else_b, pool);
            pool.intern(ExprNode::If(cid, tid, eid), span)
        }
        ExprDef::WithPrecision(l, r) => {
            let lid = expr_def_to_interned(l, pool);
            let rid = expr_def_to_interned(r, pool);
            pool.intern(ExprNode::WithPrecision(lid, rid), span)
        }
        ExprDef::Block(exprs) => {
            let ids: Vec<ExprId> = exprs.iter().map(|e| expr_def_to_interned(e, pool)).collect();
            pool.intern(ExprNode::Block(ids), span)
        }
        ExprDef::Binding(name, rhs) => {
            let rid = expr_def_to_interned(rhs, pool);
            pool.intern(ExprNode::Binding(name.clone(), rid), span)
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
            pool.intern(ExprNode::Lambda(param_ids, body_id), span)
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
            pool.intern(ExprNode::CallExpr(callee_id, arg_ids), span)
        }
        ExprDef::ExternalStream(name) => pool.intern(ExprNode::ExternalStream(name.clone()), span),
        ExprDef::InputDecl(name, param_id, type_name) => pool.intern(
            ExprNode::InputDecl(name.clone(), param_id.clone(), type_name.clone()),
            span,
        ),
        ExprDef::MapLiteral(entries) => {
            let ids: Vec<(String, ExprId)> = entries
                .iter()
                .map(|(k, v)| (k.clone(), expr_def_to_interned(v, pool)))
                .collect();
            pool.intern(ExprNode::MapLiteral(ids), span)
        }
        ExprDef::LitScalar(..) | ExprDef::LitWithUnit(..) | ExprDef::LitUnit(..) => {
            panic!("unresolved ExprDef: resolve() must be called before CAS")
        }
    }
}

/// Convert an interned expression back to SpannedExprDef. N-ary Add/Mul are re-binaryized left-associatively.
pub fn interned_to_spanned_expr_def(pool: &ExprInterner, id: ExprId) -> SpannedExprDef {
    let span = pool.get_span(id);
    let value = match pool.get(id) {
        ExprNode::Lit(q) => SpannedExprDefKind::Lit(q.clone()),
        ExprNode::LitFuzzyBool(f) => SpannedExprDefKind::LitFuzzyBool(f.clone()),
        ExprNode::LitSymbol(s) => SpannedExprDefKind::LitSymbol(s.clone()),
        ExprNode::LitDate(gd) => SpannedExprDefKind::LitDate(gd.clone()),
        ExprNode::Add(ids) => return binaryize_add_spanned(pool, ids),
        ExprNode::Mul(ids) => return binaryize_mul_spanned(pool, ids),
        ExprNode::Sub(l, r) => SpannedExprDefKind::Sub(
            Box::new(interned_to_spanned_expr_def(pool, *l)),
            Box::new(interned_to_spanned_expr_def(pool, *r)),
        ),
        ExprNode::Div(l, r) => SpannedExprDefKind::Div(
            Box::new(interned_to_spanned_expr_def(pool, *l)),
            Box::new(interned_to_spanned_expr_def(pool, *r)),
        ),
        ExprNode::Neg(inner) => {
            SpannedExprDefKind::Neg(Box::new(interned_to_spanned_expr_def(pool, *inner)))
        }
        ExprNode::Call(name, args) => {
            let args: Vec<SpannedCallArg> = args
                .iter()
                .map(|(name_opt, id)| {
                    let e = interned_to_spanned_expr_def(pool, *id);
                    match name_opt {
                        None => SpannedCallArg::Positional(Box::new(e)),
                        Some(n) => SpannedCallArg::Named(n.clone(), Box::new(e)),
                    }
                })
                .collect();
            SpannedExprDefKind::Call(name.clone(), args)
        }
        ExprNode::As(l, r) => SpannedExprDefKind::As(
            Box::new(interned_to_spanned_expr_def(pool, *l)),
            Box::new(interned_to_spanned_expr_def(pool, *r)),
        ),
        ExprNode::VecLiteral(ids) => SpannedExprDefKind::VecLiteral(
            ids.iter()
                .map(|&id| interned_to_spanned_expr_def(pool, id))
                .collect(),
        ),
        ExprNode::Transpose(inner) => {
            SpannedExprDefKind::Transpose(Box::new(interned_to_spanned_expr_def(pool, *inner)))
        }
        ExprNode::Index(base, key) => SpannedExprDefKind::Index(
            Box::new(interned_to_spanned_expr_def(pool, *base)),
            key.clone(),
        ),
        ExprNode::Member(base_id, name) => SpannedExprDefKind::Member(
            Box::new(interned_to_spanned_expr_def(pool, *base_id)),
            name.clone(),
        ),
        ExprNode::MethodCall(base_id, name, args) => {
            let args: Vec<SpannedCallArg> = args
                .iter()
                .map(|(name_opt, id)| {
                    let e = interned_to_spanned_expr_def(pool, *id);
                    match name_opt {
                        None => SpannedCallArg::Positional(Box::new(e)),
                        Some(n) => SpannedCallArg::Named(n.clone(), Box::new(e)),
                    }
                })
                .collect();
            SpannedExprDefKind::MethodCall(
                Box::new(interned_to_spanned_expr_def(pool, *base_id)),
                name.clone(),
                args,
            )
        }
        ExprNode::Eq(l, r) => SpannedExprDefKind::Eq(
            Box::new(interned_to_spanned_expr_def(pool, *l)),
            Box::new(interned_to_spanned_expr_def(pool, *r)),
        ),
        ExprNode::Ne(l, r) => SpannedExprDefKind::Ne(
            Box::new(interned_to_spanned_expr_def(pool, *l)),
            Box::new(interned_to_spanned_expr_def(pool, *r)),
        ),
        ExprNode::Lt(l, r) => SpannedExprDefKind::Lt(
            Box::new(interned_to_spanned_expr_def(pool, *l)),
            Box::new(interned_to_spanned_expr_def(pool, *r)),
        ),
        ExprNode::Le(l, r) => SpannedExprDefKind::Le(
            Box::new(interned_to_spanned_expr_def(pool, *l)),
            Box::new(interned_to_spanned_expr_def(pool, *r)),
        ),
        ExprNode::Gt(l, r) => SpannedExprDefKind::Gt(
            Box::new(interned_to_spanned_expr_def(pool, *l)),
            Box::new(interned_to_spanned_expr_def(pool, *r)),
        ),
        ExprNode::Ge(l, r) => SpannedExprDefKind::Ge(
            Box::new(interned_to_spanned_expr_def(pool, *l)),
            Box::new(interned_to_spanned_expr_def(pool, *r)),
        ),
        ExprNode::And(l, r) => SpannedExprDefKind::And(
            Box::new(interned_to_spanned_expr_def(pool, *l)),
            Box::new(interned_to_spanned_expr_def(pool, *r)),
        ),
        ExprNode::If(c, t, e) => SpannedExprDefKind::If(
            Box::new(interned_to_spanned_expr_def(pool, *c)),
            Box::new(interned_to_spanned_expr_def(pool, *t)),
            Box::new(interned_to_spanned_expr_def(pool, *e)),
        ),
        ExprNode::WithPrecision(l, r) => SpannedExprDefKind::WithPrecision(
            Box::new(interned_to_spanned_expr_def(pool, *l)),
            Box::new(interned_to_spanned_expr_def(pool, *r)),
        ),
        ExprNode::Block(ids) => SpannedExprDefKind::Block(
            ids.iter()
                .map(|&id| interned_to_spanned_expr_def(pool, id))
                .collect(),
        ),
        ExprNode::Binding(name, rhs_id) => SpannedExprDefKind::Binding(
            name.clone(),
            Box::new(interned_to_spanned_expr_def(pool, *rhs_id)),
        ),
        ExprNode::ExternalStream(name) => SpannedExprDefKind::ExternalStream(name.clone()),
        ExprNode::InputDecl(name, param_id, type_name) => {
            SpannedExprDefKind::InputDecl(name.clone(), param_id.clone(), type_name.clone())
        }
        ExprNode::MapLiteral(entries) => SpannedExprDefKind::MapLiteral(
            entries
                .iter()
                .map(|(k, id)| (k.clone(), interned_to_spanned_expr_def(pool, *id)))
                .collect(),
        ),
        ExprNode::Lambda(params, body_id) => {
            let params: Vec<(String, Option<Box<SpannedExprDef>>)> = params
                .iter()
                .map(|(name, default_id)| {
                    (
                        name.clone(),
                        default_id.map(|id| Box::new(interned_to_spanned_expr_def(pool, id))),
                    )
                })
                .collect();
            SpannedExprDefKind::Lambda(
                params,
                Box::new(interned_to_spanned_expr_def(pool, *body_id)),
            )
        }
        ExprNode::CallExpr(callee_id, args) => {
            let callee = interned_to_spanned_expr_def(pool, *callee_id);
            let args: Vec<SpannedCallArg> = args
                .iter()
                .map(|(name_opt, id)| {
                    let e = interned_to_spanned_expr_def(pool, *id);
                    match name_opt {
                        None => SpannedCallArg::Positional(Box::new(e)),
                        Some(n) => SpannedCallArg::Named(n.clone(), Box::new(e)),
                    }
                })
                .collect();
            SpannedExprDefKind::CallExpr(Box::new(callee), args)
        }
    };
    SpannedExprDef { span, value }
}

fn binaryize_add_spanned(pool: &ExprInterner, ids: &[ExprId]) -> SpannedExprDef {
    match ids {
        [] => SpannedExprDef {
            span: Span::default(),
            value: SpannedExprDefKind::Lit(crate::quantity::Quantity::from_scalar(0.0)),
        },
        [id] => interned_to_spanned_expr_def(pool, *id),
        [first, rest @ ..] => {
            let mut acc = interned_to_spanned_expr_def(pool, *first);
            for id in rest {
                let next = interned_to_spanned_expr_def(pool, *id);
                let span = Span {
                    start: acc.span.start.min(next.span.start),
                    end: acc.span.end.max(next.span.end),
                };
                acc = SpannedExprDef {
                    span,
                    value: SpannedExprDefKind::Add(Box::new(acc), Box::new(next)),
                };
            }
            acc
        }
    }
}

fn binaryize_mul_spanned(pool: &ExprInterner, ids: &[ExprId]) -> SpannedExprDef {
    match ids {
        [] => SpannedExprDef {
            span: Span::default(),
            value: SpannedExprDefKind::Lit(crate::quantity::Quantity::from_scalar(1.0)),
        },
        [id] => interned_to_spanned_expr_def(pool, *id),
        [first, rest @ ..] => {
            let mut acc = interned_to_spanned_expr_def(pool, *first);
            for id in rest {
                let next = interned_to_spanned_expr_def(pool, *id);
                let span = Span {
                    start: acc.span.start.min(next.span.start),
                    end: acc.span.end.max(next.span.end),
                };
                acc = SpannedExprDef {
                    span,
                    value: SpannedExprDefKind::Mul(Box::new(acc), Box::new(next)),
                };
            }
            acc
        }
    }
}

/// Convert an interned expression back to ExprDef (drops spans). N-ary Add/Mul are re-binaryized left-associatively.
pub fn interned_to_expr_def(pool: &ExprInterner, id: ExprId) -> ExprDef {
    interned_to_spanned_expr_def(pool, id).to_expr_def()
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
