//! Query group: build expression graph and evaluate.
//!
//! When inputs (`ProgramDef`) change, Salsa invalidates only the memoized
//! results that depended on them, so recomputation is incremental.
//! Evaluation returns Value (Numeric or Symbolic).

use crate::error::RunError;
use crate::functions;
use crate::ir::{CallArg, ExprData, ExprDef, Expression, ProgramDef};
use crate::quantity::Quantity;
use crate::symbolic::{SymbolicExpr, SymbolicQuantity, Value};
use crate::unit::Unit;
use crate::unit_registry::UnitRegistry;
use std::cell::RefCell;
use std::collections::HashMap;
use std::ops::Neg;

thread_local! {
    /// Registry used during evaluation (set by run()).
    static EVAL_REGISTRY: RefCell<Option<UnitRegistry>> = const { RefCell::new(None) };
}

/// Set the unit registry for the current thread (used by run() before evaluation).
pub fn set_eval_registry(registry: UnitRegistry) {
    EVAL_REGISTRY.with(|r| *r.borrow_mut() = Some(registry));
}

fn with_registry<R, F: FnOnce(&UnitRegistry) -> R>(f: F) -> R {
    EVAL_REGISTRY.with(|r| {
        let reg = r.borrow();
        let reg = reg.as_ref().expect("unit registry not set; use run() or set_eval_registry()");
        f(reg)
    })
}

/// Build the tracked expression graph from the program definition; returns the root.
/// Expects root to be fully resolved (only Lit(Quantity) | Add | Sub | Mul | Div).
#[salsa::tracked]
pub fn program(db: &dyn salsa::Database, program_def: ProgramDef) -> Expression<'_> {
    let root_def = program_def.root(db);
    build_expression(db, root_def.clone())
}

/// Recursively build tracked Expression nodes from ExprDef.
fn build_expression(db: &dyn salsa::Database, def: ExprDef) -> Expression<'_> {
    let data = match def {
        ExprDef::Lit(q) => ExprData::Lit(q),
        ExprDef::LitSymbol(name) => ExprData::LitSymbol(name),
        ExprDef::LitScalar(..) | ExprDef::LitWithUnit(..) | ExprDef::LitUnit(..) => {
            panic!("unresolved expression: resolve() must be called before building the graph")
        }
        ExprDef::Add(l, r) => {
            let left = build_expression(db, *l);
            let right = build_expression(db, *r);
            ExprData::Add(left, right)
        }
        ExprDef::Sub(l, r) => {
            let left = build_expression(db, *l);
            let right = build_expression(db, *r);
            ExprData::Sub(left, right)
        }
        ExprDef::Mul(l, r) => {
            let left = build_expression(db, *l);
            let right = build_expression(db, *r);
            ExprData::Mul(left, right)
        }
        ExprDef::Div(l, r) => {
            let left = build_expression(db, *l);
            let right = build_expression(db, *r);
            ExprData::Div(left, right)
        }
        ExprDef::Neg(inner) => {
            let inner_expr = build_expression(db, *inner);
            ExprData::Neg(inner_expr)
        }
        ExprDef::Call(name, args) => {
            let arg_exprs: Vec<(Option<String>, Expression<'_>)> = args
                .into_iter()
                .map(|arg| match arg {
                    CallArg::Positional(e) => (None, build_expression(db, *e)),
                    CallArg::Named(n, e) => (Some(n), build_expression(db, *e)),
                })
                .collect();
            ExprData::Call(name, arg_exprs)
        }
    };
    Expression::new(db, data)
}

/// Evaluate an expression to a Value (Numeric or Symbolic). Uses the registry set by run() (thread-local).
///
/// Memoized per `expr`; when any child's value changes,
/// only dependent entries are recomputed.
#[salsa::tracked]
pub fn value(db: &dyn salsa::Database, expr: Expression<'_>) -> Result<Value, RunError> {
    let data = expr.data(db);
    with_registry(|registry| match data {
        ExprData::Lit(q) => Ok(Value::Numeric(q.clone())),
        ExprData::LitSymbol(name) => Ok(Value::Symbolic(SymbolicQuantity::new(
            SymbolicExpr::symbol(name),
            Unit::scalar(),
        ))),
        ExprData::Add(l, r) => {
            let left = value(db, *l)?;
            let right = value(db, *r)?;
            add_values(&left, &right, registry)
        }
        ExprData::Sub(l, r) => {
            let left = value(db, *l)?;
            let right = value(db, *r)?;
            sub_values(&left, &right, registry)
        }
        ExprData::Mul(l, r) => {
            let left = value(db, *l)?;
            let right = value(db, *r)?;
            mul_values(&left, &right)
        }
        ExprData::Div(l, r) => {
            let left = value(db, *l)?;
            let right = value(db, *r)?;
            div_values(&left, &right)
        }
        ExprData::Neg(inner) => {
            let v = value(db, *inner)?;
            neg_value(&v)
        }
        ExprData::Call(name, args) => eval_call(db, name, args, registry),
    })
}

/// Bind call args (positional + named) to param names and evaluate.
fn eval_call(
    db: &dyn salsa::Database,
    name: &str,
    args: &[(Option<String>, Expression<'_>)],
    registry: &UnitRegistry,
) -> Result<Value, RunError> {
    let param_names = functions::param_names(name)
        .ok_or_else(|| RunError::UnknownFunction(name.to_string()))?;
    let mut bound: HashMap<String, Value> = HashMap::new();
    for (i, (opt_name, expr)) in args.iter().enumerate() {
        let v = value(db, *expr)?;
        let param = match opt_name {
            Some(n) => {
                if !param_names.contains(&n.as_str()) {
                    return Err(RunError::UnknownFunction(format!(
                        "{name}: unknown parameter name '{n}'"
                    )));
                }
                if bound.contains_key(n) {
                    return Err(RunError::UnknownFunction(format!(
                        "{name}: duplicate parameter '{n}'"
                    )));
                }
                n.clone()
            }
            None => {
                param_names
                    .get(i)
                    .copied()
                    .map(String::from)
                    .ok_or_else(|| {
                        RunError::UnknownFunction(format!(
                            "{name}: too many arguments (expected {})",
                            param_names.len()
                        ))
                    })?
            }
        };
        bound.insert(param, v);
    }
    for p in param_names.iter() {
        if !bound.contains_key(*p) {
            return Err(RunError::UnknownFunction(format!(
                "{name}: missing argument for parameter '{p}'"
            )));
        }
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
        Ok(qs) => functions::call_builtin(name, &qs, registry),
        Err(_) => {
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
    }
}

fn add_values(
    a: &Value,
    b: &Value,
    registry: &UnitRegistry,
) -> Result<Value, RunError> {
    match (a, b) {
        (Value::Numeric(qa), Value::Numeric(qb)) => qa
            .clone()
            .add(qb, registry)
            .map(Value::Numeric)
            .map_err(|e| match e {
                crate::quantity::QuantityError::DimensionMismatch { left, right } => {
                    RunError::DimensionMismatch { left, right }
                }
                _ => RunError::DivisionByZero,
            }),
        _ => {
            let (ea, ua) = value_to_expr_unit(a);
            let (eb, ub) = value_to_expr_unit(b);
            if !registry.same_dimension(&ua, &ub).unwrap_or(false) {
                return Err(RunError::DimensionMismatch {
                    left: ua.clone(),
                    right: ub.clone(),
                });
            }
            let result_unit = Quantity::smaller_unit(registry, &ua, &ub)
                .cloned()
                .unwrap_or_else(|| ua.clone());
            let ea_scaled = scale_expr_to_unit(a, &ea, &ua, &result_unit, registry)?;
            let eb_scaled = scale_expr_to_unit(b, &eb, &ub, &result_unit, registry)?;
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
) -> Result<Value, RunError> {
    match (a, b) {
        (Value::Numeric(qa), Value::Numeric(qb)) => qa
            .clone()
            .sub(qb, registry)
            .map(Value::Numeric)
            .map_err(|e| match e {
                crate::quantity::QuantityError::DimensionMismatch { left, right } => {
                    RunError::DimensionMismatch { left, right }
                }
                _ => RunError::DivisionByZero,
            }),
        _ => {
            let (ea, ua) = value_to_expr_unit(a);
            let (eb, ub) = value_to_expr_unit(b);
            if !registry.same_dimension(&ua, &ub).unwrap_or(false) {
                return Err(RunError::DimensionMismatch {
                    left: ua.clone(),
                    right: ub.clone(),
                });
            }
            let result_unit = Quantity::smaller_unit(registry, &ua, &ub)
                .cloned()
                .unwrap_or_else(|| ua.clone());
            let ea_scaled = scale_expr_to_unit(a, &ea, &ua, &result_unit, registry)?;
            let eb_scaled = scale_expr_to_unit(b, &eb, &ub, &result_unit, registry)?;
            Ok(Value::Symbolic(SymbolicQuantity::new(
                SymbolicExpr::sub(&ea_scaled, &eb_scaled),
                result_unit,
            )))
        }
    }
}

fn mul_values(a: &Value, b: &Value) -> Result<Value, RunError> {
    match (a, b) {
        (Value::Numeric(qa), Value::Numeric(qb)) => Ok(Value::Numeric(qa.clone() * qb.clone())),
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

fn div_values(a: &Value, b: &Value) -> Result<Value, RunError> {
    match (a, b) {
        (Value::Numeric(qa), Value::Numeric(qb)) => (qa.clone() / qb.clone())
            .map(Value::Numeric)
            .map_err(|_| RunError::DivisionByZero),
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

fn neg_value(v: &Value) -> Result<Value, RunError> {
    match v {
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
        .ok_or_else(|| RunError::DimensionMismatch {
            left: from_unit.clone(),
            right: to_unit.clone(),
        })?;
    let (_, to_factor) = registry
        .to_base_unit_representation(to_unit)
        .ok_or_else(|| RunError::DimensionMismatch {
            left: from_unit.clone(),
            right: to_unit.clone(),
        })?;
    let ratio = from_factor / to_factor;
    match v {
        Value::Numeric(q) => {
            let converted = q
                .clone()
                .convert_to(registry, to_unit)
                .map_err(|e| match e {
                    crate::quantity::QuantityError::DimensionMismatch { left, right } => {
                        RunError::DimensionMismatch { left, right }
                    }
                    _ => RunError::DivisionByZero,
                })?;
            Ok(SymbolicExpr::number(converted.value()))
        }
        Value::Symbolic(_) => Ok(SymbolicExpr::mul(expr, &SymbolicExpr::number(ratio))),
    }
}
