//! Symbolic expressions: scalar expressions that can contain numbers and named symbols.
//! Used for results like "6 + π" or "2*π m". Supports simplification (collect like terms) and substitution to f64.
//! Value is the unified result type (Numeric or Symbolic).

use crate::error::RunError;
use crate::quantity::Quantity;
use crate::symbol_registry::SymbolRegistry;
use crate::unit::Unit;
use std::collections::BTreeMap;
use std::fmt;

/// Sum form: constant + monomial terms (coef, symbol list) + rest exprs (e.g. Div).
type SumForm = (f64, Vec<(f64, Vec<String>)>, Vec<SymbolicExpr>);

/// A scalar expression that can contain numbers and symbols.
#[derive(Clone, PartialEq, Debug)]
pub enum SymbolicExpr {
    Number(f64),
    Symbol(String),
    Sum {
        constant: f64,
        terms: Vec<(f64, Vec<String>)>,
        rest: Vec<SymbolicExpr>,
    },
    Product { coef: f64, symbols: Vec<String> },
    Neg(Box<SymbolicExpr>),
    Div(Box<SymbolicExpr>, Box<SymbolicExpr>),
}

impl SymbolicExpr {
    pub fn number(x: f64) -> Self {
        SymbolicExpr::Number(x)
    }

    pub fn symbol(name: impl Into<String>) -> Self {
        SymbolicExpr::Symbol(name.into())
    }

    /// Convert this expr to "sum form": (constant, list of (coef, symbol_list)).
    /// Sum form: (constant, monomial terms, rest exprs like Div that don't simplify to monomials).
    fn to_sum_form(&self) -> SumForm {
        match self {
            SymbolicExpr::Number(x) => (*x, Vec::new(), Vec::new()),
            SymbolicExpr::Symbol(s) => (0.0, vec![(1.0, vec![s.clone()])], Vec::new()),
            SymbolicExpr::Sum {
                constant,
                terms,
                rest,
            } => (*constant, terms.clone(), rest.clone()),
            SymbolicExpr::Product { coef, symbols } => {
                (0.0, vec![(*coef, symbols.clone())], Vec::new())
            }
            SymbolicExpr::Neg(inner) => {
                let (c, t, r) = inner.to_sum_form();
                let terms = t.into_iter().map(|(k, s)| (-k, s)).collect();
                let rest = r.into_iter().map(|e| Self::neg(&e)).collect();
                (-c, terms, rest)
            }
            SymbolicExpr::Div(a, b) => (0.0, Vec::new(), vec![SymbolicExpr::Div(a.clone(), b.clone())]),
        }
    }

    /// Merge two sum forms: add constants, merge like terms, concatenate rest.
    fn merge_sum_forms((c1, t1, r1): SumForm, (c2, t2, r2): SumForm) -> SumForm {
        let mut constant = c1 + c2;
        let mut map: BTreeMap<Vec<String>, f64> = BTreeMap::new();
        for (coef, symbols) in t1.into_iter().chain(t2) {
            let key = {
                let mut s = symbols;
                s.sort();
                s
            };
            if key.is_empty() {
                constant += coef;
            } else {
                *map.entry(key).or_insert(0.0) += coef;
            }
        }
        let terms: Vec<(f64, Vec<String>)> = map
            .into_iter()
            .filter(|(_, c)| *c != 0.0)
            .map(|(s, c)| (c, s))
            .collect();
        let mut rest = r1;
        rest.extend(r2);
        (constant, terms, rest)
    }

    pub fn add(a: &SymbolicExpr, b: &SymbolicExpr) -> SymbolicExpr {
        let form = Self::merge_sum_forms(a.to_sum_form(), b.to_sum_form());
        Self::from_sum_form(form.0, form.1, form.2)
    }

    fn from_sum_form(
        constant: f64,
        terms: Vec<(f64, Vec<String>)>,
        rest: Vec<SymbolicExpr>,
    ) -> SymbolicExpr {
        let terms: Vec<(f64, Vec<String>)> = terms.into_iter().filter(|(c, _)| *c != 0.0).collect();
        if terms.is_empty() && rest.is_empty() {
            return SymbolicExpr::Number(constant);
        }
        if constant == 0.0 && terms.len() == 1 && rest.is_empty() {
            let (c, s) = &terms[0];
            if *c == 1.0 && s.len() == 1 {
                return SymbolicExpr::Symbol(s[0].clone());
            }
            if *c == 1.0 && s.len() > 1 {
                return SymbolicExpr::Product {
                    coef: 1.0,
                    symbols: s.clone(),
                };
            }
            if s.is_empty() {
                return SymbolicExpr::Number(*c);
            }
        }
        SymbolicExpr::Sum {
            constant,
            terms,
            rest,
        }
    }

    /// Convert to "product form" (coef, symbols) if this is a product-like expr (Number, Symbol, or Product). None for Sum.
    fn to_product_form(&self) -> Option<(f64, Vec<String>)> {
        match self {
            SymbolicExpr::Number(x) => Some((*x, Vec::new())),
            SymbolicExpr::Symbol(s) => Some((1.0, vec![s.clone()])),
            SymbolicExpr::Product { coef, symbols } => Some((*coef, symbols.clone())),
            SymbolicExpr::Sum { .. } | SymbolicExpr::Neg(..) | SymbolicExpr::Div(..) => None,
        }
    }

    /// Multiply two expressions. If either is a Sum, distribute.
    pub fn mul(a: &SymbolicExpr, b: &SymbolicExpr) -> SymbolicExpr {
        let ap = a.to_product_form();
        let bp = b.to_product_form();
        match (ap, bp) {
            (Some((c1, s1)), Some((c2, s2))) => {
                let mut symbols = s1;
                symbols.extend(s2);
                symbols.sort();
                SymbolicExpr::from_product_form(c1 * c2, symbols)
            }
            (Some(_), None) => {
                let (bc, bterms, brest) = b.to_sum_form();
                let mut acc = Self::mul(a, &SymbolicExpr::Number(bc));
                for (coef, syms) in bterms {
                    let term = SymbolicExpr::from_product_form(coef, syms);
                    acc = SymbolicExpr::add(&acc, &Self::mul(a, &term));
                }
                for r in brest {
                    acc = SymbolicExpr::add(&acc, &Self::mul(a, &r));
                }
                acc
            }
            (None, Some(_)) => Self::mul(b, a),
            (None, None) => {
                let (ac, aterms, arest) = a.to_sum_form();
                let mut acc = Self::mul(&SymbolicExpr::Number(ac), b);
                for (coef, syms) in aterms {
                    let term = SymbolicExpr::from_product_form(coef, syms);
                    acc = SymbolicExpr::add(&acc, &Self::mul(&term, b));
                }
                for r in arest {
                    acc = SymbolicExpr::add(&acc, &Self::mul(&r, b));
                }
                acc
            }
        }
    }

    fn from_product_form(coef: f64, mut symbols: Vec<String>) -> SymbolicExpr {
        symbols.retain(|s| !s.is_empty());
        if coef == 0.0 {
            return SymbolicExpr::Number(0.0);
        }
        if symbols.is_empty() {
            return SymbolicExpr::Number(coef);
        }
        if coef == 1.0 && symbols.len() == 1 {
            return SymbolicExpr::Symbol(symbols.into_iter().next().unwrap());
        }
        if coef == -1.0 && symbols.len() == 1 {
            return SymbolicExpr::Neg(Box::new(SymbolicExpr::Symbol(
                symbols.into_iter().next().unwrap(),
            )));
        }
        SymbolicExpr::Product { coef, symbols }
    }

    pub fn neg(expr: &SymbolicExpr) -> SymbolicExpr {
        let (c, t, r) = expr.to_sum_form();
        let terms = t.into_iter().map(|(k, s)| (-k, s)).collect();
        let rest = r.into_iter().map(|e| Self::neg(&e)).collect();
        Self::from_sum_form(-c, terms, rest)
    }

    pub fn sub(a: &SymbolicExpr, b: &SymbolicExpr) -> SymbolicExpr {
        Self::add(a, &Self::neg(b))
    }

    /// Divide a by b. If both are product-like, returns simplified product form; else returns Div(a, b).
    /// When numerator is Neg(inner), simplifies to neg(inner/b) so e.g. (-2 abc)/2 -> -abc.
    pub fn div(a: &SymbolicExpr, b: &SymbolicExpr) -> SymbolicExpr {
        if let SymbolicExpr::Neg(inner) = a {
            return Self::neg(&Self::div(inner, b));
        }
        let (bcoef, bsyms) = match b.to_product_form() {
            Some(x) => x,
            None => return SymbolicExpr::Div(Box::new(a.clone()), Box::new(b.clone())),
        };
        if bcoef == 0.0 {
            return SymbolicExpr::Div(Box::new(a.clone()), Box::new(b.clone()));
        }
        let (acoef, asyms) = match a.to_product_form() {
            Some(x) => x,
            None => return SymbolicExpr::Div(Box::new(a.clone()), Box::new(b.clone())),
        };
        let mut syms: Vec<String> = asyms;
        for s in bsyms {
            if let Some(pos) = syms.iter().position(|x| x == &s) {
                syms.remove(pos);
            } else {
                syms.push(format!("{s}⁻¹"));
            }
        }
        SymbolicExpr::from_product_form(acoef / bcoef, syms)
    }

    /// Substitute all symbols with their values from the registry. Returns None if any symbol has no value.
    pub fn substitute(&self, registry: &crate::symbol_registry::SymbolRegistry) -> Option<f64> {
        match self {
            SymbolicExpr::Number(x) => Some(*x),
            SymbolicExpr::Symbol(s) => registry.get(s),
            SymbolicExpr::Sum {
                constant,
                terms,
                rest,
            } => {
                let mut sum = *constant;
                for (coef, syms) in terms {
                    let mut term = *coef;
                    for s in syms {
                        term *= registry.get(s)?;
                    }
                    sum += term;
                }
                for r in rest {
                    sum += r.substitute(registry)?;
                }
                Some(sum)
            }
            SymbolicExpr::Product { coef, symbols } => {
                let mut p = *coef;
                for s in symbols {
                    if s.ends_with("⁻¹") {
                        let name = s.trim_end_matches("⁻¹");
                        p /= registry.get(name)?;
                    } else {
                        p *= registry.get(s)?;
                    }
                }
                Some(p)
            }
            SymbolicExpr::Neg(inner) => inner.substitute(registry).map(|x| -x),
            SymbolicExpr::Div(a, b) => {
                let av = a.substitute(registry)?;
                let bv = b.substitute(registry)?;
                if bv == 0.0 {
                    None
                } else {
                    Some(av / bv)
                }
            }
        }
    }

    /// Substitute and return the first missing symbol name on error.
    pub fn substitute_or_err(
        &self,
        registry: &crate::symbol_registry::SymbolRegistry,
    ) -> Result<f64, String> {
        match self {
            SymbolicExpr::Number(x) => Ok(*x),
            SymbolicExpr::Symbol(s) => registry
                .get(s)
                .ok_or_else(|| s.clone()),
            SymbolicExpr::Sum {
                constant,
                terms,
                rest,
            } => {
                let mut sum = *constant;
                for (coef, syms) in terms {
                    let mut term = *coef;
                    for s in syms {
                        term *= registry.get(s).ok_or_else(|| s.clone())?;
                    }
                    sum += term;
                }
                for r in rest {
                    sum += r.substitute_or_err(registry)?;
                }
                Ok(sum)
            }
            SymbolicExpr::Product { coef, symbols } => {
                let mut p = *coef;
                for s in symbols {
                    if s.ends_with("⁻¹") {
                        let name = s.trim_end_matches("⁻¹");
                        p /= registry.get(name).ok_or_else(|| name.to_string())?;
                    } else {
                        p *= registry.get(s).ok_or_else(|| s.clone())?;
                    }
                }
                Ok(p)
            }
            SymbolicExpr::Neg(inner) => inner.substitute_or_err(registry).map(|x| -x),
            SymbolicExpr::Div(a, b) => {
                let av = a.substitute_or_err(registry)?;
                let bv = b.substitute_or_err(registry)?;
                if bv == 0.0 {
                    Err("division by zero".to_string())
                } else {
                    Ok(av / bv)
                }
            }
        }
    }
}

impl fmt::Display for SymbolicExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SymbolicExpr::Number(x) => {
                if *x == f64::INFINITY {
                    write!(f, "∞")
                } else if *x == f64::NEG_INFINITY {
                    write!(f, "-∞")
                } else {
                    write!(f, "{x}")
                }
            }
            SymbolicExpr::Symbol(s) => {
                if s == "pi" {
                    write!(f, "π")
                } else {
                    write!(f, "{s}")
                }
            }
            SymbolicExpr::Sum {
                constant,
                terms,
                rest,
            } => {
                let mut first = true;
                if *constant != 0.0 {
                    write!(f, "{constant}")?;
                    first = false;
                }
                for (coef, syms) in terms {
                    if !first {
                        write!(f, " + ")?;
                    }
                    first = false;
                    if *coef == 1.0 && !syms.is_empty() {
                        format_symbols(f, syms)?;
                    } else if *coef == -1.0 && !syms.is_empty() {
                        write!(f, "-")?;
                        format_symbols(f, syms)?;
                    } else {
                        write!(f, "{coef}*")?;
                        format_symbols(f, syms)?;
                    }
                }
                for expr in rest {
                    if !first {
                        write!(f, " + ")?;
                    }
                    first = false;
                    write!(f, "({expr})")?;
                }
                Ok(())
            }
            SymbolicExpr::Product { coef, symbols } => {
                if *coef != 1.0 || symbols.is_empty() {
                    write!(f, "{coef}")?;
                    if !symbols.is_empty() {
                        write!(f, "*")?;
                    }
                }
                format_symbols(f, symbols)?;
                Ok(())
            }
            SymbolicExpr::Neg(inner) => write!(f, "-({inner})"),
            SymbolicExpr::Div(a, b) => write!(f, "({a}) / ({b})"),
        }
    }
}

fn format_symbols(f: &mut fmt::Formatter<'_>, symbols: &[String]) -> fmt::Result {
    for (i, s) in symbols.iter().enumerate() {
        if i > 0 {
            write!(f, "*")?;
        }
        if s.ends_with("⁻¹") {
            write!(f, "1/{}", s.trim_end_matches("⁻¹"))?;
        } else if s == "pi" {
            write!(f, "π")?;
        } else {
            write!(f, "{s}")?;
        }
    }
    Ok(())
}

/// A symbolic expression with a unit (e.g. "6 + π" or "2*π m").
#[derive(Clone, PartialEq, Debug)]
pub struct SymbolicQuantity {
    pub expr: SymbolicExpr,
    pub unit: Unit,
}

impl SymbolicQuantity {
    pub fn new(expr: SymbolicExpr, unit: Unit) -> Self {
        Self { expr, unit }
    }

    pub fn scalar(expr: SymbolicExpr) -> Self {
        Self::new(expr, Unit::scalar())
    }

    pub fn substitute(
        &self,
        registry: &crate::symbol_registry::SymbolRegistry,
    ) -> Option<crate::quantity::Quantity> {
        let value = self.expr.substitute(registry)?;
        Some(crate::quantity::Quantity::new(value, self.unit.clone()))
    }

    pub fn substitute_or_err(
        &self,
        registry: &crate::symbol_registry::SymbolRegistry,
    ) -> Result<crate::quantity::Quantity, RunError> {
        self.expr
            .substitute_or_err(registry)
            .map(|v| crate::quantity::Quantity::new(v, self.unit.clone()))
            .map_err(|s| {
                if s == "division by zero" {
                    RunError::DivisionByZero
                } else {
                    RunError::SymbolHasNoValue(s)
                }
            })
    }
}

impl fmt::Display for SymbolicQuantity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.unit.is_scalar() {
            write!(f, "{}", self.expr)
        } else {
            write!(f, "{} {}", self.expr, self.unit)
        }
    }
}

/// Result of evaluation: either a numeric quantity or a symbolic expression (with optional unit).
///
/// Use [Value::to_string] for display (e.g. `"6 + π"` or `"1000 + π m"`). Use [Value::to_quantity]
/// with a [crate::SymbolRegistry] to substitute symbols and get a single [crate::Quantity].
#[derive(Clone, PartialEq, Debug)]
pub enum Value {
    Numeric(Quantity),
    Symbolic(SymbolicQuantity),
}

impl Value {
    pub fn numeric(q: Quantity) -> Self {
        Value::Numeric(q)
    }

    pub fn symbolic(sq: SymbolicQuantity) -> Self {
        Value::Symbolic(sq)
    }

    /// Substitute all symbols and return a single Quantity. Errors if any symbol has no value.
    pub fn to_quantity(&self, registry: &SymbolRegistry) -> Result<Quantity, RunError> {
        match self {
            Value::Numeric(q) => Ok(q.clone()),
            Value::Symbolic(sq) => sq.substitute_or_err(registry),
        }
    }

    /// Return the numeric value only if this is Numeric; otherwise try substitution.
    pub fn as_scalar_with_registry(
        &self,
        registry: &SymbolRegistry,
    ) -> Result<f64, RunError> {
        let q = self.to_quantity(registry)?;
        q.as_scalar().map_err(|_| RunError::DimensionMismatch {
            left: q.unit().clone(),
            right: Unit::scalar(),
        })
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Numeric(q) => write!(f, "{q}"),
            Value::Symbolic(sq) => write!(f, "{sq}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol_registry::SymbolRegistry;

    #[test]
    fn sum_simplifies_like_terms() {
        let a = SymbolicExpr::add(
            &SymbolicExpr::Number(3.0),
            &SymbolicExpr::Number(2.0),
        );
        let b = SymbolicExpr::add(&a, &SymbolicExpr::symbol("pi"));
        let c = SymbolicExpr::add(&b, &SymbolicExpr::Number(1.0));
        let (constant, terms, rest) = c.to_sum_form();
        assert!((constant - 6.0).abs() < 1e-10);
        assert!(rest.is_empty());
        assert_eq!(terms.len(), 1);
        assert_eq!(terms[0].0, 1.0);
        assert_eq!(terms[0].1, vec!["pi"]);
    }

    #[test]
    fn product_simplifies() {
        let p = SymbolicExpr::mul(
            &SymbolicExpr::Number(2.0),
            &SymbolicExpr::mul(&SymbolicExpr::symbol("pi"), &SymbolicExpr::Number(3.0)),
        );
        let form = p.to_product_form().unwrap();
        assert!((form.0 - 6.0).abs() < 1e-10);
        assert_eq!(form.1, vec!["pi"]);
    }

    #[test]
    fn substitute_pi() {
        let r = SymbolRegistry::default_registry();
        let e = SymbolicExpr::add(&SymbolicExpr::Number(1.0), &SymbolicExpr::symbol("pi"));
        let v = e.substitute(&r).unwrap();
        assert!((v - (1.0 + std::f64::consts::PI)).abs() < 1e-10);
    }

    #[test]
    fn div_neg_product_simplifies_to_neg_symbol() {
        // (-2*abc)/2 should simplify to -abc (not -1*abc)
        let num = SymbolicExpr::mul(
            &SymbolicExpr::neg(&SymbolicExpr::Number(2.0)),
            &SymbolicExpr::symbol("abc"),
        );
        let den = SymbolicExpr::Number(2.0);
        let result = SymbolicExpr::div(&num, &den);
        let s = result.to_string();
        assert!(s.contains("abc") && (s.contains('-') || s.starts_with('-')), "expected -abc, got {s}");
        assert!(!s.contains("1*"), "should not show -1*abc");
    }
}
