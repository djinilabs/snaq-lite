//! Metric and binary prefixes for units (e.g. kilo, milli, kibi).

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Prefix {
    /// Metric (decimal): 10^n.
    Metric(i32),
    /// Binary: 2^n.
    Binary(i32),
}

impl Prefix {
    /// Conversion factor: 10^n or 2^n.
    pub fn factor(&self) -> f64 {
        match self {
            Prefix::Metric(exp) => 10.0f64.powi(*exp),
            Prefix::Binary(exp) => 2.0f64.powi(*exp),
        }
    }

    pub fn none() -> Self {
        Prefix::Metric(0)
    }

    pub fn is_none(&self) -> bool {
        matches!(self, Prefix::Metric(0) | Prefix::Binary(0))
    }

    /// Short symbol for display (e.g. k, m, µ, M). Returns empty string for none.
    pub fn short_symbol(&self) -> &'static str {
        match self {
            Prefix::Metric(0) | Prefix::Binary(0) => "",
            Prefix::Metric(24) => "Y",
            Prefix::Metric(21) => "Z",
            Prefix::Metric(18) => "E",
            Prefix::Metric(15) => "P",
            Prefix::Metric(12) => "T",
            Prefix::Metric(9) => "G",
            Prefix::Metric(6) => "M",
            Prefix::Metric(3) => "k",
            Prefix::Metric(2) => "h",
            Prefix::Metric(1) => "da",
            Prefix::Metric(-1) => "d",
            Prefix::Metric(-2) => "c",
            Prefix::Metric(-3) => "m",
            Prefix::Metric(-6) => "µ",
            Prefix::Metric(-9) => "n",
            Prefix::Metric(-12) => "p",
            Prefix::Metric(-15) => "f",
            Prefix::Metric(-18) => "a",
            Prefix::Metric(-21) => "z",
            Prefix::Metric(-24) => "y",
            Prefix::Binary(10) => "Ki",
            Prefix::Binary(20) => "Mi",
            Prefix::Binary(30) => "Gi",
            Prefix::Binary(40) => "Ti",
            _ => "",
        }
    }

    pub fn kilo() -> Self {
        Prefix::Metric(3)
    }
    pub fn milli() -> Self {
        Prefix::Metric(-3)
    }
    pub fn centi() -> Self {
        Prefix::Metric(-2)
    }
    pub fn micro() -> Self {
        Prefix::Metric(-6)
    }
}

/// Pairs of (short symbol, prefix) for parsing, sorted by symbol length descending (longest first).
pub fn metric_short_prefixes() -> [(&'static str, Prefix); 20] {
    [
        ("da", Prefix::Metric(1)),
        ("µ", Prefix::Metric(-6)),
        ("Y", Prefix::Metric(24)),
        ("Z", Prefix::Metric(21)),
        ("E", Prefix::Metric(18)),
        ("P", Prefix::Metric(15)),
        ("T", Prefix::Metric(12)),
        ("G", Prefix::Metric(9)),
        ("M", Prefix::Metric(6)),
        ("k", Prefix::Metric(3)),
        ("h", Prefix::Metric(2)),
        ("d", Prefix::Metric(-1)),
        ("c", Prefix::Metric(-2)),
        ("m", Prefix::Metric(-3)),
        ("n", Prefix::Metric(-9)),
        ("p", Prefix::Metric(-12)),
        ("f", Prefix::Metric(-15)),
        ("a", Prefix::Metric(-18)),
        ("z", Prefix::Metric(-21)),
        ("y", Prefix::Metric(-24)),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prefix_none_factor_is_one() {
        assert!((Prefix::none().factor() - 1.0).abs() < 1e-10);
    }

    #[test]
    fn prefix_kilo_factor() {
        assert!((Prefix::kilo().factor() - 1000.0).abs() < 1e-10);
    }

    #[test]
    fn prefix_milli_factor() {
        assert!((Prefix::milli().factor() - 0.001).abs() < 1e-10);
    }
}
