//! Three-valued result of statistical comparisons: True, False, or Uncertain(probability).

use std::fmt;
use ordered_float::OrderedFloat;

/// Result of a statistical comparison when operands have variance.
/// Based on a confidence threshold, the comparison is confidently True, confidently False,
/// or in the ambiguous band (Uncertain with the raw probability).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum FuzzyBool {
    /// The comparison meets or exceeds the upper confidence threshold.
    True,
    /// The comparison falls at or below the lower confidence threshold.
    False,
    /// The probability falls in the ambiguous band; holds the calculated probability in [0, 1].
    Uncertain(OrderedFloat<f64>),
}

impl FuzzyBool {
    /// Returns the stored probability when Uncertain; None for True/False.
    pub fn uncertain_probability(&self) -> Option<f64> {
        match self {
            FuzzyBool::Uncertain(p) => Some(p.0),
            _ => None,
        }
    }
}

impl fmt::Display for FuzzyBool {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FuzzyBool::True => write!(f, "true"),
            FuzzyBool::False => write!(f, "false"),
            FuzzyBool::Uncertain(p) => write!(f, "uncertain({})", p.0),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fuzzy_bool_display() {
        assert_eq!(FuzzyBool::True.to_string(), "true");
        assert_eq!(FuzzyBool::False.to_string(), "false");
        assert_eq!(
            FuzzyBool::Uncertain(OrderedFloat::from(0.73)).to_string(),
            "uncertain(0.73)"
        );
    }
}
