//! Statistical comparison for numbers with variance: P(A > B) and mapping to FuzzyBool.

use crate::fuzzy::FuzzyBool;
use crate::quantity::SnaqNumber;
use ordered_float::OrderedFloat;
use statrs::function::erf::erf;

/// Default confidence threshold (e.g. 95%): prob >= this → True, prob <= (1 - this) → False.
pub const CONFIDENCE_THRESHOLD: f64 = 0.95;

/// Tolerance for treating two means as equal (e.g. for Ge/Le when A ≈ B).
pub const MEANS_EQUAL_TOLERANCE: f64 = 1e-15;

/// Kind of comparison; used to compute the probability for that op from two SnaqNumbers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ComparisonKind {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// Returns the probability that A > B for two independent Gaussian variables.
///
/// Uses the distribution of (A - B): mean_diff = E[A] - E[B], var_diff = Var(A) + Var(B).
/// If both have zero variance, returns 1.0 or 0.0 from a crisp comparison.
/// Returns 0.5 if the result would be non-finite (e.g. degenerate inputs).
pub fn probability_a_gt_b(a: SnaqNumber, b: SnaqNumber) -> f64 {
    let mean_diff = a.value() - b.value();
    let var_diff = a.variance() + b.variance();

    if var_diff == 0.0 {
        return if a.value() > b.value() { 1.0 } else { 0.0 };
    }

    let std_dev = var_diff.sqrt();
    let z = (0.0 - mean_diff) / std_dev;
    // P(A > B) = P(A - B > 0) = 0.5 * (1 - erf(z / sqrt(2)))
    let p = 0.5 * (1.0 - erf(z / std::f64::consts::SQRT_2));
    let clamped = p.clamp(0.0, 1.0);
    if clamped.is_finite() {
        clamped
    } else {
        0.5
    }
}

/// Returns the probability that the comparison (kind) holds given two SnaqNumbers.
///
/// Encapsulates exact (zero variance) and equal-means (Ge/Le) handling; otherwise
/// uses P(A > B) and the standard derivations (Lt/Le: 1 - P; Eq/Ne: symmetric).
pub fn comparison_probability(kind: ComparisonKind, na: SnaqNumber, nb: SnaqNumber) -> f64 {
    let var_diff = na.variance() + nb.variance();
    let means_equal = (na.value() - nb.value()).abs() < MEANS_EQUAL_TOLERANCE;
    let p_gt = probability_a_gt_b(na, nb);

    match kind {
        ComparisonKind::Eq => {
            if var_diff == 0.0 {
                if means_equal {
                    1.0
                } else {
                    0.0
                }
            } else {
                2.0 * p_gt.min(1.0 - p_gt)
            }
        }
        ComparisonKind::Ne => {
            if var_diff == 0.0 {
                if !means_equal {
                    1.0
                } else {
                    0.0
                }
            } else {
                1.0 - 2.0 * p_gt.min(1.0 - p_gt)
            }
        }
        ComparisonKind::Lt => {
            if var_diff == 0.0 {
                if na.value() < nb.value() {
                    1.0
                } else {
                    0.0
                }
            } else {
                1.0 - p_gt
            }
        }
        ComparisonKind::Le => {
            if var_diff == 0.0 {
                if na.value() <= nb.value() {
                    1.0
                } else {
                    0.0
                }
            } else if means_equal {
                1.0
            } else {
                1.0 - p_gt
            }
        }
        ComparisonKind::Gt => {
            if var_diff == 0.0 {
                if na.value() > nb.value() {
                    1.0
                } else {
                    0.0
                }
            } else {
                p_gt
            }
        }
        ComparisonKind::Ge => {
            if var_diff == 0.0 {
                if na.value() >= nb.value() {
                    1.0
                } else {
                    0.0
                }
            } else if means_equal {
                1.0
            } else {
                p_gt
            }
        }
    }
}

/// Maps a raw probability to FuzzyBool using the given confidence threshold.
///
/// - prob >= confidence → True
/// - prob <= (1 - confidence) → False
/// - otherwise → Uncertain(prob)
pub fn probability_to_fuzzy_bool(prob: f64, confidence: f64) -> FuzzyBool {
    let lower = 1.0 - confidence;
    if prob >= confidence {
        FuzzyBool::True
    } else if prob <= lower {
        FuzzyBool::False
    } else {
        FuzzyBool::Uncertain(OrderedFloat::from(prob))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn probability_a_gt_b_exact_both_zero_var() {
        let a = SnaqNumber::new(3.0, 0.0);
        let b = SnaqNumber::new(2.0, 0.0);
        assert_eq!(probability_a_gt_b(a, b), 1.0);
        assert_eq!(probability_a_gt_b(b, a), 0.0);
        assert_eq!(probability_a_gt_b(a, a), 0.0);
    }

    #[test]
    fn probability_a_gt_b_clear_ordering() {
        let a = SnaqNumber::new(10.0, 0.1);
        let b = SnaqNumber::new(5.0, 0.1);
        let p = probability_a_gt_b(a, b);
        assert!(p > 0.99, "P(10 > 5) should be near 1, got {}", p);
        let p_rev = probability_a_gt_b(b, a);
        assert!(p_rev < 0.01, "P(5 > 10) should be near 0, got {}", p_rev);
    }

    #[test]
    fn probability_a_gt_b_overlapping() {
        let a = SnaqNumber::new(0.0, 1.0);
        let b = SnaqNumber::new(0.0, 1.0);
        let p = probability_a_gt_b(a, b);
        assert!(p > 0.4 && p < 0.6, "P(0>0 with same var) should be ~0.5, got {}", p);
    }

    #[test]
    fn probability_to_fuzzy_bool_threshold() {
        assert!(matches!(
            probability_to_fuzzy_bool(0.96, 0.95),
            FuzzyBool::True
        ));
        assert!(matches!(
            probability_to_fuzzy_bool(0.04, 0.95),
            FuzzyBool::False
        ));
        let u = probability_to_fuzzy_bool(0.5, 0.95);
        assert!(matches!(u, FuzzyBool::Uncertain(p) if (p.0 - 0.5).abs() < 1e-10));
    }

    #[test]
    fn comparison_probability_ge_equal_means() {
        let a = SnaqNumber::new(4.0, 1e-10);
        let b = SnaqNumber::new(4.0, 1e-10);
        assert_eq!(comparison_probability(ComparisonKind::Ge, a, b), 1.0);
        assert_eq!(comparison_probability(ComparisonKind::Le, a, b), 1.0);
    }
}
