import Mathlib
import ClassicalAnalysisAPI

/-! # Concentration Inequalities

This module provides the mathematical foundation for tail probability bounds
on deviations from expected behavior in session-typed distributed systems.
Concentration inequalities quantify how tightly random quantities cluster
around their means.

## Physical Intuition

Consider measuring the average height of 1000 randomly selected people. The
law of large numbers says the sample average will be close to the population
mean. But how close? Concentration inequalities answer: the probability of
the sample average deviating by more than ε from the true mean decays
exponentially in the sample size and ε².

The archetypal result is Hoeffding's inequality: for n independent bounded
random variables with mean μ,

  P(|X̄ - μ| > t) ≤ 2 exp(-2nt² / (b-a)²)

where [a, b] is the range of each variable. This "sub-Gaussian" tail decay
is the gold standard for concentration.

## Canonical Mathematical Formulation

A random variable X is **sub-Gaussian** with parameter σ if its moment
generating function satisfies:

  𝔼[exp(λ(X - 𝔼[X]))] ≤ exp(λ²σ²/2)   for all λ ∈ ℝ

Equivalently, its tails satisfy:

  P(|X - 𝔼[X]| > t) ≤ 2 exp(-t²/(2σ²))

The parameter σ is the "sub-Gaussian proxy variance" and controls tail decay.

For sums of n independent sub-Gaussian variables with parameters σ₁, ..., σₙ:

  P(|Σᵢ Xᵢ - Σᵢ μᵢ| > t) ≤ 2 exp(-t²/(2 Σᵢ σᵢ²))

## Application to Telltale

In session-typed systems, concentration inequalities apply to:

1. **Buffer occupancy**: The deviation of buffer length from its expected
   value concentrates around zero with sub-Gaussian tails, enabling buffer
   sizing with high confidence.

2. **Completion time**: Deviations of protocol completion time from the
   expected time are bounded by concentration, giving tail guarantees.

3. **Throughput variability**: Short-term throughput variations around
   long-term averages satisfy concentration bounds.

The `subGaussianTail σ t = 2 exp(-t²/(2σ²))` function gives the canonical
tail bound, and `ConcentrationWitness` certifies that an observable has
sub-Gaussian concentration.

For Coherence, concentration provides the bridge from expected behavior
(which Foster-Lyapunov guarantees) to high-probability statements (which
SLAs require).

## Key Properties

- **Exponential decay**: Tails decay as exp(-t²), much faster than the
  1/t² of Chebyshev's inequality.

- **Variance parameter**: The σ parameter summarizes the "effective spread"
  of the distribution, even for non-Gaussian distributions.

- **Additivity**: For independent variables, sub-Gaussian parameters add
  in quadrature: σ²_sum = Σᵢ σᵢ².

## Connection to Other Modules

- **Large deviation**: Concentration is the "local" version of large
  deviations, applying to single observations rather than sequences.

- **Heavy traffic**: Near capacity, σ can grow, weakening concentration.

- **Foster-Lyapunov**: Concentration sharpens Lyapunov's "eventually" into
  "with high probability within T steps."

## References

- Hoeffding, W. (1963). Probability inequalities for sums of bounded random
  variables.
- McDiarmid, C. (1989). On the method of bounded differences.
- Boucheron, S., Lugosi, G., and Massart, P. (2013). Concentration Inequalities.
- See also `Runtime/Proofs/SchedulingBound.lean` for protocol concentration.
-/

/-
The Problem. This module needs a concise statement of its theorem-family boundary and reusable assumptions.
Solution Structure. Introduce the core model/contracts first, then derive canonical lemmas and API wrappers from those contracts.
-/

/-! ## Core Development -/

namespace Classical
namespace ConcentrationInequalities

/-- The sub-Gaussian tail bound: 2 exp(-t²/(2σ²)).

    In the Telltale setting:
    - σ is the sub-Gaussian parameter (controls tail decay)
    - t is the deviation threshold

    P(|X - μ| > t) ≤ subGaussianTail σ t gives the canonical tail bound. -/
def subGaussianTail [EntropyAPI.AnalysisModel] (σ t : Real) : Real :=
  EntropyAPI.exponentialTail σ t

/-- Sub-Gaussian tails are non-negative.

    Probabilities are always in [0, 1], but sub-Gaussian bounds can exceed 1
    for small t. This theorem just confirms the bound is at least 0. -/
theorem sub_gaussian_tail_nonneg [EntropyAPI.AnalysisLaws] (σ t : Real) :
    0 ≤ subGaussianTail σ t := by
  simpa [subGaussianTail] using EntropyAPI.exponential_tail_nonneg σ t

/-- A `ConcentrationWitness` certifies that a tail function has sub-Gaussian decay.

    The witness provides:
    - σ: the sub-Gaussian parameter (must be > 0)
    - tail_upper: proof that p(t) ≤ 2 exp(-t²/(2σ²)) for all t ≥ 0

    In the Telltale setting, this witnesses that an observable (like buffer
    deviation or completion time deviation) has sub-Gaussian concentration. -/
structure ConcentrationWitness [EntropyAPI.AnalysisModel] (p : Real → Real) where
  σ : Real
  sigma_pos : 0 < σ
  tail_upper : ∀ t, 0 ≤ t → p t ≤ subGaussianTail σ t

/-- At zero deviation, the bound is trivially 2.

    For protocols: P(|X - μ| > 0) ≤ 2, which is vacuously true since
    probabilities are at most 1. The bound becomes meaningful for t > 0. -/
theorem at_zero_bound [EntropyAPI.AnalysisLaws] {p : Real → Real}
    (h : ConcentrationWitness p) :
    p 0 ≤ 2 := by
  have h0 := h.tail_upper 0 (le_rfl : (0 : Real) ≤ 0)
  calc
    p 0 ≤ subGaussianTail h.σ 0 := h0
    _ = 2 := by
      simpa [subGaussianTail] using EntropyAPI.exponential_tail_zero h.σ

end ConcentrationInequalities
end Classical
