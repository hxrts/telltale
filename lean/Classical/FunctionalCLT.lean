import Mathlib

/-!
# Functional Central Limit Theorem

This module provides the mathematical foundation for path-level convergence
in session-typed distributed systems. The functional CLT (also known as
Donsker's theorem) extends the classical central limit theorem from
single-point convergence to convergence of entire sample paths.

## Physical Intuition

Consider tracking your cumulative walking distance over a day. At any single
moment, the CLT says your distance is approximately normally distributed
around the mean. But the functional CLT says something stronger: the entire
trajectory of your cumulative distance, viewed as a function of time,
converges to Brownian motion.

The key insight is that the *shape* of sample paths carries information beyond
single-point statistics. A path that steadily increases differs from one that
jumps around, even if they have the same endpoints.

## Canonical Mathematical Formulation

Let X₁, X₂, ... be i.i.d. random variables with mean μ and variance σ². Define
the partial sum process:

  Sₙ(t) = Σᵢ₌₁^{⌊nt⌋} (Xᵢ - μ)

The **scaled process** is:

  Ŝₙ(t) = Sₙ(t) / (σ√n)

**Donsker's Theorem** states:

  Ŝₙ → B   (in distribution, as processes)

where B is standard Brownian motion. The convergence is in the space of
continuous functions C[0,1] equipped with the supremum norm.

## Application to Telltale

In session-typed systems, the functional CLT applies to:

1. **Buffer trajectories**: The path of buffer occupancy over time, not just
   the final value, converges to a scaled Brownian motion. This matters for
   buffer sizing because peaks, not just averages, determine overflow.

2. **Cumulative throughput**: The trajectory of messages processed over time
   follows Brownian motion after centering and scaling, enabling path-dependent
   SLA specifications.

3. **Protocol progress**: The path of "protocol completion percentage" over
   time converges to a Brownian bridge, useful for progress monitoring.

The `centeredIncrement` function computes Xᵢ - μ, `partialSum` computes the
cumulative sum, and `scaledProcess` applies the √n normalization.

For Coherence, the functional CLT provides a basis for reasoning about
*how* protocols reach completion, not just *that* they complete.

## Key Properties

- **Path convergence**: Unlike the pointwise CLT, the functional CLT captures
  temporal correlations and path shapes.

- **Centering**: The `centeredIncrement` removes the drift, isolating random
  fluctuations that drive Brownian behavior.

- **Scaling invariance**: A constant sequence produces a constant partial sum,
  which scales to zero, matching the zero function.

## Connection to Other Modules

- **Heavy traffic**: The functional CLT is the theoretical foundation for
  heavy traffic diffusion limits.

- **Concentration**: Path-level concentration bounds (like Kolmogorov-Smirnov)
  extend single-point concentration to trajectories.

- **Fluid limits**: The functional CLT describes fluctuations around the
  deterministic fluid limit.

## References

- Donsker, M.D. (1951). An invariance principle for certain probability limit
  theorems.
- Billingsley, P. (1968). Convergence of Probability Measures.
- Whitt, W. (2002). Stochastic-Process Limits.
- See also `Runtime/Proofs/WeightedMeasure.lean` for trajectory analysis.
-/

namespace Classical
namespace FunctionalCLT

/-- Centered increment: the deviation of observation x(n) from mean μ.

    In the Telltale setting:
    - x(n) is the n-th observation (e.g., buffer change at step n)
    - μ is the expected change per step

    Centering isolates the random component that drives Brownian behavior. -/
def centeredIncrement (x : Nat → Real) (μ : Real) (n : Nat) : Real :=
  x n - μ

/-- Partial sum of centered increments up to time t.

    In the Telltale setting:
    - This is the cumulative deviation from expected behavior
    - partialSum x μ t = Σᵢ₌₀^{t-1} (x(i) - μ)

    The partial sum is the "random walk" component of the trajectory. -/
def partialSum (x : Nat → Real) (μ : Real) (t : Nat) : Real :=
  (Finset.range t).sum (fun i => centeredIncrement x μ i)

/-- The scaled process: partial sum divided by √N.

    In the Telltale setting:
    - N is the time horizon (total steps to consider)
    - t is the current time
    - The √N scaling gives O(1) fluctuations as N → ∞

    This is the object that converges to Brownian motion. -/
noncomputable def scaledProcess (x : Nat → Real) (μ : Real) (N t : Nat) : Real :=
  partialSum x μ t / Real.sqrt N

/-- Centered increments are additive.

    For independent observations, centering distributes over sums.
    This is the foundation for analyzing composite processes. -/
theorem centeredIncrement_add (x y : Nat → Real) (μx μy : Real) (n : Nat) :
    centeredIncrement (fun k => x k + y k) (μx + μy) n =
      centeredIncrement x μx n + centeredIncrement y μy n := by
  unfold centeredIncrement
  ring

/-- A constant sequence has zero partial sum after centering.

    If every observation equals its mean, there are no fluctuations,
    so the cumulative deviation is zero. -/
theorem partialSum_const_zero (c : Real) (t : Nat) :
    partialSum (fun _ => c) c t = 0 := by
  unfold partialSum centeredIncrement
  simp

/-- A constant sequence produces a zero scaled process.

    This is the base case: no randomness means no Brownian component.
    For protocols, a perfectly predictable execution has zero fluctuations. -/
theorem scaledProcess_const_zero (c : Real) (N t : Nat) (hN : N ≠ 0) :
    scaledProcess (fun _ => c) c N t = 0 := by
  unfold scaledProcess
  simp [partialSum_const_zero]

end FunctionalCLT
end Classical
