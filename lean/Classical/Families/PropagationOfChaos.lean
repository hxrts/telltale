import Mathlib
import ClassicalAnalysisAPI

/-!
# Propagation of Chaos and Mean-Field Limits

This module provides the mathematical foundation for analyzing large-scale
session-typed systems where many participants interact. The "propagation of
chaos" phenomenon describes how, in systems with many interacting components,
individual components become approximately independent in the large-n limit.

## Physical Intuition

Consider a room full of people, each choosing their walking direction based
partly on avoiding nearby others. When there are only a few people, their
movements are highly correlated. But with hundreds of people, any single
person's trajectory becomes nearly independent of any other specific person's
trajectory. The crowd has an aggregate "flow" that each person responds to,
but individual correlations vanish.

This is "chaos" in the probabilistic sense: not disorder, but independence.
The "propagation" refers to how this independence, once established at time 0,
persists through the dynamics.

## Canonical Mathematical Formulation

Consider n particles with positions X₁, ..., Xₙ. Define the **empirical
measure**:

  μₙ = (1/n) Σᵢ δ_{Xᵢ}

where δ_x is a point mass at x.

In a **mean-field** system, each particle evolves according to:

  dXᵢ = b(Xᵢ, μₙ) dt + σ dWᵢ

where b depends on the empirical measure (aggregate behavior) rather than
individual particles.

**Propagation of chaos** states: if the initial particles are i.i.d., then
as n → ∞, any fixed subset of k particles remains approximately i.i.d.
with distribution evolving according to the limiting "McKean-Vlasov" equation.

The empirical mean (1/n) Σᵢ Xᵢ is a key observable that converges to the
population mean, with permutation invariance reflecting exchangeability.

## Application to Telltale

In session-typed systems with many concurrent sessions, mean-field analysis
applies:

1. **Multi-session aggregation**: With n concurrent sessions, the behavior
   of any single session becomes approximately independent of others. The
   "mean field" is the aggregate buffer occupancy or load.

2. **Scalability analysis**: As the number of sessions grows, per-session
   behavior converges to a deterministic limit determined by aggregate load.

3. **Resource pooling**: Resources shared across sessions can be analyzed
   via mean-field approximations, simplifying capacity planning.

The `empiricalMean` function computes the average over sessions, and
`empiricalMean_perm` proves this average is invariant under relabeling.
This exchangeability is the mathematical signature of "chaos": sessions
are statistically interchangeable.

For Coherence, mean-field analysis justifies treating multi-session systems
via aggregate properties rather than tracking individual session correlations.

## Key Properties

- **Permutation invariance**: The empirical mean (and any symmetric statistic)
  is unchanged by relabeling particles. This reflects exchangeability.

- **Concentration**: For i.i.d. particles, the empirical mean concentrates
  around the true mean with O(1/√n) deviations.

- **Decoupling**: In the limit, k-particle marginals factorize, enabling
  independent analysis of each particle.

## Connection to Other Modules

- **Concentration**: The empirical mean satisfies concentration inequalities
  with σ ∝ 1/√n.

- **Fluid limits**: Mean-field limits are closely related to fluid limits,
  with the empirical measure playing the role of the fluid state.

- **Heavy traffic**: Under heavy load, correlations can persist longer,
  slowing the approach to mean-field behavior.

## References

- Kac, M. (1956). Foundations of kinetic theory.
- Sznitman, A.S. (1991). Topics in propagation of chaos.
- Meleard, S. (1996). Asymptotic behaviour of some interacting particle systems.
- See also `Runtime/Proofs/SchedulingBound.lean` for multi-session analysis.
-/

/-
The Problem. This module needs a concise statement of its theorem-family boundary and reusable assumptions.
Solution Structure. Introduce the core model/contracts first, then derive canonical lemmas and API wrappers from those contracts.
-/

/-! ## Core Development -/

namespace Classical
namespace PropagationOfChaos

open scoped BigOperators

variable {n : Nat}

/-- Total of observations across all participants.

    In the Telltale setting:
    - x(i) is the buffer occupancy (or some metric) for session i
    - empiricalTotal x = Σᵢ x(i) is the aggregate across all sessions

    This is the numerator of the empirical mean. -/
def empiricalTotal (x : Fin n → Real) : Real :=
  ∑ i, x i

/-- Empirical mean: average of observations across participants.

    In the Telltale setting:
    - empiricalMean x = (1/n) Σᵢ x(i) is the average metric across sessions

    The empirical mean is the key observable for mean-field analysis. -/
def empiricalMean [EntropyAPI.AnalysisModel] (x : Fin n → Real) : Real :=
  EntropyAPI.finiteAverage x

/-- The total is invariant under permutation of indices.

    Relabeling sessions does not change the aggregate. This is the
    foundation of exchangeability: sessions are statistically equivalent. -/
theorem empiricalTotal_perm (σ : Equiv.Perm (Fin n)) (x : Fin n → Real) :
    empiricalTotal (fun i => x (σ i)) = empiricalTotal x := by
  simpa [empiricalTotal] using
    (Fintype.sum_equiv σ (fun i => x (σ i)) x (by intro i; rfl))

/-- The empirical mean is invariant under permutation of indices.

    Relabeling sessions does not change the average. This permutation
    invariance is the mathematical signature of propagation of chaos:
    any subset of k sessions is statistically equivalent to any other
    subset of k sessions.

    For Coherence: this justifies analyzing "typical" session behavior
    without tracking which specific sessions we are examining. -/
theorem empiricalMean_perm (σ : Equiv.Perm (Fin n)) (x : Fin n → Real) :
    [EntropyAPI.AnalysisLaws] →
    empiricalMean (fun i => x (σ i)) = empiricalMean x := by
  intro _
  simpa [empiricalMean] using EntropyAPI.finiteAverage_perm σ x

/-- The empirical mean of a constant is that constant.

    If all sessions have the same metric value c, the average is c.
    This is the base case for mean-field analysis: homogeneous systems
    have trivial empirical measures.

    For protocols: if all sessions are in identical states, the
    aggregate behavior equals the individual behavior. -/
theorem empiricalMean_const (c : Real) :
    [EntropyAPI.AnalysisLaws] →
    ∀ hn : n ≠ 0, empiricalMean (fun _ : Fin n => c) = c := by
  intro _ hn
  simpa [empiricalMean] using EntropyAPI.finiteAverage_const c hn

end PropagationOfChaos
end Classical
