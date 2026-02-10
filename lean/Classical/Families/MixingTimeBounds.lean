import Mathlib

/-!
# Mixing Time Bounds

This module provides the mathematical foundation for convergence rate analysis
in session-typed distributed systems. Mixing time theory characterizes how
quickly a stochastic system approaches its equilibrium distribution.

## Physical Intuition

Consider shuffling a deck of cards. After one shuffle, the deck is slightly
randomized. After two shuffles, more so. The "mixing time" is the number of
shuffles needed until the deck is essentially random, meaning further shuffling
provides negligible additional randomization.

The key insight is that convergence to equilibrium is typically *geometric*:
the distance to equilibrium decreases by a constant factor with each step.
If the initial distance is D and each step reduces it to ρ · D (for some
ρ < 1), then after n steps the distance is at most D · ρⁿ.

## Canonical Mathematical Formulation

For a Markov chain with transition kernel P and stationary distribution π,
the **total variation distance** to equilibrium at time n is:

  d(n) = max_x ||Pⁿ(x, ·) - π||_TV

The **mixing time** τ(ε) is the smallest n such that d(n) ≤ ε.

Under mild conditions (irreducibility, aperiodicity), mixing is geometric:

  d(n) ≤ C · ρⁿ

where C depends on initial conditions and ρ < 1 is the **spectral gap**
parameter, related to the second-largest eigenvalue of P.

## Application to Telltale

In session-typed systems, mixing analysis applies to:

1. **Protocol state convergence**: After how many steps does the distribution
   over protocol configurations become close to its steady state?

2. **Scheduler fairness**: If the scheduler randomizes over choices, how
   quickly does the system explore all branches?

3. **Compositional analysis**: When composing sessions via `link`, how does
   the mixing time of the composed system relate to the components?

The `geometricEnvelope C ρ n` bounds the distance to equilibrium, and the
`MixingWitness` structure certifies that a given system has geometric mixing.
For coherent protocols, the key observation is that Coherence preservation
acts like a contractive map, ensuring the mixing rate ρ < 1.

## Key Properties

- **Geometric envelope**: The envelope `C · ρⁿ` bounds the distance to
  equilibrium, with the same structure as large deviation bounds.

- **Monotone decrease**: For ρ ≤ 1, the bound decreases with each step,
  reflecting steady progress toward equilibrium.

- **Spectral interpretation**: The rate ρ is related to the spectral gap
  1 - λ₂, where λ₂ is the second-largest eigenvalue of the transition matrix.

## Connection to Other Modules

- **Foster-Lyapunov**: Mixing provides the "how fast" to Foster-Lyapunov's
  "eventually" for convergence.

- **Concentration**: Mixing implies concentration for time-averaged observables.

- **Heavy traffic**: Near capacity, mixing times can grow, requiring careful
  analysis of the ρ parameter.

## References

- Levin, D.A., Peres, Y., and Wilmer, E.L. (2009). Markov Chains and Mixing Times.
- Jerrum, M. and Sinclair, A. (1989). Approximating the permanent.
- See also `Runtime/Proofs/SchedulingChain.lean` for protocol mixing analysis.
-/

/-
The Problem. This module needs a concise statement of its theorem-family boundary and reusable assumptions.
Solution Structure. Introduce the core model/contracts first, then derive canonical lemmas and API wrappers from those contracts.
-/

/-! ## Core Development -/

namespace Classical
namespace MixingTimeBounds

/-- The geometric envelope `C · ρⁿ` that bounds distance to equilibrium.

    In the Telltale setting:
    - n is the number of protocol steps
    - C is the initial distance from equilibrium
    - ρ < 1 is the contraction rate per step

    The bound `d(n) ≤ C · ρⁿ` says we approach equilibrium exponentially fast. -/
def geometricEnvelope (C ρ : Real) (n : Nat) : Real :=
  C * ρ ^ n

/-- The envelope decreases with each step when ρ ≤ 1.

    For protocols: as execution progresses, the distance to the stationary
    distribution shrinks geometrically. -/
theorem envelope_step (C ρ : Real) (n : Nat)
    (hC : 0 ≤ C) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    geometricEnvelope C ρ (n + 1) ≤ geometricEnvelope C ρ n := by
  unfold geometricEnvelope
  have hpow : ρ ^ (n + 1) ≤ ρ ^ n := by
    simpa [pow_succ] using mul_le_of_le_one_right (pow_nonneg hρ0 n) hρ1
  exact mul_le_mul_of_nonneg_left hpow hC

/-- A `MixingWitness` certifies that a distance sequence has geometric decay.

    The witness provides:
    - C: the initial distance bound
    - ρ: the contraction rate per step (must be in [0, 1])
    - dist_upper: proof that d(n) ≤ C · ρⁿ for all n

    In the Telltale setting, this witnesses that protocol configurations
    converge to their equilibrium distribution at a geometric rate. -/
structure MixingWitness (d : Nat → Real) where
  C : Real
  ρ : Real
  C_nonneg : 0 ≤ C
  rho_nonneg : 0 ≤ ρ
  rho_le_one : ρ ≤ 1
  dist_upper : ∀ n, d n ≤ geometricEnvelope C ρ n

/-- One-step bound: distance at step n+1 is bounded by the envelope at step n.

    For protocols: knowing d(n+1) ≤ C · ρⁿ⁺¹ and using monotonicity, we get
    d(n+1) ≤ C · ρⁿ. This allows deriving simpler bounds at the cost of tightness. -/
theorem one_step_bound {d : Nat → Real} (h : MixingWitness d) (n : Nat) :
    d (n + 1) ≤ geometricEnvelope h.C h.ρ n := by
  exact le_trans (h.dist_upper (n + 1))
    (envelope_step h.C h.ρ n h.C_nonneg h.rho_nonneg h.rho_le_one)

end MixingTimeBounds
end Classical
