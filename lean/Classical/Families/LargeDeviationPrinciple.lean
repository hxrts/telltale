import Mathlib

/-!
# Large Deviation Principle

This module provides the mathematical foundation for tail probability bounds in
session-typed distributed systems. Large deviation theory characterizes the
exponentially small probabilities of rare events, enabling precise SLA guarantees
and timeout calculations.

## Physical Intuition

Consider flipping a fair coin 1000 times. The law of large numbers says you will
get about 500 heads. But what is the probability of getting 700 or more heads?
Large deviation theory answers: this probability decays *exponentially* in the
number of trials. Specifically:

  P(heads ≥ 700) ≈ exp(-1000 · I(0.7))

where I(x) is a "rate function" measuring how far x deviates from the expected
value. The key insight is that rare events are not just unlikely, they are
*exponentially* unlikely, with a rate that depends on how extreme the deviation is.

## Canonical Mathematical Formulation

A sequence of probability measures (μₙ) on a space X satisfies a **Large Deviation
Principle** (LDP) with rate function I : X → [0, ∞] if for all measurable sets A:

  -inf_{x ∈ A°} I(x) ≤ liminf_{n→∞} (1/n) log μₙ(A)
                     ≤ limsup_{n→∞} (1/n) log μₙ(A) ≤ -inf_{x ∈ Ā} I(x)

In practice, this gives **exponential tail bounds** of the form:

  P(Xₙ ∈ A) ≤ C · ρⁿ

where ρ < 1 is determined by the rate function I.

## Application to Telltale

In session-typed systems, the LDP applies to protocol completion times and
buffer occupancy:

  P(completion_time > t) ≤ C · ρᵗ

where:
  - t is time measured in protocol steps
  - C is a constant depending on initial conditions
  - ρ < 1 is determined by the protocol structure

This gives exponential tail bounds on how long a session takes to complete.
The coherence invariant ensures that the rate ρ is strictly less than 1
(protocols make progress), while the constant C depends on the initial
buffer sizes and type depths.

**Practical implications:**
- **SLA guarantees**: "99.9% of sessions complete within T steps" can be
  computed from C and ρ.
- **Timeout calculation**: Safe timeout values can be derived from the
  tail bound.
- **Resource planning**: Buffer size requirements follow from bounding
  the probability of overflow.

## Key Properties

- **Exponential envelope**: The `exponentialEnvelope C ρ n = C · ρⁿ` captures
  the characteristic shape of large deviation bounds.

- **Monotone decay**: For ρ ≤ 1, the envelope decreases with n, reflecting
  that rare events become exponentially rarer over time.

- **Tightening**: Each step tightens the bound, as `p(n+1) ≤ C · ρⁿ` follows
  from `p(n+1) ≤ C · ρⁿ⁺¹ ≤ C · ρⁿ`.

## References

- Cramér, H. (1938). Sur un nouveau théorème-limite de la théorie des probabilités.
- Varadhan, S.R.S. (1966). Asymptotic probabilities and differential equations.
- Dembo, A. and Zeitouni, O. (1998). Large Deviations Techniques and Applications.
- See also `Runtime/Proofs/SchedulingBound.lean` for protocol tail bounds.
-/

/-
The Problem. This module needs a concise statement of its theorem-family boundary and reusable assumptions.
Solution Structure. Introduce the core model/contracts first, then derive canonical lemmas and API wrappers from those contracts.
-/

/-! ## Core Development -/

namespace Classical
namespace LargeDeviationPrinciple

/-- The exponential envelope `C · ρⁿ` that bounds tail probabilities.

    In the Telltale setting:
    - n is the number of protocol steps (or time)
    - C is an initial constant (depends on starting configuration)
    - ρ < 1 is the decay rate (determined by protocol structure)

    The bound `P(not done by step n) ≤ C · ρⁿ` gives SLA guarantees. -/
def exponentialEnvelope (C ρ : Real) (n : Nat) : Real :=
  C * ρ ^ n

/-- The envelope decreases with each step when ρ ≤ 1.

    For protocols: as time passes, the probability of not yet being done
    decreases exponentially. This is the quantitative version of liveness. -/
theorem envelope_step_mono (C ρ : Real) (n : Nat)
    (hC : 0 ≤ C) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) :
    exponentialEnvelope C ρ (n + 1) ≤ exponentialEnvelope C ρ n := by
  unfold exponentialEnvelope
  have hpow : ρ ^ (n + 1) ≤ ρ ^ n := by
    simpa [pow_succ] using mul_le_of_le_one_right (pow_nonneg hρ₀ n) hρ₁
  exact mul_le_mul_of_nonneg_left hpow hC

/-- An `LDPWitness` certifies that a probability sequence has exponential tails.

    The witness provides:
    - C: the leading constant (initial bound)
    - ρ: the decay rate (must be in [0, 1])
    - tail_upper: proof that p(n) ≤ C · ρⁿ for all n

    In the Telltale setting, this witnesses that protocol completion times
    have exponential tails, enabling SLA calculations. -/
structure LDPWitness (p : Nat → Real) where
  C : Real
  ρ : Real
  C_nonneg : 0 ≤ C
  rho_nonneg : 0 ≤ ρ
  rho_le_one : ρ ≤ 1
  tail_upper : ∀ n, p n ≤ exponentialEnvelope C ρ n

/-- One-step tightening: the bound at step n+1 is at most the bound at step n.

    For protocols: if we know P(not done at step n+1) ≤ C · ρⁿ⁺¹,
    then we also know P(not done at step n+1) ≤ C · ρⁿ (a weaker bound).
    This allows trading precision for simpler calculations. -/
theorem one_step_tightening {p : Nat → Real}
    (h : LDPWitness p) (n : Nat) :
    p (n + 1) ≤ exponentialEnvelope h.C h.ρ n := by
  exact le_trans (h.tail_upper (n + 1))
    (envelope_step_mono h.C h.ρ n h.C_nonneg h.rho_nonneg h.rho_le_one)

end LargeDeviationPrinciple
end Classical
