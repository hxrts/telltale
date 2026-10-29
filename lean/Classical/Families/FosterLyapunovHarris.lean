import Mathlib

/-! # Foster-Lyapunov-Harris Stability Theory

**Scope (Option B, honest conditional interface).** Only deterministic facts about a `DriftSystem` (a step map with a
nat-valued potential that never increases and strictly decreases when
positive) are proved, including that the potential reaches zero within
`V s` steps. There is no probability, Markov kernel, petite set or Harris
recurrence here; the stochastic Foster-Lyapunov theorem is not proved.

This module provides the mathematical foundation for proving liveness in session-typed
distributed systems. The Foster-Lyapunov method originates from the theory of Markov
chains, where it establishes conditions under which a stochastic system returns to a
"good" set of states with probability one.

## Physical Intuition

Consider a ball rolling in a bowl. No matter where you place the ball, gravity pulls it
toward the bottom. The height of the ball acts as a "potential function" or "Lyapunov
function": it decreases with each moment until the ball reaches the minimum. The
Foster-Lyapunov method generalizes this intuition: if we can find a function V that
decreases on average with each step of a system, then the system must eventually reach
states where V is minimal.

## Canonical Mathematical Formulation

For a Markov chain with transition kernel P on state space S, a function V : S → [0, ∞)
is a **Lyapunov function** if there exist constants b, δ > 0 and a set C ⊆ S such that:

  𝔼[V(X_{n+1}) | X_n = s] ≤ V(s) - δ     for s ∉ C     (drift condition)
  𝔼[V(X_{n+1}) | X_n = s] ≤ b            for s ∈ C     (boundedness on C)

The **Foster-Lyapunov theorem** states: if such a V exists with C finite (or
"petite"), then the chain is positive Harris recurrent, meaning it returns to C
infinitely often and admits a unique stationary distribution.

## Application to Telltale

In session-typed systems, the Lyapunov function V is instantiated as a
**progress measure** on protocol configurations:

  V(config) = Σ (type_depth(edge) + buffer_length(edge) + send_potential(edge))

where the sum ranges over active edges in the session. The key insight is that
Coherence (the invariant that message buffers are compatible with expected types)
ensures that every protocol step either:

  1. Consumes a message (decreasing buffer_length)
  2. Advances the type (decreasing type_depth)
  3. Resolves a choice (decreasing send_potential)

This gives us the drift condition. The set C corresponds to completed sessions
(where V = 0). For a *deterministic* `DriftSystem`, `DriftSystem.reaches_zero_within_rank`
proves the potential reaches zero within `V s₀` steps. Whether a concrete protocol
step actually satisfies the drift fields is a separate obligation (see
`Protocol.Classical.Instantiation.FosterDrain` for one genuine instance).

## Key Properties

- **Deterministic simplification**: The kernel here uses a deterministic step function
  rather than a probability measure, simplifying the analysis while preserving the
  core descent argument.

- **Strict decrease on positive states**: When V(s) > 0, every step strictly decreases
  V, giving a concrete termination bound of V(s₀) steps.

- **Compositionality**: Session isolation means V decomposes as a sum over independent
  sessions, so progress in one session does not affect others.

## References

- Foster, F.G. (1953). On the stochastic matrices associated with certain queuing processes.
- Meyn, S.P. and Tweedie, R.L. (1993). Markov Chains and Stochastic Stability.
- See also `Runtime/Proofs/Lyapunov.lean` for the session-types instantiation.
-/

/-
The Problem. This module needs a concise statement of its theorem-family boundary and reusable assumptions.
Solution Structure. Introduce the core model/contracts first, then derive canonical lemmas and API wrappers from those contracts.
-/

/-! ## Core Development -/

namespace Classical
namespace FosterLyapunovHarris

universe u

/-- A `DriftSystem` captures the core structure of a Foster-Lyapunov argument:
    a state space with a step function and a potential V that decreases toward zero.

    In the Telltale setting:
    - `α` is the type of protocol configurations (GEnv × DEnv pairs)
    - `step` is a single protocol transition (send, receive, or choice)
    - `V` is the progress measure (type depth + buffer length + send potential)
    - `nonincrease` is guaranteed by Coherence preservation
    - `strict_on_pos` is guaranteed by progress: coherent non-terminal states can step -/
structure DriftSystem (α : Type u) where
  step : α → α
  V : α → Nat
  nonincrease : ∀ s, V (step s) ≤ V s
  strict_on_pos : ∀ s, V s ≠ 0 → V (step s) < V s

namespace DriftSystem

variable {α : Type u} (S : DriftSystem α)

/-- The potential is non-increasing under iteration.

    For protocols: if V(config₀) = k, then after n steps V(configₙ) ≤ k.
    This bounds the "energy" in the system throughout execution. -/
theorem iterate_nonincrease (s : α) :
    ∀ n, S.V (S.step^[n] s) ≤ S.V s := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        S.V (S.step^[n.succ] s) = S.V (S.step (S.step^[n] s)) := by
          simp [Function.iterate_succ_apply']
        _ ≤ S.V (S.step^[n] s) := S.nonincrease _
        _ ≤ S.V s := ih

/-- Bounded-rank form of `reaches_zero_within_rank`, by induction on the bound. -/
theorem reaches_zero_of_rank_le :
    ∀ k s, S.V s ≤ k → ∃ n ≤ S.V s, S.V (S.step^[n] s) = 0 := by
  intro k
  induction k with
  | zero =>
      intro s hs
      exact ⟨0, Nat.zero_le _, by simpa using Nat.le_zero.mp hs⟩
  | succ k ih =>
      intro s hs
      by_cases h0 : S.V s = 0
      · exact ⟨0, Nat.zero_le _, by simpa using h0⟩
      · have hlt := S.strict_on_pos s h0
        obtain ⟨n, hn, hz⟩ := ih (S.step s) (by omega)
        exact ⟨n + 1, by omega, by simpa [Function.iterate_succ_apply] using hz⟩

/-- Deterministic termination: from any state the potential reaches zero within
    `V s` steps (strict decrease on positive potential, `V : α → ℕ`).

    This is a deterministic well-founded-descent fact, not the stochastic
    Foster-Lyapunov theorem (which needs a Markov kernel, an expected-drift
    condition and a petite set, and concludes positive Harris recurrence). -/
theorem reaches_zero_within_rank (s : α) :
    ∃ n ≤ S.V s, S.V (S.step^[n] s) = 0 :=
  reaches_zero_of_rank_le S (S.V s) s le_rfl

end DriftSystem

end FosterLyapunovHarris
end Classical
