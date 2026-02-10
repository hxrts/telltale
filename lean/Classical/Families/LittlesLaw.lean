import Mathlib

/-! # Little's Law

This module provides the mathematical foundation for relating queue length,
arrival rate, and waiting time in session-typed distributed systems. Little's
Law is one of the most fundamental results in queueing theory, remarkable for
its generality and simplicity.

## Physical Intuition

Consider a coffee shop. On average, there are L customers in the shop, new
customers arrive at rate λ per hour, and each customer spends W hours inside.
Little's Law states a simple relationship:

  L = λ · W

This holds regardless of the arrival pattern (bursty or steady), the service
discipline (first-come-first-served or random), or the number of servers. The
relationship is purely structural, arising from conservation of customer-hours.

The intuition is counting: each customer contributes W hours of "presence" to
the shop. With λ arrivals per hour, the total presence accumulates at rate
λ · W per hour. In steady state, this equals the average occupancy L.

## Canonical Mathematical Formulation

Consider a system in steady state with:
  - L = average number of items in the system
  - λ = arrival rate (items per unit time)
  - W = average time an item spends in the system

**Little's Law** states:

  L = λ · W

Equivalently:
  - W = L / λ  (average wait time from queue length and arrival rate)
  - λ = L / W  (infer throughput from queue length and wait time)

The law holds under very general conditions: any arrival process, any service
discipline, any number of servers, any service time distribution.

## Application to Telltale

In session-typed systems, Little's Law relates:

  L = average number of messages in buffers (across all edges)
  λ = message arrival rate (sends per unit time)
  W = average message latency (time from send to receive)

This gives three practical applications:

1. **Latency from backlog**: If you observe L messages in buffers and know
   the sending rate λ, you can infer average latency W = L / λ without
   timing each message.

2. **Throughput monitoring**: If you measure buffer occupancy L and message
   latency W, you can infer effective throughput λ = L / W.

3. **Capacity planning**: To achieve target latency W with arrival rate λ,
   you need buffer capacity at least L = λ · W.

For Coherence, Little's Law connects static properties (buffer capacity) to
dynamic properties (latency), enabling principled resource allocation.

## Key Properties

- **Model-independence**: The law holds for any arrival and service pattern,
  requiring only that the system is in steady state.

- **Algebraic flexibility**: Any one of L, λ, W can be computed from the
  other two.

- **Composability**: For subsystems, the law applies locally, enabling
  modular analysis.

## Connection to Other Modules

- **Foster-Lyapunov**: Stability (λ < μ) ensures L is finite, making
  Little's Law applicable.

- **Heavy traffic**: As λ → μ (capacity), L → ∞ and W → ∞, reflecting
  congestion buildup.

- **Concentration**: Little's Law gives expectations; concentration bounds
  give deviations.

## References

- Little, J.D.C. (1961). A proof for the queuing formula: L = λW.
- Little, J.D.C. and Graves, S.C. (2008). Little's Law. In Building Intuition.
- See also `Runtime/Proofs/SchedulingBound.lean` for latency analysis.
-/

/-
The Problem. This module needs a concise statement of its theorem-family boundary and reusable assumptions.
Solution Structure. Introduce the core model/contracts first, then derive canonical lemmas and API wrappers from those contracts.
-/

/-! ## Core Development -/

namespace Classical
namespace LittlesLaw

/-- A `LittleInput` packages the three quantities related by Little's Law.

    In the Telltale setting:
    - lam (λ) is the message sending rate
    - W is the average message latency (time in buffer)
    - L is the average buffer occupancy
    - law is the proof that L = λ · W holds

    The structure witnesses that the system is in a stable regime where
    Little's Law applies. -/
structure LittleInput where
  lam : Real
  W : Real
  L : Real
  law : L = lam * W

/-- Queue length equals arrival rate times waiting time.

    This is Little's Law in its direct form. For protocols: the average
    number of messages in buffers equals the sending rate times the
    average time each message waits to be received. -/
theorem queue_length (h : LittleInput) : h.L = h.lam * h.W :=
  h.law

/-- Waiting time equals queue length divided by arrival rate.

    For protocols: if you know the average buffer occupancy L and the
    sending rate λ, you can compute average latency as W = L / λ. This
    avoids having to time individual messages. -/
theorem wait_time (h : LittleInput) (hlam : h.lam ≠ 0) :
    h.W = h.L / h.lam := by
  have : h.lam * h.W = h.L := by simp [h.law]
  apply (eq_div_iff hlam).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

/-- Throughput equals queue length divided by waiting time.

    For protocols: if you measure buffer occupancy L and message latency W,
    you can infer the effective message rate λ = L / W. This is useful for
    monitoring throughput without counting individual messages. -/
theorem throughput (h : LittleInput) (hW : h.W ≠ 0) :
    h.lam = h.L / h.W := by
  have : h.lam * h.W = h.L := by simp [h.law]
  apply (eq_div_iff hW).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

end LittlesLaw
end Classical
