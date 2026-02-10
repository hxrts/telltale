import Mathlib

/-!
# MaxWeight Backpressure Scheduling

This module provides the mathematical foundation for throughput-optimal scheduling
in session-typed distributed systems. The MaxWeight algorithm originates from
queueing theory and network scheduling, where it achieves the maximum possible
throughput in multi-queue systems.

## Physical Intuition

Imagine a switchboard operator handling multiple incoming phone lines. Each line has a
queue of waiting callers, and the operator can only handle one call at a time. The
MaxWeight strategy says: always pick up the line with the longest queue. Surprisingly,
this simple greedy rule is *optimal* in a precise sense: it stabilizes the system
whenever stability is achievable at all.

The "weight" in MaxWeight refers to the queue length (or more generally, a priority
metric). The "backpressure" refers to how congestion at one node propagates backward
through the network, naturally regulating the flow of work.

## Canonical Mathematical Formulation

Consider a system with queues indexed by i ∈ I and queue lengths q(i). At each time
step, we choose a service rate vector μ from a feasible set Γ. The MaxWeight
policy selects:

  μ* = argmax_{μ ∈ Γ} Σᵢ q(i) · μ(i)

This maximizes the weighted sum of service, where weights are queue lengths.

The **MaxWeight Theorem** states: under mild conditions on arrivals, the MaxWeight
policy stabilizes the system (keeps queues finite) for any arrival rate within the
*capacity region* Λ. Moreover, no other policy can stabilize rates outside Λ, making
MaxWeight *throughput optimal*.

## Application to Telltale

In session-typed systems, MaxWeight scheduling applies to message processing across
multiple sessions:

  q(session) = buffer backlog for that session
  μ(session) = rate at which we process messages for that session
  Γ = scheduling constraints (e.g., only one session active per role at a time)

The MaxWeight policy says: prioritize sessions with the largest message backlogs.
This ensures that:

1. **No session starves**: Sessions with growing backlogs get priority.
2. **System remains coherent**: By processing backlogs, we maintain the Coherence
   invariant that buffers match expected types.
3. **Throughput is maximized**: We handle as many messages as the system can support.

The `weight` function computes Σᵢ q(i) · μ(i), and `MaxWeightChoice` certifies that
a scheduling decision achieves the maximum possible weight.

## Key Properties

- **Greedy optimality**: MaxWeight is a greedy algorithm but achieves global
  optimality for throughput.

- **Decomposition**: The weight is a sum over independent terms, so scheduling
  decisions can be made locally while achieving global optimality.

- **Lyapunov connection**: MaxWeight maximizes the "drift" of a quadratic Lyapunov
  function, connecting to Foster-Lyapunov stability.

## References

- Tassiulas, L. and Ephremides, A. (1992). Stability properties of constrained
  queueing systems and scheduling policies for maximum throughput.
- Neely, M.J. (2010). Stochastic Network Optimization with Application to
  Communication and Queueing Systems.
- See also `Runtime/Proofs/SchedulingBound.lean` for the session-types instantiation.
-/

/-
The Problem. This module needs a concise statement of its theorem-family boundary and reusable assumptions.
Solution Structure. Introduce the core model/contracts first, then derive canonical lemmas and API wrappers from those contracts.
-/

/-! ## Core Development -/

namespace Classical
namespace MaxWeightBackpressure

open scoped BigOperators

variable {ι : Type} [Fintype ι]

/-- The MaxWeight objective function: sum of queue lengths times service rates.

    In the Telltale setting:
    - q(i) is the buffer backlog for session i
    - μ(i) is the service rate (messages processed) for session i

    Maximizing this quantity balances clearing large backlogs while respecting
    capacity constraints. -/
def weight (q μ : ι → Real) : Real :=
  ∑ i, q i * μ i

/-- Non-negative inputs yield non-negative weight.

    Buffers and service rates are naturally non-negative, so the objective is too. -/
theorem weight_nonneg (q μ : ι → Real)
    (hq : ∀ i, 0 ≤ q i) (hμ : ∀ i, 0 ≤ μ i) :
    0 ≤ weight q μ := by
  unfold weight
  exact Finset.sum_nonneg (by
    intro i hi
    exact mul_nonneg (hq i) (hμ i))

/-- A `MaxWeightChoice` certifies that a scheduling decision is optimal.

    The `sched` field gives the chosen service rates, and `optimal` proves that
    no alternative choice achieves higher weight. In the Telltale setting, this
    corresponds to a scheduling proof that says "processing these sessions first
    is provably optimal for clearing backlogs." -/
structure MaxWeightChoice (q : ι → Real) where
  sched : ι → Real
  optimal : ∀ ν : ι → Real, weight q ν ≤ weight q sched

variable (q : ι → Real)

/-- MaxWeight dominates all alternatives.

    This is the key theorem: any scheduling choice ν achieves at most the weight
    of the MaxWeight choice. For protocols, this means the MaxWeight scheduler
    clears backlogs at least as fast as any alternative. -/
theorem maxweight_dominates
    (h : MaxWeightChoice q) (ν : ι → Real) :
    weight q ν ≤ weight q h.sched :=
  h.optimal ν

end MaxWeightBackpressure
end Classical
