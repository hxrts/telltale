import Runtime.Resources.HeapModel

/-! # Runtime.Proofs.Heap

Replay-compositionality and order-independence lemmas for the executable Lean heap model used by the
Rust↔Lean parity lane.
-/

set_option autoImplicit false

namespace Runtime.Proofs.Heap

open Runtime.Resources.HeapModel

theorem canonical_bytes_congr {left right : Resource} (h : left = right) :
    resourceCanonicalBytes left = resourceCanonicalBytes right := by
  cases h
  rfl

theorem preimages_congr
    {resourceBytes₁ resourceBytes₂ : List UInt8}
    {counter₁ counter₂ : Nat}
    (hBytes : resourceBytes₁ = resourceBytes₂)
    (hCounter : counter₁ = counter₂) :
    resourceIdPreimage resourceBytes₁ counter₁ = resourceIdPreimage resourceBytes₂ counter₂ := by
  cases hBytes
  cases hCounter
  rfl

/-- Replaying a log in two chunks reconstructs the same heap as one replay. -/
theorem replay_split (ops₁ ops₂ : List HeapOp) (state : HeapState := {}) :
    applyOps (ops₁ ++ ops₂) state = applyOps ops₂ (applyOps ops₁ state) :=
  applyOps_append ops₁ ops₂ state

/-- Consume order does not affect the active heap. -/
theorem replay_consume_order_independent (state : HeapState) (a b : ResourceId) :
    activeEntries (applyOps [.consume a, .consume b] state) =
      activeEntries (applyOps [.consume b, .consume a] state) :=
  consume_comm_activeEntries state a b

end Runtime.Proofs.Heap
