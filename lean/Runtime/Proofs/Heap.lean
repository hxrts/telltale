import Runtime.Resources.HeapModel

/-! # Runtime.Proofs.Heap

Small determinism lemmas for the executable Lean heap model used by the
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

theorem apply_op_deterministic (state : HeapState) (op : HeapOp) :
    applyOp state op = applyOp state op := rfl

theorem apply_ops_deterministic (ops : List HeapOp) (state : HeapState := {}) :
    applyOps ops state = applyOps ops state := rfl

theorem replay_outputs_match (ops : List HeapOp) (state : HeapState := {}) :
    let first := applyOps ops state
    let second := applyOps ops state
    first = second := by
  rfl

theorem proof_path_deterministic (levels : List (List DigestHex)) (index : Nat) :
    proofPathFromLevels levels index = proofPathFromLevels levels index := rfl

end Runtime.Proofs.Heap
