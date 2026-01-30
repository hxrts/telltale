import Runtime.Shim.ResourceAlgebra
import Runtime.Shim.WeakestPre

/-!
# GenHeap: Generalized Heap

Axiom shims for generalized heap (points-to, alloc, valid, update).
Retires when: iris_2.md Task 9G lands.
Unblocks: Task 19.
-/

set_option autoImplicit false

/-! ## Generalized Heap -/

axiom HeapLookup {Λ : Type} [Language Λ] : Language.state Λ → Nat → Option (Language.val Λ)
axiom HeapInsert {Λ : Type} [Language Λ] : Language.state Λ → Nat → Language.val Λ → Language.state Λ

axiom pointsto {Λ : Type} [Language Λ] (l : Nat) (v : Language.val Λ) : iProp

axiom gen_heap_alloc {Λ : Type} [Language Λ] (σ : Language.state Λ)
    (l : Nat) (v : Language.val Λ) (hFresh : HeapLookup σ l = none) :
    iProp.entails (state_interp Λ σ)
      (bupd (iProp.sep (state_interp Λ (HeapInsert σ l v)) (pointsto l v)))

axiom gen_heap_valid {Λ : Type} [Language Λ] (σ : Language.state Λ)
    (l : Nat) (v : Language.val Λ) :
    iProp.entails (iProp.sep (state_interp Λ σ) (pointsto l v))
      (iProp.pure (HeapLookup σ l = some v))

axiom gen_heap_update {Λ : Type} [Language Λ] (σ : Language.state Λ)
    (l : Nat) (v v' : Language.val Λ) :
    iProp.entails (iProp.sep (state_interp Λ σ) (pointsto l v))
      (bupd (iProp.sep (state_interp Λ (HeapInsert σ l v')) (pointsto l v')))
