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

axiom HeapLookup {Λ : Type} [Iris.Language Λ] :
    Iris.Language.state Λ → Nat → Option (Iris.Language.val Λ)
axiom HeapInsert {Λ : Type} [Iris.Language Λ] :
    Iris.Language.state Λ → Nat → Iris.Language.val Λ → Iris.Language.state Λ

axiom pointsto {Λ : Type} [Iris.Language Λ] (l : Nat) (v : Iris.Language.val Λ) : iProp

axiom gen_heap_alloc {Λ : Type} [Iris.Language Λ] (σ : Iris.Language.state Λ)
    (l : Nat) (v : Iris.Language.val Λ) (hFresh : HeapLookup σ l = none) :
    iProp.entails (Iris.state_interp Λ σ)
      (bupd (iProp.sep (Iris.state_interp Λ (HeapInsert σ l v)) (pointsto l v)))

axiom gen_heap_valid {Λ : Type} [Iris.Language Λ] (σ : Iris.Language.state Λ)
    (l : Nat) (v : Iris.Language.val Λ) :
    iProp.entails (iProp.sep (Iris.state_interp Λ σ) (pointsto l v))
      (iProp.pure (HeapLookup σ l = some v))

axiom gen_heap_update {Λ : Type} [Iris.Language Λ] (σ : Iris.Language.state Λ)
    (l : Nat) (v v' : Iris.Language.val Λ) :
    iProp.entails (iProp.sep (Iris.state_interp Λ σ) (pointsto l v))
      (bupd (iProp.sep (Iris.state_interp Λ (HeapInsert σ l v')) (pointsto l v')))
