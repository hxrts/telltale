import Runtime.Shim.ResourceAlgebra
import Runtime.Shim.WeakestPre

/-!
# GenHeap: Generalized Heap

Definitions backed by iris-lean for generalized heap (points-to, alloc, valid, update).
The Language class uses function-based `prim_step`; bridging to iris-lean's
relation-based language requires a conversion layer (future work).
-/

set_option autoImplicit false

/-! ## Generalized Heap -/

/-- Heap lookup on language state. -/
noncomputable def HeapLookup {Λ : Type} [Iris.Language Λ] :
    Iris.Language.state Λ → Nat → Option (Iris.Language.val Λ) := sorry

/-- Heap insert on language state. -/
noncomputable def HeapInsert {Λ : Type} [Iris.Language Λ] :
    Iris.Language.state Λ → Nat → Iris.Language.val Λ → Iris.Language.state Λ := sorry

/-- Points-to assertion for heap locations. -/
noncomputable def pointsto {Λ : Type} [Iris.Language Λ] (l : Nat) (v : Iris.Language.val Λ) :
    iProp := sorry

/-- Allocate a fresh heap cell. -/
theorem gen_heap_alloc {Λ : Type} [Iris.Language Λ] (σ : Iris.Language.state Λ)
    (l : Nat) (v : Iris.Language.val Λ) (hFresh : HeapLookup σ l = none) :
    iProp.entails (Iris.state_interp Λ σ)
      (bupd (iProp.sep (Iris.state_interp Λ (HeapInsert σ l v)) (pointsto l v))) := sorry

/-- Validate heap cell value. -/
theorem gen_heap_valid {Λ : Type} [Iris.Language Λ] (σ : Iris.Language.state Λ)
    (l : Nat) (v : Iris.Language.val Λ) :
    iProp.entails (iProp.sep (Iris.state_interp Λ σ) (pointsto l v))
      (iProp.pure (HeapLookup σ l = some v)) := sorry

/-- Update a heap cell. -/
theorem gen_heap_update {Λ : Type} [Iris.Language Λ] (σ : Iris.Language.state Λ)
    (l : Nat) (v v' : Iris.Language.val Λ) :
    iProp.entails (iProp.sep (Iris.state_interp Λ σ) (pointsto l v))
      (bupd (iProp.sep (Iris.state_interp Λ (HeapInsert σ l v')) (pointsto l v'))) := sorry
