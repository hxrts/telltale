import Mathlib
import Telltale.Coinductive.LocalTypeC
import Telltale.Coinductive.Regularity

set_option linter.dupNamespace false

/-!
The Problem. To convert regular coinductive types back to inductive types or
to reason about them algorithmically, we need a finite representation. A regular
type has finitely many reachable states, so we can index them with Fin n.

Solution Structure.
1. Extract the reachable states as a list (ReachableList)
2. Assign each state an index (StateIndex)
3. Define FiniteSystem as a coalgebra on Fin n
4. Build RegularSystem: the finite coalgebra extracted from a regular type
5. Provide SystemToCoind: reconstruct LocalTypeC from a finite system
-/

namespace Telltale.Coinductive

open Classical

/-! ## State Indexing -/

/-- List of reachable states from a regular coinductive type. -/
noncomputable def ReachableList (t : LocalTypeC) (h : Regular t) : List LocalTypeC :=
  (Set.Finite.toFinset h).toList

/-- Index a reachable state in the list. Defaults to 0 if not found (which
    can't happen for truly reachable states). -/
noncomputable def StateIndex (t : LocalTypeC) (h : Regular t) (s : LocalTypeC) :
    Fin (ReachableList t h).length :=
  if h_in : s ∈ ReachableList t h then
    let p : Fin (ReachableList t h).length → Prop := fun i => (ReachableList t h).get i = s
    have : ∃ i, p i := by rw [List.mem_iff_get] at h_in; exact h_in
    Classical.choose this
  else
    ⟨0, by
      have h_t : t ∈ Reachable t := Relation.ReflTransGen.refl
      have h_t_in : t ∈ ReachableList t h := by
        simpa [ReachableList] using (Set.Finite.mem_toFinset h).2 h_t
      exact List.length_pos_of_mem h_t_in⟩

/-! ## Finite Coalgebra -/

/-- A finite coalgebra presentation: maps each state index to its one-step unfolding. -/
def FiniteSystem (n : Nat) := Fin n → LocalTypeF.Obj (Fin n)

/-- Reconstruct a coinductive type from a finite system and start state. -/
def SystemToCoind {n : Nat} (sys : FiniteSystem n) (start : Fin n) : LocalTypeC :=
  PFunctor.M.corec sys start

/-! ## Extraction from Regular Types -/

/-- Extract a finite coalgebra from a regular coinductive type.
    Each reachable state maps to its destructor with children indexed. -/
noncomputable def RegularSystem (t : LocalTypeC) (h : Regular t) :
    FiniteSystem (ReachableList t h).length :=
  fun i =>
    match PFunctor.M.dest ((ReachableList t h).get i) with
    | ⟨.end, _⟩      => ⟨.end, PEmpty.elim⟩
    | ⟨.var v, _⟩    => ⟨.var v, PEmpty.elim⟩
    | ⟨.mu v, f⟩     => ⟨.mu v, fun _ => StateIndex t h (f ())⟩
    | ⟨.send p ls, f⟩ => ⟨.send p ls, fun j => StateIndex t h (f j)⟩
    | ⟨.recv p ls, f⟩ => ⟨.recv p ls, fun j => StateIndex t h (f j)⟩

end Telltale.Coinductive
