import Mathlib
import RumpsteakV2.Coinductive.LocalTypeC
import RumpsteakV2.Coinductive.Regularity

set_option linter.dupNamespace false

/-!
# Finite Systems for Regular LocalTypeC

Defines a finite coalgebra presentation for coinductive local types and a
corecursive reconstruction into `LocalTypeC`.
-/

namespace RumpsteakV2.Coinductive

open Classical

/-- List of reachable states from a regular coinductive type. -/
noncomputable def ReachableList (t : LocalTypeC) (h : Regular t) : List LocalTypeC :=
  (Set.Finite.toFinset h).toList

/-- Index a reachable state in the reachable list (defaulting to 0 if missing). -/
noncomputable def StateIndex (t : LocalTypeC) (h : Regular t) (s : LocalTypeC) :
    Fin (ReachableList t h).length :=
  if h_in : s ∈ ReachableList t h then
    let p : Fin (ReachableList t h).length → Prop := fun i => (ReachableList t h).get i = s
    have : ∃ i, p i := by
      rw [List.mem_iff_get] at h_in
      exact h_in
    Classical.choose this
  else
    ⟨0, by
      have h_t_reachable : t ∈ ReachableList t h := by
        have h_t : t ∈ Reachable t := Relation.ReflTransGen.refl
        simpa [ReachableList] using (Set.Finite.mem_toFinset h).2 h_t
      exact List.length_pos_of_mem h_t_reachable⟩

/-- A finite coalgebra presentation for LocalTypeC. -/
def FiniteSystem (n : Nat) := Fin n → LocalTypeF.Obj (Fin n)

/-- Rebuild a coinductive session from a finite coalgebra and a start state. -/
def SystemToCoind {n : Nat} (sys : FiniteSystem n) (start : Fin n) : LocalTypeC :=
  PFunctor.M.corec sys start

/-- Coalgebra extracted from a regular coinductive type by indexing reachable states. -/
noncomputable def RegularSystem (t : LocalTypeC) (h : Regular t) :
    FiniteSystem (ReachableList t h).length :=
  fun i =>
    match PFunctor.M.dest ((ReachableList t h).get i) with
    | ⟨.end, _⟩ => ⟨.end, fun x => PEmpty.elim x⟩
    | ⟨.var v, _⟩ => ⟨.var v, fun x => PEmpty.elim x⟩
    | ⟨.mu v, f⟩ => ⟨.mu v, fun _ => StateIndex t h (f ())⟩
    | ⟨.send p labels, f⟩ =>
        ⟨.send p labels, fun j => StateIndex t h (f j)⟩
    | ⟨.recv p labels, f⟩ =>
        ⟨.recv p labels, fun j => StateIndex t h (f j)⟩

end RumpsteakV2.Coinductive
