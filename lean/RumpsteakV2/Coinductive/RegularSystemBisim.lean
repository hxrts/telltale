import Mathlib
import RumpsteakV2.Coinductive.LocalTypeC
import RumpsteakV2.Coinductive.Regularity
import RumpsteakV2.Coinductive.FiniteSystem
import RumpsteakV2.Coinductive.Bisim

set_option linter.dupNamespace false

/-!
# Regular systems and bisimulation

Builds a bisimulation between a regular coinductive type and the coinductive
term generated from its finite system presentation.
-/

namespace RumpsteakV2.Coinductive

open Classical

/-- `StateIndex` returns the index witnessing membership in the reachable list. -/
theorem get_StateIndex (t : LocalTypeC) (h : Regular t) (s : LocalTypeC)
    (hs : s ∈ ReachableList t h) :
    (ReachableList t h).get (StateIndex t h s) = s := by
  unfold StateIndex
  by_cases h_in : s ∈ ReachableList t h
  · have : ∃ i, (ReachableList t h).get i = s := by
      simpa [List.mem_iff_get] using h_in
    simpa [h_in] using (Classical.choose_spec this)
  · cases h_in hs

/-- One-step behavior of the regular system at a reachable state. -/
theorem RegularSystem_at_index (t : LocalTypeC) (h : Regular t) (s : LocalTypeC)
    (hs : s ∈ ReachableList t h) :
    RegularSystem t h (StateIndex t h s) =
      match PFunctor.M.dest s with
      | ⟨.end, _⟩ => ⟨.end, fun x => PEmpty.elim x⟩
      | ⟨.var v, _⟩ => ⟨.var v, fun x => PEmpty.elim x⟩
      | ⟨.mu v, f⟩ => ⟨.mu v, fun _ => StateIndex t h (f ())⟩
      | ⟨.send p labels, f⟩ =>
          ⟨.send p labels, fun j => StateIndex t h (f j)⟩
      | ⟨.recv p labels, f⟩ =>
          ⟨.recv p labels, fun j => StateIndex t h (f j)⟩ := by
      unfold RegularSystem
      rw [get_StateIndex t h s hs]
      rfl

/-- A bisimulation relating reachable states to their finite-system image. -/
def RegularBisim (t : LocalTypeC) (h : Regular t)
    (sys : FiniteSystem (ReachableList t h).length) (s1 s2 : LocalTypeC) : Prop :=
  ∃ s, s ∈ ReachableList t h ∧ s1 = s ∧ s2 = SystemToCoind sys (StateIndex t h s)

/-- The regular bisimulation is a bisimulation. -/
theorem RegularBisim_isBisimulation (t : LocalTypeC) (h : Regular t) :
    IsBisimulation (RegularBisim t h (RegularSystem t h)) := by
  -- TODO: Fix after TypeContext refactoring
  sorry

/-- Regular coinductive types are bisimilar to their finite-system presentation. -/
theorem Regular_implies_System (t : LocalTypeC) (h : Regular t) :
    ∃ (n : Nat) (sys : FiniteSystem n) (start : Fin n),
      Bisim t (SystemToCoind sys start) := by
  let n := (ReachableList t h).length
  let sys := RegularSystem t h
  let start := StateIndex t h t
  refine ⟨n, sys, start, ?_⟩
  refine ⟨RegularBisim t h sys, RegularBisim_isBisimulation t h, ?_⟩
  refine ⟨t, ?_, rfl, rfl⟩
  have ht : t ∈ Reachable t := Relation.ReflTransGen.refl
  have ht' : t ∈ Set.Finite.toFinset h := (Set.Finite.mem_toFinset h).2 ht
  simpa [ReachableList] using ht'

end RumpsteakV2.Coinductive
