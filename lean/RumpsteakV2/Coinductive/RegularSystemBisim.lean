import Mathlib
import RumpsteakV2.Coinductive.LocalTypeC
import RumpsteakV2.Coinductive.Regularity
import RumpsteakV2.Coinductive.FiniteSystem
import RumpsteakV2.Coinductive.Bisim

set_option linter.dupNamespace false

/-!
The Problem. We defined RegularSystem to extract a finite coalgebra from a
regular coinductive type. We need to prove that reconstructing from this
system via SystemToCoind yields a bisimilar (hence equal) type.

The difficulty is constructing the bisimulation witness. We define RegularBisim
which relates a reachable state `s` to its finite-system reconstruction, then
prove this relation satisfies the IsBisimulation property.

Solution Structure.
1. get_StateIndex: StateIndex correctly retrieves the indexed state
2. RegularSystem_at_index: the system at index i matches dest of state i
3. RegularBisim: the relation connecting states to their reconstructions
4. RegularBisim_isBisimulation: proof that this is a valid bisimulation
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
  intro s1 s2 hrel
  rcases hrel with ⟨s, hs, rfl, rfl⟩
  rcases hdest : PFunctor.M.dest s1 with ⟨hd, f⟩
  -- helper: show a child is in the reachable list
  have hclosed := reachable_is_closed_set t h
  have hs_fin : s1 ∈ Set.Finite.toFinset h := by
    simpa [ReachableList, Finset.mem_toList] using hs
  have hchild_mem :
      ∀ i : LocalTypeChild hd, f i ∈ ReachableList t h := by
    intro i
    have hchild : childRel s1 (f i) := by
      exact ⟨hd, f, i, hdest, rfl⟩
    have hfin : f i ∈ Set.Finite.toFinset h := mem_of_closed_child hclosed hs_fin hchild
    simpa [ReachableList, Finset.mem_toList] using hfin
  cases hd with
  | «end» =>
      let g : LocalTypeChild LocalTypeHead.end → LocalTypeC :=
        PFunctor.M.corec (RegularSystem t h) ∘ fun x => PEmpty.elim x
      refine ⟨LocalTypeHead.end, f, g, ?_, ?_, ?_⟩
      · rfl
      · have hsys := RegularSystem_at_index t h s1 hs
        simp [hdest] at hsys
        simp [SystemToCoind, PFunctor.M.dest_corec, hsys, g]
        rfl
      · intro i
        cases i
  | var v =>
      let g : LocalTypeChild (LocalTypeHead.var v) → LocalTypeC :=
        PFunctor.M.corec (RegularSystem t h) ∘ fun x => PEmpty.elim x
      refine ⟨LocalTypeHead.var v, f, g, ?_, ?_, ?_⟩
      · rfl
      · have hsys := RegularSystem_at_index t h s1 hs
        simp [hdest] at hsys
        simp [SystemToCoind, PFunctor.M.dest_corec, hsys, g]
        rfl
      · intro i
        cases i
  | mu v =>
      let g : LocalTypeChild (LocalTypeHead.mu v) → LocalTypeC :=
        PFunctor.M.corec (RegularSystem t h) ∘ fun _ => StateIndex t h (f ())
      refine ⟨LocalTypeHead.mu v, f, g, ?_, ?_, ?_⟩
      · rfl
      · have hsys := RegularSystem_at_index t h s1 hs
        simp [hdest] at hsys
        simp [SystemToCoind, PFunctor.M.dest_corec, hsys, g]
        rfl
      · intro i
        cases i
        refine ⟨f (), hchild_mem (), rfl, rfl⟩
  | send p labels =>
      let g : LocalTypeChild (LocalTypeHead.send p labels) → LocalTypeC :=
        PFunctor.M.corec (RegularSystem t h) ∘ fun i => StateIndex t h (f i)
      refine ⟨LocalTypeHead.send p labels, f, g, ?_, ?_, ?_⟩
      · rfl
      · have hsys := RegularSystem_at_index t h s1 hs
        simp [hdest] at hsys
        simp [SystemToCoind, PFunctor.M.dest_corec, hsys, g]
        rfl
      · intro i
        refine ⟨f i, hchild_mem i, rfl, rfl⟩
  | recv p labels =>
      let g : LocalTypeChild (LocalTypeHead.recv p labels) → LocalTypeC :=
        PFunctor.M.corec (RegularSystem t h) ∘ fun i => StateIndex t h (f i)
      refine ⟨LocalTypeHead.recv p labels, f, g, ?_, ?_, ?_⟩
      · rfl
      · have hsys := RegularSystem_at_index t h s1 hs
        simp [hdest] at hsys
        simp [SystemToCoind, PFunctor.M.dest_corec, hsys, g]
        rfl
      · intro i
        refine ⟨f i, hchild_mem i, rfl, rfl⟩

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

/-- Regular coinductive types coincide with their finite-system presentation. -/
theorem Regular_implies_System_eq (t : LocalTypeC) (h : Regular t) :
    ∃ (n : Nat) (sys : FiniteSystem n) (start : Fin n),
      t = SystemToCoind sys start := by
  rcases Regular_implies_System t h with ⟨n, sys, start, hbisim⟩
  have hEq : t = SystemToCoind sys start :=
    (Bisim_eq_iff t (SystemToCoind sys start)).1 hbisim
  exact ⟨n, sys, start, hEq⟩

end RumpsteakV2.Coinductive
