import Mathlib
import SessionCoTypes.Coinductive.LocalTypeC
import SessionCoTypes.Coinductive.Regularity
import SessionCoTypes.Coinductive.FiniteSystem
import SessionCoTypes.Coinductive.Bisim

set_option linter.dupNamespace false

/-! # Regular System Bisimulation

Bisimulation proof for regular coalgebra reconstruction. -/

/-
The Problem. RegularSystem extracts a finite coalgebra from a regular coinductive
type. We need to prove that reconstructing from this system via SystemToCoind
yields a bisimilar (hence equal) type.

Solution Structure. Proves get_StateIndex correctly retrieves indexed states,
RegularSystem_at_index shows system matches dest of state, defines RegularBisim
relating states to their reconstructions, and proves this satisfies IsBisimulation.
-/

-- Core Development

namespace SessionCoTypes.Coinductive

open Classical

attribute [local instance] Classical.decEq

-- State Index Retrieval

/-- `StateIndex` returns the index witnessing membership in the reachable list. -/
theorem get_StateIndex (t : LocalTypeC) (h : Regular t) (s : LocalTypeC)
    (hs : s ∈ ReachableList (witnessOfRegular h)) :
    (ReachableList (witnessOfRegular h)).get (StateIndex (witnessOfRegular h) s) = s := by
  let w := witnessOfRegular h
  change s ∈ ReachableList w at hs
  change (ReachableList w).get (StateIndex w s) = s
  unfold StateIndex
  cases hidx : (ReachableList w).finIdxOf? s with
  | none =>
      have hnot : s ∉ ReachableList w := (List.finIdxOf?_eq_none_iff).1 hidx
      exact (hnot hs).elim
  | some i =>
      have hget : (ReachableList w)[i] = s := (List.finIdxOf?_eq_some_iff).1 hidx |>.1
      simpa [hidx] using hget

-- RegularSystem at Indexed States

/-- One-step behavior of the regular system at a reachable state. -/
theorem RegularSystem_at_index (t : LocalTypeC) (h : Regular t) (s : LocalTypeC)
    (hs : s ∈ ReachableList (witnessOfRegular h)) :
    RegularSystem (witnessOfRegular h) (StateIndex (witnessOfRegular h) s) =
      match PFunctor.M.dest s with
      | ⟨.end, _⟩ => ⟨.end, fun x => PEmpty.elim x⟩
      | ⟨.var v, _⟩ => ⟨.var v, fun x => PEmpty.elim x⟩
      | ⟨.mu v, f⟩ => ⟨.mu v, fun _ => StateIndex (witnessOfRegular h) (f ())⟩
      | ⟨.send p labels, f⟩ =>
          ⟨.send p labels, fun j => StateIndex (witnessOfRegular h) (f j)⟩
      | ⟨.recv p labels, f⟩ =>
          ⟨.recv p labels, fun j => StateIndex (witnessOfRegular h) (f j)⟩ := by
      let w := witnessOfRegular h
      change s ∈ ReachableList w at hs
      change RegularSystem w (StateIndex w s) =
        match PFunctor.M.dest s with
        | ⟨.end, _⟩ => ⟨.end, fun x => PEmpty.elim x⟩
        | ⟨.var v, _⟩ => ⟨.var v, fun x => PEmpty.elim x⟩
        | ⟨.mu v, f⟩ => ⟨.mu v, fun _ => StateIndex w (f ())⟩
        | ⟨.send p labels, f⟩ =>
            ⟨.send p labels, fun j => StateIndex w (f j)⟩
        | ⟨.recv p labels, f⟩ =>
            ⟨.recv p labels, fun j => StateIndex w (f j)⟩
      unfold RegularSystem
      rw [get_StateIndex t h s hs]
      rfl

-- RegularBisim Relation

/-- A bisimulation relating reachable states to their finite-system image. -/
def RegularBisim (t : LocalTypeC) (h : Regular t)
    (sys : FiniteSystem (ReachableList (witnessOfRegular h)).length) (s1 s2 : LocalTypeC) : Prop :=
  ∃ s, s ∈ ReachableList (witnessOfRegular h) ∧
    s1 = s ∧ s2 = SystemToCoind sys (StateIndex (witnessOfRegular h) s)

-- RegularBisim Is a Bisimulation

/-- The regular bisimulation is a bisimulation. -/
theorem RegularBisim_isBisimulation (t : LocalTypeC) (h : Regular t) :
    IsBisimulation (RegularBisim t h (RegularSystem (witnessOfRegular h))) := by
  classical
  let w := witnessOfRegular h
  intro s1 s2 hrel
  change RegularBisim t h (RegularSystem w) s1 s2 at hrel
  rcases hrel with ⟨s, hs, rfl, rfl⟩
  rcases hdest : PFunctor.M.dest s1 with ⟨hd, f⟩
  have hchild_mem :
      ∀ i : LocalTypeChild hd, f i ∈ ReachableList w := by
    intro i
    have hchild : childRel s1 (f i) := by
      exact ⟨hd, f, i, hdest, rfl⟩
    exact w.closed s1 hs _ hchild
  cases hd with
  -- Head Case: end
  | «end» =>
      let g : LocalTypeChild LocalTypeHead.end → LocalTypeC :=
        PFunctor.M.corec (RegularSystem w) ∘ fun x => PEmpty.elim x
      refine ⟨LocalTypeHead.end, f, g, ?_, ?_, ?_⟩
      · rfl
      · have hsys := RegularSystem_at_index t h s1 hs
        simp [hdest] at hsys
        have hmap :=
          congrArg (LocalTypeF.map (PFunctor.M.corec (RegularSystem w))) hsys
        simpa [SystemToCoind, PFunctor.M.dest_corec, g, Function.comp] using hmap
      · intro i
        cases i
  -- Head Case: var
  | var v =>
      let g : LocalTypeChild (LocalTypeHead.var v) → LocalTypeC :=
        PFunctor.M.corec (RegularSystem w) ∘ fun x => PEmpty.elim x
      refine ⟨LocalTypeHead.var v, f, g, ?_, ?_, ?_⟩
      · rfl
      · have hsys := RegularSystem_at_index t h s1 hs
        simp [hdest] at hsys
        have hmap :=
          congrArg (LocalTypeF.map (PFunctor.M.corec (RegularSystem w))) hsys
        simpa [SystemToCoind, PFunctor.M.dest_corec, g, Function.comp] using hmap
      · intro i
        cases i
  -- Head Case: mu
  | mu v =>
      let g : LocalTypeChild (LocalTypeHead.mu v) → LocalTypeC :=
        PFunctor.M.corec (RegularSystem w) ∘ fun _ => StateIndex w (f ())
      refine ⟨LocalTypeHead.mu v, f, g, ?_, ?_, ?_⟩
      · rfl
      · have hsys := RegularSystem_at_index t h s1 hs
        simp [hdest] at hsys
        have hmap :=
          congrArg (LocalTypeF.map (PFunctor.M.corec (RegularSystem w))) hsys
        simpa [SystemToCoind, PFunctor.M.dest_corec, g, Function.comp] using hmap
      · intro i
        cases i
        refine ⟨f (), hchild_mem (), rfl, rfl⟩
  -- Head Case: send
  | send p labels =>
      let g : LocalTypeChild (LocalTypeHead.send p labels) → LocalTypeC :=
        PFunctor.M.corec (RegularSystem w) ∘ fun i => StateIndex w (f i)
      refine ⟨LocalTypeHead.send p labels, f, g, ?_, ?_, ?_⟩
      · rfl
      · have hsys := RegularSystem_at_index t h s1 hs
        simp [hdest] at hsys
        have hmap :=
          congrArg (LocalTypeF.map (PFunctor.M.corec (RegularSystem w))) hsys
        simpa [SystemToCoind, PFunctor.M.dest_corec, g, Function.comp] using hmap
      · intro i
        refine ⟨f i, hchild_mem i, rfl, rfl⟩
  -- Head Case: recv
  | recv p labels =>
      let g : LocalTypeChild (LocalTypeHead.recv p labels) → LocalTypeC :=
        PFunctor.M.corec (RegularSystem w) ∘ fun i => StateIndex w (f i)
      refine ⟨LocalTypeHead.recv p labels, f, g, ?_, ?_, ?_⟩
      · rfl
      · have hsys := RegularSystem_at_index t h s1 hs
        simp [hdest] at hsys
        have hmap :=
          congrArg (LocalTypeF.map (PFunctor.M.corec (RegularSystem w))) hsys
        simpa [SystemToCoind, PFunctor.M.dest_corec, g, Function.comp] using hmap
      · intro i
        refine ⟨f i, hchild_mem i, rfl, rfl⟩

-- Finite-System Extraction Theorems

/-- Regular coinductive types are bisimilar to their finite-system presentation. -/
theorem Regular_implies_System (t : LocalTypeC) (h : Regular t) :
    ∃ (n : Nat) (sys : FiniteSystem n) (start : Fin n),
      Bisim t (SystemToCoind sys start) := by
  classical
  let w := witnessOfRegular h
  let n := (ReachableList w).length
  let sys := RegularSystem w
  let start := StateIndex w t
  refine ⟨n, sys, start, ?_⟩
  refine ⟨RegularBisim t h sys, RegularBisim_isBisimulation t h, ?_⟩
  refine ⟨t, ?_, rfl, rfl⟩
  exact w.root_mem

/-- Regular coinductive types coincide with their finite-system presentation. -/
theorem Regular_implies_System_eq (t : LocalTypeC) (h : Regular t) :
    ∃ (n : Nat) (sys : FiniteSystem n) (start : Fin n),
      t = SystemToCoind sys start := by
  rcases Regular_implies_System t h with ⟨n, sys, start, hbisim⟩
  have hEq : t = SystemToCoind sys start :=
    (Bisim_eq_iff t (SystemToCoind sys start)).1 hbisim
  exact ⟨n, sys, start, hEq⟩

end SessionCoTypes.Coinductive
