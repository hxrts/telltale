import Mathlib
import RumpsteakV2.Coinductive.LocalTypeC
import RumpsteakV2.Coinductive.Observable

set_option linter.dupNamespace false

/-!
# EQ2C: Equi-recursive equality on LocalTypeC

Defines an observable-based bisimulation that treats μ-unfolding as silent.
-/

namespace RumpsteakV2.Coinductive

-- Alias Label to avoid ambiguity
abbrev Label := RumpsteakV2.Protocol.GlobalType.Label

/-- Branch relation: labels match and continuations are related by `R`. -/
def BranchesRelC (R : LocalTypeC → LocalTypeC → Prop)
    (bs cs : List (Label × LocalTypeC)) : Prop :=
  List.Forall₂ (fun b c => b.1 = c.1 ∧ R b.2 c.2) bs cs

lemma BranchesRelC_refl (R : LocalTypeC → LocalTypeC → Prop)
    (h : ∀ t, R t t) : ∀ bs, BranchesRelC R bs bs := by
  intro bs
  induction bs with
  | nil => exact List.Forall₂.nil
  | cons b bs ih =>
      constructor
      · exact ⟨rfl, h b.2⟩
      · exact ih

lemma BranchesRelC_flip {R : LocalTypeC → LocalTypeC → Prop}
    (h : ∀ a b, R a b → R b a) :
    ∀ {bs cs}, BranchesRelC R bs cs → BranchesRelC R cs bs := by
  intro bs cs hrel
  induction hrel with
  | nil => exact List.Forall₂.nil
  | cons hbc hrest ih =>
      rcases hbc with ⟨hlabel, hrel⟩
      constructor
      · exact ⟨hlabel.symm, h _ _ hrel⟩
      · exact ih

lemma BranchesRelC_comp {R S : LocalTypeC → LocalTypeC → Prop}
    (T : LocalTypeC → LocalTypeC → Prop) (hT : ∀ a c, T a c ↔ ∃ b, R a b ∧ S b c) :
    ∀ {bs cs ds}, BranchesRelC R bs cs → BranchesRelC S cs ds → BranchesRelC T bs ds := by
  -- TODO: Fix after TypeContext refactoring
  sorry

/-- Observable relation between two coinductive types, parameterized by `R`. -/
inductive ObservableRelC (R : LocalTypeC → LocalTypeC → Prop) :
    {a b : LocalTypeC} → ObservableC a → ObservableC b → Prop
  | is_end {a b} (ha : UnfoldsToEndC a) (hb : UnfoldsToEndC b) :
      ObservableRelC R (ObservableC.is_end ha) (ObservableC.is_end hb)
  | is_var {a b} (v : String) (ha : UnfoldsToVarC a v) (hb : UnfoldsToVarC b v) :
      ObservableRelC R (ObservableC.is_var v ha) (ObservableC.is_var v hb)
  | is_send {a b} (p : String) (bs cs : List (Label × LocalTypeC))
      (ha : CanSendC a p bs) (hb : CanSendC b p cs) (hbr : BranchesRelC R bs cs) :
      ObservableRelC R (ObservableC.is_send p bs ha) (ObservableC.is_send p cs hb)
  | is_recv {a b} (p : String) (bs cs : List (Label × LocalTypeC))
      (ha : CanRecvC a p bs) (hb : CanRecvC b p cs) (hbr : BranchesRelC R bs cs) :
      ObservableRelC R (ObservableC.is_recv p bs ha) (ObservableC.is_recv p cs hb)

/-- Observable relation is reflexive (for a relation reflexive on states). -/
lemma ObservableRelC_refl (R : LocalTypeC → LocalTypeC → Prop) (hR : ∀ t, R t t)
    {a : LocalTypeC} (obs : ObservableC a) : ObservableRelC R obs obs := by
  cases obs with
  | is_end ha => exact ObservableRelC.is_end ha ha
  | is_var v ha => exact ObservableRelC.is_var v ha ha
  | is_send p bs ha =>
      exact ObservableRelC.is_send p bs bs ha ha (BranchesRelC_refl R hR bs)
  | is_recv p bs ha =>
      exact ObservableRelC.is_recv p bs bs ha ha (BranchesRelC_refl R hR bs)

/-- Observable relation is symmetric. -/
lemma ObservableRelC_symm {R : LocalTypeC → LocalTypeC → Prop}
    (hR : ∀ a b, R a b → R b a) :
    ∀ {a b} {obs_a : ObservableC a} {obs_b : ObservableC b},
      ObservableRelC R obs_a obs_b → ObservableRelC R obs_b obs_a := by
  intro a b obs_a obs_b hrel
  cases hrel with
  | is_end ha hb => exact ObservableRelC.is_end hb ha
  | is_var v ha hb => exact ObservableRelC.is_var v hb ha
  | is_send p bs cs ha hb hbr =>
      exact ObservableRelC.is_send p cs bs hb ha (BranchesRelC_flip hR hbr)
  | is_recv p bs cs ha hb hbr =>
      exact ObservableRelC.is_recv p cs bs hb ha (BranchesRelC_flip hR hbr)

/-- Observable relation composes through relational composition. -/
lemma ObservableRelC_comp {R S : LocalTypeC → LocalTypeC → Prop}
    (T : LocalTypeC → LocalTypeC → Prop) (hT : ∀ a c, T a c ↔ ∃ b, R a b ∧ S b c) :
    ∀ {a b c} {obs_a : ObservableC a} {obs_b : ObservableC b} {obs_c : ObservableC c},
      ObservableRelC R obs_a obs_b → ObservableRelC S obs_b obs_c → ObservableRelC T obs_a obs_c := by
  -- TODO: Fix after TypeContext refactoring
  sorry

/-- A relation is an EQ2C-bisimulation if it relates observable heads. -/
def IsBisimulationC (R : LocalTypeC → LocalTypeC → Prop) : Prop :=
  ∀ a b, R a b → ∃ obs_a : ObservableC a, ∃ obs_b : ObservableC b, ObservableRelC R obs_a obs_b

/-- Equi-recursive equality on `LocalTypeC`. -/
def EQ2C (a b : LocalTypeC) : Prop :=
  ∃ R, IsBisimulationC R ∧ R a b

/-- Reflexivity for observable states. -/
lemma EQ2C_refl_of_observable {a : LocalTypeC} (obs : ObservableC a) : EQ2C a a := by
  -- TODO: Fix after TypeContext refactoring
  sorry

/-- Symmetry. -/
lemma EQ2C_symm {a b : LocalTypeC} (h : EQ2C a b) : EQ2C b a := by
  -- TODO: Fix after TypeContext refactoring
  sorry

/-- Transitivity. -/
lemma EQ2C_trans {a b c : LocalTypeC} (hab : EQ2C a b) (hbc : EQ2C b c) : EQ2C a c := by
  rcases hab with ⟨R, hR, hab⟩
  rcases hbc with ⟨S, hS, hbc⟩
  let T : LocalTypeC → LocalTypeC → Prop := fun x z => ∃ y, R x y ∧ S y z
  refine ⟨T, ?_, ⟨b, hab, hbc⟩⟩
  intro x z hxz
  rcases hxz with ⟨y, hxy, hyz⟩
  obtain ⟨obs_x, obs_y, hrel_xy⟩ := hR x y hxy
  obtain ⟨obs_y', obs_z, hrel_yz⟩ := hS y z hyz
  -- Use proof irrelevance to align observables on `y`.
  have : obs_y = obs_y' := by
    apply Subsingleton.elim _ _
  subst this
  refine ⟨obs_x, obs_z, ?_⟩
  exact ObservableRelC_comp T (by intro a c; rfl) hrel_xy hrel_yz

end RumpsteakV2.Coinductive
