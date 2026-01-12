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

lemma BranchesRelC_mono {R S : LocalTypeC → LocalTypeC → Prop}
    (h : ∀ a b, R a b → S a b) :
    ∀ {bs cs}, BranchesRelC R bs cs → BranchesRelC S bs cs := by
  intro bs cs hrel
  exact List.Forall₂.imp (fun a b hab => ⟨hab.1, h _ _ hab.2⟩) hrel

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

lemma BranchesRelC_swap (R : LocalTypeC → LocalTypeC → Prop) :
    ∀ {bs cs}, BranchesRelC R bs cs → BranchesRelC (fun x y => R y x) cs bs := by
  intro bs cs hrel
  induction hrel with
  | nil => exact List.Forall₂.nil
  | cons hbc hrest ih =>
      rcases hbc with ⟨hlabel, hrel⟩
      constructor
      · exact ⟨hlabel.symm, hrel⟩
      · exact ih

lemma BranchesRelC_comp {R S : LocalTypeC → LocalTypeC → Prop}
    (T : LocalTypeC → LocalTypeC → Prop) (hT : ∀ a c, T a c ↔ ∃ b, R a b ∧ S b c) :
    ∀ {bs cs ds}, BranchesRelC R bs cs → BranchesRelC S cs ds → BranchesRelC T bs ds := by
  intro bs cs ds hrel1 hrel2
  induction hrel1 generalizing ds with
  | nil =>
      cases hrel2
      exact List.Forall₂.nil
  | cons hbc hrest ih =>
      cases hrel2 with
      | cons hcd hrest2 =>
          rcases hbc with ⟨hlab1, hR⟩
          rcases hcd with ⟨hlab2, hS⟩
          have hT' : T _ _ := (hT _ _).2 ⟨_, hR, hS⟩
          refine List.Forall₂.cons ?_ (ih hrest2)
          exact ⟨hlab1.trans hlab2, hT'⟩

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

/-- Observable relation is monotone in the underlying relation. -/
lemma ObservableRelC_mono {R S : LocalTypeC → LocalTypeC → Prop}
    (h : ∀ a b, R a b → S a b) :
    ∀ {a b} {obs_a : ObservableC a} {obs_b : ObservableC b},
      ObservableRelC R obs_a obs_b → ObservableRelC S obs_a obs_b := by
  intro a b obs_a obs_b hrel
  cases hrel with
  | is_end ha hb => exact ObservableRelC.is_end ha hb
  | is_var v ha hb => exact ObservableRelC.is_var v ha hb
  | is_send p bs cs ha hb hbr =>
      exact ObservableRelC.is_send p bs cs ha hb (BranchesRelC_mono h hbr)
  | is_recv p bs cs ha hb hbr =>
      exact ObservableRelC.is_recv p bs cs ha hb (BranchesRelC_mono h hbr)

/-- Observable relation composes through relational composition. -/
lemma ObservableRelC_comp {R S : LocalTypeC → LocalTypeC → Prop}
    (T : LocalTypeC → LocalTypeC → Prop) (hT : ∀ a c, T a c ↔ ∃ b, R a b ∧ S b c) :
    ∀ {a b c} {obs_a : ObservableC a} {obs_b : ObservableC b} {obs_c : ObservableC c},
      ObservableRelC R obs_a obs_b → ObservableRelC S obs_b obs_c → ObservableRelC T obs_a obs_c := by
  intro a b c obs_a obs_b obs_c hrel1 hrel2
  cases hrel1 with
  | is_end ha hb =>
      cases hrel2 with
      | is_end hb' hc => exact ObservableRelC.is_end ha hc
  | is_var v ha hb =>
      cases hrel2 with
      | is_var _ hb' hc => exact ObservableRelC.is_var v ha hc
  | is_send p bs cs ha hb hbr1 =>
      cases hrel2 with
      | is_send _ cs' ds hb' hc hbr2 =>
          have hbr : BranchesRelC T bs ds := BranchesRelC_comp T hT hbr1 hbr2
          exact ObservableRelC.is_send p bs ds ha hc hbr
  | is_recv p bs cs ha hb hbr1 =>
      cases hrel2 with
      | is_recv _ cs' ds hb' hc hbr2 =>
          have hbr : BranchesRelC T bs ds := BranchesRelC_comp T hT hbr1 hbr2
          exact ObservableRelC.is_recv p bs ds ha hc hbr

/-- A relation is an EQ2C-bisimulation if it relates observable heads. -/
def IsBisimulationC (R : LocalTypeC → LocalTypeC → Prop) : Prop :=
  ∀ a b, R a b → ∃ obs_a : ObservableC a, ∃ obs_b : ObservableC b, ObservableRelC R obs_a obs_b

/-- Equi-recursive equality on `LocalTypeC`. -/
def EQ2C (a b : LocalTypeC) : Prop :=
  ∃ R, IsBisimulationC R ∧ R a b

/-- Symmetry. -/
lemma EQ2C_symm {a b : LocalTypeC} (h : EQ2C a b) : EQ2C b a := by
  rcases h with ⟨R, hR, hab⟩
  let R' : LocalTypeC → LocalTypeC → Prop := fun x y => R y x
  have hswap :
      ∀ {x y} {obs_x : ObservableC x} {obs_y : ObservableC y},
        ObservableRelC R obs_x obs_y → ObservableRelC R' obs_y obs_x := by
    intro x y obs_x obs_y hrel
    cases hrel with
    | is_end ha hb => exact ObservableRelC.is_end hb ha
    | is_var v ha hb => exact ObservableRelC.is_var v hb ha
    | is_send p bs cs ha hb hbr =>
        have hbr' : BranchesRelC R' cs bs := BranchesRelC_swap R hbr
        exact ObservableRelC.is_send p cs bs hb ha hbr'
    | is_recv p bs cs ha hb hbr =>
        have hbr' : BranchesRelC R' cs bs := BranchesRelC_swap R hbr
        exact ObservableRelC.is_recv p cs bs hb ha hbr'
  refine ⟨R', ?_, hab⟩
  intro x y hxy
  obtain ⟨obs_y, obs_x, hrel⟩ := hR y x hxy
  exact ⟨obs_x, obs_y, hswap hrel⟩

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
