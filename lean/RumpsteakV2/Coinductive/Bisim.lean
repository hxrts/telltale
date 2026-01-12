import Mathlib
import RumpsteakV2.Coinductive.LocalTypeC

set_option linter.dupNamespace false

/-!
# Bisimulation for LocalTypeC

Defines a membership-based bisimulation relation for coinductive local types and
proves that it is an equivalence relation.
-/

namespace RumpsteakV2.Coinductive

/-- A relation is a bisimulation if heads match and children are related. -/
def IsBisimulation (R : LocalTypeC → LocalTypeC → Prop) : Prop :=
  ∀ x y, R x y →
    ∃ s f g,
      PFunctor.M.dest x = ⟨s, f⟩ ∧
      PFunctor.M.dest y = ⟨s, g⟩ ∧
      ∀ i, R (f i) (g i)

/-- Bisimilarity: there exists a bisimulation relating the two states. -/
def Bisim (x y : LocalTypeC) : Prop :=
  ∃ R, IsBisimulation R ∧ R x y

/-- Bisimilarity is reflexive. -/
theorem Bisim_refl : ∀ x : LocalTypeC, Bisim x x := by
  intro x
  refine ⟨fun a b => a = b, ?_, rfl⟩
  intro a b h
  subst h
  obtain ⟨s, f⟩ := PFunctor.M.dest a
  refine ⟨s, f, f, rfl, rfl, ?_⟩
  intro i
  rfl

/-- Bisimilarity is symmetric. -/
theorem Bisim_symm : ∀ x y : LocalTypeC, Bisim x y → Bisim y x := by
  rintro x y ⟨R, hR, hxy⟩
  refine ⟨fun a b => R b a, ?_, hxy⟩
  intro a b hba
  obtain ⟨s, f, g, hx, hy, hfg⟩ := hR b a hba
  refine ⟨s, g, f, hy, hx, ?_⟩
  intro i
  exact hfg i

/-- Bisimilarity is transitive. -/
theorem Bisim_trans : ∀ x y z : LocalTypeC, Bisim x y → Bisim y z → Bisim x z := by
  rintro x y z ⟨R, hR, hxy⟩ ⟨S, hS, hyz⟩
  let T : LocalTypeC → LocalTypeC → Prop := fun a c => ∃ b, R a b ∧ S b c
  refine ⟨T, ?_, ?_⟩
  · intro a c hT
    rcases hT with ⟨b, hab, hbc⟩
    obtain ⟨s, f1, f2, ha, hb, hRstep⟩ := hR a b hab
    obtain ⟨t, g1, g2, hb', hc, hSstep⟩ := hS b c hbc
    -- align the middle witness for `b` so the child functions have matching domains
    cases hb'.symm.trans hb
    refine ⟨s, f1, g2, ha, hc, ?_⟩
    intro i
    exact ⟨f2 i, hRstep i, hSstep i⟩
  · exact ⟨y, hxy, hyz⟩

/-! ## Extensionality for `LocalTypeC` -/

/-- Bisimilarity coincides with equality for `LocalTypeC` (M-types are extensional). -/
theorem Bisim_eq_iff (x y : LocalTypeC) : Bisim x y ↔ x = y := by
  constructor
  · intro h
    rcases h with ⟨R, hR, hxy⟩
    apply PFunctor.M.bisim R
    · intro a b hab
      obtain ⟨s, f, g, ha, hb, hfg⟩ := hR a b hab
      exact ⟨s, f, g, ha, hb, hfg⟩
    · exact hxy
  · intro h
    subst h
    exact Bisim_refl _

end RumpsteakV2.Coinductive
