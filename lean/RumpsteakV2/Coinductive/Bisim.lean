import Mathlib
import RumpsteakV2.Coinductive.LocalTypeC

set_option linter.dupNamespace false

/-!
The Problem. Coinductive types don't have structural equality in the same way
as inductive types. Two coinductive trees are "the same" if they are bisimilar:
they have the same head at every level, forever. We need a bisimulation relation
for LocalTypeC and a proof that bisimilarity equals equality (extensionality).

Solution Structure.
1. Define what it means for a relation to be a bisimulation (IsBisimulation)
2. Define bisimilarity as the existence of a witnessing bisimulation (Bisim)
3. Prove Bisim is reflexive, symmetric, and transitive
4. Prove the key theorem: Bisim x y ↔ x = y (M-types are extensional)
-/

namespace RumpsteakV2.Coinductive

/-! ## Bisimulation Definition -/

/-- A relation R is a bisimulation if whenever R x y holds:
    - x and y have the same head constructor
    - their corresponding children are also R-related -/
def IsBisimulation (R : LocalTypeC → LocalTypeC → Prop) : Prop :=
  ∀ x y, R x y →
    ∃ s f g,
      PFunctor.M.dest x = ⟨s, f⟩ ∧
      PFunctor.M.dest y = ⟨s, g⟩ ∧
      ∀ i, R (f i) (g i)

/-- Bisimilarity: x and y are bisimilar if some bisimulation relates them. -/
def Bisim (x y : LocalTypeC) : Prop :=
  ∃ R, IsBisimulation R ∧ R x y

/-! ## Bisimilarity is an Equivalence -/

/-- Bisimilarity is reflexive: every type is bisimilar to itself. -/
theorem Bisim_refl : ∀ x : LocalTypeC, Bisim x x := by
  intro x
  refine ⟨fun a b => a = b, ?_, rfl⟩
  intro a b h
  subst h
  obtain ⟨s, f⟩ := PFunctor.M.dest a
  exact ⟨s, f, f, rfl, rfl, fun _ => rfl⟩

/-- Bisimilarity is symmetric: flip the relation. -/
theorem Bisim_symm : ∀ x y : LocalTypeC, Bisim x y → Bisim y x := by
  rintro x y ⟨R, hR, hxy⟩
  refine ⟨fun a b => R b a, ?_, hxy⟩
  intro a b hba
  obtain ⟨s, f, g, hx, hy, hfg⟩ := hR b a hba
  exact ⟨s, g, f, hy, hx, hfg⟩

/-- Bisimilarity is transitive: compose witnesses via an intermediate state. -/
theorem Bisim_trans : ∀ x y z : LocalTypeC, Bisim x y → Bisim y z → Bisim x z := by
  rintro x y z ⟨R, hR, hxy⟩ ⟨S, hS, hyz⟩
  let T : LocalTypeC → LocalTypeC → Prop := fun a c => ∃ b, R a b ∧ S b c
  refine ⟨T, ?_, ⟨y, hxy, hyz⟩⟩
  intro a c ⟨b, hab, hbc⟩
  obtain ⟨s, f1, f2, ha, hb, hRstep⟩ := hR a b hab
  obtain ⟨t, g1, g2, hb', hc, hSstep⟩ := hS b c hbc
  -- The middle witness for b must have matching heads
  cases hb'.symm.trans hb
  exact ⟨s, f1, g2, ha, hc, fun i => ⟨f2 i, hRstep i, hSstep i⟩⟩

/-! ## Extensionality -/

/-- Bisimilarity coincides with equality for LocalTypeC.
    This is the fundamental property of M-types: they are extensional. -/
theorem Bisim_eq_iff (x y : LocalTypeC) : Bisim x y ↔ x = y := by
  constructor
  · rintro ⟨R, hR, hxy⟩
    apply PFunctor.M.bisim R
    · intro a b hab
      obtain ⟨s, f, g, ha, hb, hfg⟩ := hR a b hab
      exact ⟨s, f, g, ha, hb, hfg⟩
    · exact hxy
  · intro h
    subst h
    exact Bisim_refl _

end RumpsteakV2.Coinductive
