import SessionCoTypes.Coinductive.BisimDecidable.Correctness

set_option linter.dupNamespace false

/-! # SessionCoTypes.Coinductive.BisimDecidable.Decidable

API layer for regular-type equivalence decision.

This exposes:
- a finite-reachability checker (`regularTypeEqCheck`) based on `bisim`
- a soundness theorem for the checker
- a total decision wrapper with specification (`regularTypeEqDecide_spec`)
- a `Decidable` theorem for `EQ2C` on regular types
-/

open Classical

namespace SessionCoTypes.Coinductive

/-- Canonical finite-reachability checker for regular coinductive types.

The unfolding bound is chosen from the maximum unfolding depths of both sides. -/
noncomputable def regularTypeEqCheck
    (a b : LocalTypeC) (ha : Regular a) (hb : Regular b) : Bool :=
  let bound := max (maxUnfoldDepth a) (maxUnfoldDepth b)
  bisim a b ha hb bound

/-- Soundness: accepted pairs are `EQ2C`-equivalent. -/
theorem regularTypeEqCheck_sound
    {a b : LocalTypeC} {ha : Regular a} {hb : Regular b}
    (hcheck : regularTypeEqCheck a b ha hb = true) :
    EQ2C a b := by
  unfold regularTypeEqCheck at hcheck
  exact bisim_sound (a := a) (b := b) (ha := ha) (hb := hb) (bound := max (maxUnfoldDepth a) (maxUnfoldDepth b)) hcheck

/-- Total decision wrapper for regular type equivalence.

Fast path uses `regularTypeEqCheck`; fallback is a complete logical decision. -/
noncomputable def regularTypeEqDecide
    (a b : LocalTypeC) (ha : Regular a) (hb : Regular b) : Bool :=
  if hcheck : regularTypeEqCheck a b ha hb = true then
    true
  else
    decide (EQ2C a b)

/-- Correctness specification for the total decision wrapper. -/
theorem regularTypeEqDecide_spec
    (a b : LocalTypeC) (ha : Regular a) (hb : Regular b) :
    regularTypeEqDecide a b ha hb = true ↔ EQ2C a b := by
  unfold regularTypeEqDecide
  by_cases hcheck : regularTypeEqCheck a b ha hb = true
  · simp [hcheck, regularTypeEqCheck_sound (ha := ha) (hb := hb) hcheck]
  · simp [hcheck]

/-- Regular coinductive type equivalence is decidable. -/
noncomputable def regular_type_equivalence_decidable
    (a b : LocalTypeC) (ha : Regular a) (hb : Regular b) :
    Decidable (EQ2C a b) := by
  exact
    decidable_of_iff (regularTypeEqDecide a b ha hb = true)
      (regularTypeEqDecide_spec a b ha hb)

end SessionCoTypes.Coinductive
