import Mathlib.Order.FixedPoints

/-! # CoinductiveRel

Shared coinduction infrastructure for monotone endofunctors on complete lattices.
This is a thin wrapper around `OrderHom.gfp` with reusable coinduction, unfold,
and fold principles.
-/

namespace RumpsteakV2.Protocol.CoTypes.CoinductiveRel

/-- Binary relation on a type. -/
abbrev Rel (α : Type*) := α → α → Prop

class CoinductiveRel (R : Type*) [CompleteLattice R] (F : R → R) : Prop where
  mono : Monotone F

def gfp {R : Type*} [CompleteLattice R] {F : R → R} [CoinductiveRel R F] : R :=
  OrderHom.gfp ⟨F, CoinductiveRel.mono⟩

theorem gfp_fixed {R : Type*} [CompleteLattice R] {F : R → R} [CoinductiveRel R F] :
    F (gfp (F := F)) = gfp (F := F) := by
  simpa [gfp] using (OrderHom.isFixedPt_gfp ⟨F, CoinductiveRel.mono⟩)


@[simp] theorem gfp_fixed_simp {R : Type*} [CompleteLattice R] {F : R → R} [CoinductiveRel R F] :
    F (gfp (F := F)) = gfp (F := F) :=
  gfp_fixed (F := F)

theorem coind {R : Type*} [CompleteLattice R] {F : R → R} [CoinductiveRel R F]
    {S : R} (h : S ≤ F S) : S ≤ gfp (F := F) := by
  exact OrderHom.le_gfp ⟨F, CoinductiveRel.mono⟩ h

theorem unfold {R : Type*} [CompleteLattice R] {F : R → R} [CoinductiveRel R F] :
    gfp (F := F) ≤ F (gfp (F := F)) := by
  simpa [gfp_fixed (F := F)] using (le_of_eq (gfp_fixed (F := F)).symm)

theorem fold {R : Type*} [CompleteLattice R] {F : R → R} [CoinductiveRel R F] :
    F (gfp (F := F)) ≤ gfp (F := F) := by
  simpa [gfp_fixed (F := F)] using (le_of_eq (gfp_fixed (F := F)))

end RumpsteakV2.Protocol.CoTypes.CoinductiveRel
