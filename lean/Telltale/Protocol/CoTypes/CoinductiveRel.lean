import Mathlib.Order.FixedPoints

set_option linter.dupNamespace false

/-! # CoinductiveRel

Shared coinduction infrastructure for monotone endofunctors on complete lattices.
This is a thin wrapper around `OrderHom.gfp` with reusable coinduction, unfold,
and fold principles.
-/

namespace Telltale.Protocol.CoTypes.CoinductiveRel

/-- Binary relation on a type. -/
abbrev Rel (α : Type*) := α → α → Prop

/-- Typeclass witnessing that `F` is a monotone endofunctor, enabling coinduction. -/
class CoinductiveRel (R : Type*) [CompleteLattice R] (F : R → R) : Prop where
  mono : Monotone F

/-- Greatest fixed point of the monotone functor `F`. -/
def gfp {R : Type*} [CompleteLattice R] {F : R → R} [CoinductiveRel R F] : R :=
  OrderHom.gfp ⟨F, CoinductiveRel.mono⟩

/-- The greatest fixed point is a fixed point: `F gfp = gfp`. -/
theorem gfp_fixed {R : Type*} [CompleteLattice R] {F : R → R} [CoinductiveRel R F] :
    F (gfp (F := F)) = gfp (F := F) := by
  simpa [gfp] using (OrderHom.isFixedPt_gfp ⟨F, CoinductiveRel.mono⟩)

/-- Simp lemma: the greatest fixed point is a fixed point. -/
@[simp] theorem gfp_fixed_simp {R : Type*} [CompleteLattice R] {F : R → R} [CoinductiveRel R F] :
    F (gfp (F := F)) = gfp (F := F) :=
  gfp_fixed (F := F)

/-- Coinduction principle: if `S` is a post-fixpoint (`S ≤ F S`), then `S ≤ gfp`. -/
theorem coind {R : Type*} [CompleteLattice R] {F : R → R} [CoinductiveRel R F]
    {S : R} (h : S ≤ F S) : S ≤ gfp (F := F) := by
  exact OrderHom.le_gfp ⟨F, CoinductiveRel.mono⟩ h

/-- Unfold principle: `gfp ≤ F gfp` (immediate from fixed point). -/
theorem unfold {R : Type*} [CompleteLattice R] {F : R → R} [CoinductiveRel R F] :
    gfp (F := F) ≤ F (gfp (F := F)) := by
  exact (le_of_eq (gfp_fixed (F := F)).symm)

/-- Fold principle: `F gfp ≤ gfp` (immediate from fixed point). -/
theorem fold {R : Type*} [CompleteLattice R] {F : R → R} [CoinductiveRel R F] :
    F (gfp (F := F)) ≤ gfp (F := F) := by
  exact (le_of_eq (gfp_fixed (F := F)))

end Telltale.Protocol.CoTypes.CoinductiveRel
