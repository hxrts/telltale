-- Minimal subsequence-based subtyping used to compare local traces.
import Rumpsteak.Projection

/-! Provides a lightweight subtyping check to ensure exported local types
    maintain a consistent action ordering relative to projections. -/

namespace Rumpsteak.Subtyping

open Rumpsteak.Projection

/-- Tests whether `sub` is a subsequence of `sup`, keeping order (uses decidable equality). -/
def isSubsequence {α : Type} [DecidableEq α] : List α → List α → Bool
  | [], _ => true
  | _, [] => false
  | a :: as, b :: bs =>
    if a = b then
      isSubsequence as bs
    else
      isSubsequence (a :: as) bs
termination_by xs ys => (xs.length, ys.length)

/- Ensure the sub list can be embedded into the super list without reordering. -/
def isSubtype (sub sup : LocalType) : Bool :=
  sub.actions.length <= sup.actions.length &&
    isSubsequence sub.actions sup.actions

/-- Reflexivity: any list is a subsequence of itself. -/
theorem isSubsequence_refl {α} [DecidableEq α] (xs : List α) :
    isSubsequence xs xs = true := by
  induction xs with
  | nil => simp [isSubsequence]
  | cons a t ih =>
      simp [isSubsequence, ih]

/-- Reflexivity: any local type is a subtype of itself. -/
theorem isSubtype_refl (lt : LocalType) : isSubtype lt lt = true := by
  simp [isSubtype, isSubsequence_refl]

end Rumpsteak.Subtyping
