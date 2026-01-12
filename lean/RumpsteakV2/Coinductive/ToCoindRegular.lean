import Mathlib
import RumpsteakV2.Coinductive.LocalTypeC
import RumpsteakV2.Coinductive.Bridge
import RumpsteakV2.Coinductive.RegularityLemmas
import RumpsteakV2.Protocol.LocalTypeR

set_option linter.dupNamespace false

/-!
# Regularity of `toCoind`
-/

namespace RumpsteakV2.Coinductive

open RumpsteakV2.Protocol.LocalTypeR

private lemma children_mkSend (p : String) (bs : List (RumpsteakV2.Protocol.GlobalType.Label × LocalTypeC))
    (i : Fin (bs.map Prod.fst).length) :
    children (mkSend p bs) i = (bs.get (castFin (by simp) i)).2 := by
  simp [children, mkSend]

private lemma children_mkRecv (p : String) (bs : List (RumpsteakV2.Protocol.GlobalType.Label × LocalTypeC))
    (i : Fin (bs.map Prod.fst).length) :
    children (mkRecv p bs) i = (bs.get (castFin (by simp) i)).2 := by
  simp [children, mkRecv]

/-- `toCoind` produces a regular coinductive type. -/
theorem toCoind_regular : ∀ t : LocalTypeR, Regular (toCoind t)
  | .end => by
      apply regular_of_children
      intro i; cases i
  | .var x => by
      apply regular_of_children
      intro i; cases i
  | .mu x body => by
      apply regular_of_children
      intro i
      cases i
      simpa [toCoind] using toCoind_regular body
  | .send p bs => by
      have hreg :
          ∀ b ∈ toCoindBranches bs, Regular b.2 := by
        intro b hb
        induction bs with
        | nil =>
            cases hb
        | cons head tail ih =>
            simp [toCoindBranches] at hb
            cases hb with
            | inl h =>
                subst h
                exact toCoind_regular head.2
            | inr h =>
                exact ih _ h
      apply regular_of_children
      intro i
      have hchild :
          children (mkSend p (toCoindBranches bs)) i =
            ((toCoindBranches bs).get (castFin (by simp) i)).2 := by
        simpa using (children_mkSend p (toCoindBranches bs) i)
      have hmem :
          (toCoindBranches bs).get (castFin (by simp) i) ∈ toCoindBranches bs :=
        List.get_mem (l := toCoindBranches bs) (n := castFin (by simp) i)
      have hreg' := hreg _ hmem
      simpa [hchild] using hreg'
  | .recv p bs => by
      have hreg :
          ∀ b ∈ toCoindBranches bs, Regular b.2 := by
        intro b hb
        induction bs with
        | nil =>
            cases hb
        | cons head tail ih =>
            simp [toCoindBranches] at hb
            cases hb with
            | inl h =>
                subst h
                exact toCoind_regular head.2
            | inr h =>
                exact ih _ h
      apply regular_of_children
      intro i
      have hchild :
          children (mkRecv p (toCoindBranches bs)) i =
            ((toCoindBranches bs).get (castFin (by simp) i)).2 := by
        simpa using (children_mkRecv p (toCoindBranches bs) i)
      have hmem :
          (toCoindBranches bs).get (castFin (by simp) i) ∈ toCoindBranches bs :=
        List.get_mem (l := toCoindBranches bs) (n := castFin (by simp) i)
      have hreg' := hreg _ hmem
      simpa [hchild] using hreg'

end RumpsteakV2.Coinductive
