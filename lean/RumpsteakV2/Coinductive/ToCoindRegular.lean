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

/-- Helper for regularity of branches. -/
private theorem toCoindBranches_regular_aux :
    (bs : List (RumpsteakV2.Protocol.GlobalType.Label × LocalTypeR)) →
    (hrec : ∀ cont : LocalTypeR, sizeOf cont < sizeOf bs → Regular (toCoind cont)) →
    ∀ b ∈ toCoindBranches bs, Regular b.2
  | [], _, b, hb => by simp [toCoindBranches] at hb
  | head :: tail, hrec, b, hb => by
      simp only [toCoindBranches, List.mem_cons] at hb
      cases hb with
      | inl h =>
          subst h
          have hsz : sizeOf head.2 < sizeOf (head :: tail) := by
            -- sizeOf (head :: tail) = 1 + sizeOf head + sizeOf tail
            -- sizeOf head ≥ sizeOf head.2 (for products)
            -- So sizeOf head.2 < 1 + sizeOf head + sizeOf tail
            have hhead : sizeOf head.2 < 1 + sizeOf head := by
              cases head; simp only [Prod.snd, Prod.mk.sizeOf_spec]; omega
            simp only [List.cons.sizeOf_spec]
            omega
          exact hrec head.2 hsz
      | inr h =>
          have htail_lt : sizeOf tail < sizeOf (head :: tail) := by
            simp only [List.cons.sizeOf_spec]
            omega
          have htail_rec : ∀ cont : LocalTypeR, sizeOf cont < sizeOf tail → Regular (toCoind cont) := by
            intro cont hcont
            exact hrec cont (Nat.lt_trans hcont htail_lt)
          exact toCoindBranches_regular_aux tail htail_rec b h

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
      have hreg := toCoindBranches_regular_aux bs (fun cont hsz => by
        have hsz' : sizeOf cont < sizeOf (LocalTypeR.send p bs) := by
          simp only [LocalTypeR.send.sizeOf_spec]
          omega
        exact toCoind_regular cont)
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
      have hreg := toCoindBranches_regular_aux bs (fun cont hsz => by
        have hsz' : sizeOf cont < sizeOf (LocalTypeR.recv p bs) := by
          simp only [LocalTypeR.recv.sizeOf_spec]
          omega
        exact toCoind_regular cont)
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
termination_by t => sizeOf t

end RumpsteakV2.Coinductive
