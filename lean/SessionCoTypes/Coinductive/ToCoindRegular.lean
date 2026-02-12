import Mathlib
import SessionCoTypes.Coinductive.LocalTypeC
import SessionCoTypes.Coinductive.Bridge
import SessionCoTypes.Coinductive.RegularityLemmas
import SessionTypes.LocalTypeR

set_option linter.dupNamespace false


/-
The Problem. The toCoind function embeds inductive types into coinductive types.
We need to prove that the result is always regular (has finitely many reachable
states), which is necessary for round-tripping via toInductive.

The difficulty is that the proof must work for arbitrary inductive types,
including those with deeply nested branches. We use structural induction
and the regular_of_children lemma.

Solution Structure.
1. Prove toCoindBranches preserves regularity for all branch continuations
2. Prove toCoind_regular by structural induction on LocalTypeR
3. For send/recv cases, use regular_of_children with the branches lemma
-/

namespace SessionCoTypes.Coinductive

open SessionTypes.LocalTypeR

/-! ## Branch Regularity -/

/-- All continuations in toCoindBranches are regular if the source types are. -/
private def toCoindBranches_regular_aux :
    (bs : List BranchR) →
    (hrec : ∀ cont : LocalTypeR, sizeOf cont < sizeOf bs → Regular (toCoind cont)) →
    ∀ i : Fin (toCoindBranches bs).length, Regular ((toCoindBranches bs).get i).2
  | [], _, i => by
      exact (Nat.not_lt_zero _ i.2).elim
  | head :: tail, hrec, i => by
      rcases i with ⟨idx, hidx⟩
      cases idx with
      | zero =>
          have hsz : sizeOf head.2.2 < sizeOf (head :: tail) := by
            cases head with
            | mk lbl rest =>
                cases rest with
                | mk ty cont =>
                    simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
                    omega
          simpa [toCoindBranches] using hrec head.2.2 hsz
      | succ idx' =>
          have htail_lt : sizeOf tail < sizeOf (head :: tail) := by
            simp only [List.cons.sizeOf_spec]
            omega
          have htail_rec : ∀ cont, sizeOf cont < sizeOf tail → Regular (toCoind cont) :=
            fun cont hcont => hrec cont (Nat.lt_trans hcont htail_lt)
          let iTail : Fin (toCoindBranches tail).length := ⟨idx', by
            simpa [toCoindBranches] using hidx⟩
          simpa [toCoindBranches, iTail] using toCoindBranches_regular_aux tail htail_rec iTail

/-! ## Main Regularity Theorem -/

/-- Embedding an inductive type always produces a regular coinductive type.
    This is the key lemma enabling round-trip conversion. -/
def toCoind_regular : ∀ t : LocalTypeR, Regular (toCoind t)
  | .end => by apply regular_of_children; intro i; cases i
  | .var x => by apply regular_of_children; intro i; cases i
  | .mu x body => by
      apply regular_of_children
      intro i; cases i
      simpa [toCoind] using toCoind_regular body
  | .send p bs => by
      have hreg := toCoindBranches_regular_aux bs (fun cont hsz => by
        have hsz' : sizeOf cont < sizeOf (LocalTypeR.send p bs) := by
          simp only [LocalTypeR.send.sizeOf_spec]; omega
        exact toCoind_regular cont)
      apply regular_of_children
      intro i
      simpa using hreg (castFin (by simp) i)
  | .recv p bs => by
      have hreg := toCoindBranches_regular_aux bs (fun cont hsz => by
        have hsz' : sizeOf cont < sizeOf (LocalTypeR.recv p bs) := by
          simp only [LocalTypeR.recv.sizeOf_spec]; omega
        exact toCoind_regular cont)
      apply regular_of_children
      intro i
      simpa using hreg (castFin (by simp) i)
termination_by t => sizeOf t

end SessionCoTypes.Coinductive
