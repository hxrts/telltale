import Rumpsteak.Proofs.Projection.Merging.Associative.Helpers

/-! # Rumpsteak.Proofs.Projection.Merging.Associative.SendSorted

Associativity proof for sorted send-branch merging.

## Overview

This module proves that `mergeSendSorted` is associative when all continuations
satisfy the associativity property. This is a key lemma for the main
`merge_associative` theorem.
-/

namespace Rumpsteak.Proofs.Projection.Merging

open Rumpsteak.Protocol.LocalTypeR
open Rumpsteak.Protocol.GlobalType (Label)
open Rumpsteak.Protocol.ProjectionR

attribute [local instance] boolRelToRel

/-! ## MergeAssocAt predicate -/

/-- Associativity property for a fixed first argument. -/
def MergeAssocAt (t : LocalTypeR) : Prop :=
  ∀ u v,
    (LocalTypeR.merge t u).bind (fun m => LocalTypeR.merge m v) =
    (LocalTypeR.merge u v).bind (fun m => LocalTypeR.merge t m)

/-! ## Option bind helpers -/

theorem option_bind_comm {α β γ : Type} (oa : Option α) (ob : Option β) (f : α → β → Option γ) :
    oa.bind (fun a => ob.bind (fun b => f a b)) =
    ob.bind (fun b => oa.bind (fun a => f a b)) := by
  cases oa <;> cases ob <;> rfl

/-! ## Send sorted merge associativity -/

theorem mergeSendSorted_assoc :
    ∀ (bs1 bs2 bs3 : List (Label × LocalTypeR)),
      AllBranches MergeAssocAt bs1 →
      (LocalTypeR.mergeSendSorted bs1 bs2).bind (fun m12 => LocalTypeR.mergeSendSorted m12 bs3) =
      (LocalTypeR.mergeSendSorted bs2 bs3).bind (fun m23 => LocalTypeR.mergeSendSorted bs1 m23) := by
  intro bs1 bs2 bs3 ih
  induction bs1 generalizing bs2 bs3 with
  | nil =>
    cases bs2 with
    | nil =>
      cases bs3 <;> simp [LocalTypeR.mergeSendSorted]
    | cons head2 tail2 =>
      cases bs3 with
      | nil =>
        simp [LocalTypeR.mergeSendSorted]
      | cons head3 tail3 =>
        cases h23 : LocalTypeR.mergeSendSorted (head2 :: tail2) (head3 :: tail3) with
        | none =>
          simp [LocalTypeR.mergeSendSorted, h23]
        | some m23 =>
          have hFst :
              m23.map Prod.fst = (head2 :: tail2).map Prod.fst :=
            mergeSendSorted_map_fst (bs1 := head2 :: tail2) (bs2 := head3 :: tail3) (rest := m23) h23
          cases m23 with
          | nil =>
            cases (by simpa using hFst : False)
          | cons _ _ =>
            simp [LocalTypeR.mergeSendSorted, h23]
  | cons head tail ihTail =>
    cases bs2 with
    | nil =>
      cases bs3 <;> simp [LocalTypeR.mergeSendSorted]
    | cons head2 tail2 =>
      cases bs3 with
      | nil =>
        cases h12 : LocalTypeR.mergeSendSorted (head :: tail) (head2 :: tail2) with
        | none =>
          simp [LocalTypeR.mergeSendSorted, h12]
        | some a =>
          have hFst :
              a.map Prod.fst = (head :: tail).map Prod.fst :=
            mergeSendSorted_map_fst (bs1 := head :: tail) (bs2 := head2 :: tail2) (rest := a) h12
          cases a with
          | nil =>
            cases (by simpa using hFst : False)
          | cons _ _ =>
            simp [LocalTypeR.mergeSendSorted, h12]
      | cons head3 tail3 =>
        cases head with
        | mk l1 c1 =>
          cases head2 with
          | mk l2 c2 =>
            cases head3 with
            | mk l3 c3 =>
              have ihHead : MergeAssocAt c1 := ih (l1, c1) (by simp)
              have ihTailBranches : AllBranches MergeAssocAt tail := by
                intro b hb
                exact ih b (by simp [hb])
              by_cases h12 : l1 = l2
              · subst h12
                by_cases h13 : l1 = l3
                · subst h13
                  have swapL :
                      ∀ merged12,
                        (LocalTypeR.mergeSendSorted tail tail2).bind (fun rest12 =>
                            (LocalTypeR.merge merged12 c3).bind (fun merged123 =>
                                (LocalTypeR.mergeSendSorted rest12 tail3).bind (fun rest123 =>
                                    some ((l1, merged123) :: rest123)))) =
                          (LocalTypeR.merge merged12 c3).bind (fun merged123 =>
                            (LocalTypeR.mergeSendSorted tail tail2).bind (fun rest12 =>
                                (LocalTypeR.mergeSendSorted rest12 tail3).bind (fun rest123 =>
                                    some ((l1, merged123) :: rest123)))) := by
                    intro merged12
                    simpa using
                      (option_bind_comm
                        (oa := LocalTypeR.mergeSendSorted tail tail2)
                        (ob := LocalTypeR.merge merged12 c3)
                        (f := fun rest12 merged123 =>
                          (LocalTypeR.mergeSendSorted rest12 tail3).bind (fun rest123 =>
                            some ((l1, merged123) :: rest123))))

                  have swapR :
                      ∀ merged23,
                        (LocalTypeR.mergeSendSorted tail2 tail3).bind (fun rest23 =>
                            (LocalTypeR.merge c1 merged23).bind (fun merged123 =>
                                (LocalTypeR.mergeSendSorted tail rest23).bind (fun rest123 =>
                                    some ((l1, merged123) :: rest123)))) =
                          (LocalTypeR.merge c1 merged23).bind (fun merged123 =>
                            (LocalTypeR.mergeSendSorted tail2 tail3).bind (fun rest23 =>
                                (LocalTypeR.mergeSendSorted tail rest23).bind (fun rest123 =>
                                    some ((l1, merged123) :: rest123)))) := by
                    intro merged23
                    simpa using
                      (option_bind_comm
                        (oa := LocalTypeR.mergeSendSorted tail2 tail3)
                        (ob := LocalTypeR.merge c1 merged23)
                        (f := fun rest23 merged123 =>
                          (LocalTypeR.mergeSendSorted tail rest23).bind (fun rest123 =>
                            some ((l1, merged123) :: rest123))))

                  let head123Left :=
                    (LocalTypeR.merge c1 c2).bind (fun m12 => LocalTypeR.merge m12 c3)
                  let tail123Left :=
                    (LocalTypeR.mergeSendSorted tail tail2).bind (fun m12 => LocalTypeR.mergeSendSorted m12 tail3)
                  let head123Right :=
                    (LocalTypeR.merge c2 c3).bind (fun m23 => LocalTypeR.merge c1 m23)
                  let tail123Right :=
                    (LocalTypeR.mergeSendSorted tail2 tail3).bind (fun m23 => LocalTypeR.mergeSendSorted tail m23)

                  have hTailEq : tail123Left = tail123Right :=
                    ihTail (bs2 := tail2) (bs3 := tail3) ihTailBranches
                  have hHeadEq : head123Left = head123Right := by
                    simpa [head123Left, head123Right, MergeAssocAt] using ihHead c2 c3

                  have hLhs :
                      (LocalTypeR.mergeSendSorted ((l1, c1) :: tail) ((l1, c2) :: tail2)).bind
                          (fun m12 => LocalTypeR.mergeSendSorted m12 ((l1, c3) :: tail3)) =
                        head123Left.bind (fun merged123 =>
                          tail123Left.bind (fun rest123 => some ((l1, merged123) :: rest123))) := by
                      simp [LocalTypeR.mergeSendSorted]
                      rw [Option.bind_assoc]
                      simp [Option.bind_assoc, LocalTypeR.mergeSendSorted]
                      simp [swapL]
                      rw [← Option.bind_assoc]
                      simp [head123Left, tail123Left, Option.bind_assoc]

                  have hRhs :
                      (LocalTypeR.mergeSendSorted ((l1, c2) :: tail2) ((l1, c3) :: tail3)).bind
                          (fun m23 => LocalTypeR.mergeSendSorted ((l1, c1) :: tail) m23) =
                        head123Right.bind (fun merged123 =>
                          tail123Right.bind (fun rest123 => some ((l1, merged123) :: rest123))) := by
                      simp [LocalTypeR.mergeSendSorted]
                      rw [Option.bind_assoc]
                      simp [Option.bind_assoc, LocalTypeR.mergeSendSorted]
                      simp [swapR]
                      rw [← Option.bind_assoc]
                      simp [head123Right, tail123Right, Option.bind_assoc]

                  simpa [hLhs, hRhs, hHeadEq, hTailEq]
                · have hRhsNone : LocalTypeR.mergeSendSorted ((l1, c2) :: tail2) ((l3, c3) :: tail3) = none := by
                    simp [LocalTypeR.mergeSendSorted, h13]
                  cases h12' : LocalTypeR.mergeSendSorted ((l1, c1) :: tail) ((l1, c2) :: tail2) with
                  | none =>
                    simp [LocalTypeR.mergeSendSorted, h12', hRhsNone]
                  | some val =>
                    have hFst : val.map Prod.fst = ((l1, c1) :: tail).map Prod.fst :=
                      mergeSendSorted_map_fst (bs1 := (l1, c1) :: tail) (bs2 := (l1, c2) :: tail2) (rest := val) h12'
                    cases val with
                    | nil =>
                      cases (by simpa using hFst : False)
                    | cons vHead vTail =>
                      have hv : vHead.1 = l1 := by
                        have hHeadOpt := congrArg List.head? hFst
                        simpa using hHeadOpt
                      have hv' : ¬vHead.1 = l3 := by
                        intro hEq
                        exact h13 (hv ▸ hEq)
                      have hSecond : LocalTypeR.mergeSendSorted (vHead :: vTail) ((l3, c3) :: tail3) = none := by
                        cases vHead with
                        | mk l t =>
                          have hv'' : ¬l = l3 := by
                            simpa using hv'
                          simp [LocalTypeR.mergeSendSorted, hv'']
                      simp [h12', hRhsNone, hSecond]
              · have hLhsNone : LocalTypeR.mergeSendSorted ((l1, c1) :: tail) ((l2, c2) :: tail2) = none := by
                  simp [LocalTypeR.mergeSendSorted, h12]
                cases h23 : LocalTypeR.mergeSendSorted ((l2, c2) :: tail2) ((l3, c3) :: tail3) with
                | none =>
                  simp [hLhsNone, h23]
                | some m23 =>
                  have hFst : m23.map Prod.fst = ((l2, c2) :: tail2).map Prod.fst :=
                    mergeSendSorted_map_fst (bs1 := (l2, c2) :: tail2) (bs2 := (l3, c3) :: tail3) (rest := m23) h23
                  cases m23 with
                  | nil =>
                    cases (by simpa using hFst : False)
                  | cons mHead mTail =>
                    have hm : mHead.1 = l2 := by
                      have hHeadOpt := congrArg List.head? hFst
                      simpa using hHeadOpt
                    have hm' : ¬l1 = mHead.1 := by
                      intro hEq
                      exact h12 (hEq.trans hm)
                    have hSecond : LocalTypeR.mergeSendSorted ((l1, c1) :: tail) (mHead :: mTail) = none := by
                      cases mHead with
                      | mk l t =>
                        have hm'' : ¬l1 = l := by
                          simpa using hm'
                        simp [LocalTypeR.mergeSendSorted, hm'']
                    simp [hLhsNone, h23, hSecond]

end Rumpsteak.Proofs.Projection.Merging
