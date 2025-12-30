import Rumpsteak.Proofs.Projection.Merging.Associative.SendSorted

/-! # Rumpsteak.Proofs.Projection.Merging.Associative.RecvSorted

Associativity proof for sorted recv-branch merging.

## Overview

This module proves that `mergeRecvSorted` is associative when all continuations
satisfy the associativity property. This is a key lemma for the main
`merge_associative` theorem.
-/

namespace Rumpsteak.Proofs.Projection.Merging

open Rumpsteak.Protocol.LocalTypeR
open Rumpsteak.Protocol.GlobalType (Label)
open Rumpsteak.Protocol.ProjectionR

attribute [local instance] boolRelToRel

/-! ## Recv sorted merge associativity -/

theorem mergeRecvSorted_assoc
    (bs1 bs2 bs3 : List (Label × LocalTypeR))
    (ih : AllBranches MergeAssocAt bs1) :
    (LocalTypeR.mergeRecvSorted bs1 bs2).bind (fun m12 => LocalTypeR.mergeRecvSorted m12 bs3) =
    (LocalTypeR.mergeRecvSorted bs2 bs3).bind (fun m23 => LocalTypeR.mergeRecvSorted bs1 m23) := by
  cases bs1 with
  | nil =>
    simp [LocalTypeR.mergeRecvSorted]
  | cons head1 tail1 =>
    cases bs2 with
    | nil =>
      simp [LocalTypeR.mergeRecvSorted]
    | cons head2 tail2 =>
      cases bs3 with
      | nil =>
        simp [LocalTypeR.mergeRecvSorted]
      | cons head3 tail3 =>
        cases head1 with
        | mk l1 c1 =>
          cases head2 with
          | mk l2 c2 =>
            cases head3 with
            | mk l3 c3 =>
              have ihHead : MergeAssocAt c1 := ih (l1, c1) (by simp)
              have ihTail1 : AllBranches MergeAssocAt tail1 := by
                intro b hb
                exact ih b (by simp [hb])

              by_cases h12 : l1.name < l2.name
              · have h21 : ¬ l2.name < l1.name := String.lt_asymm h12
                by_cases h13 : l1.name < l3.name
                · have h31 : ¬ l3.name < l1.name := String.lt_asymm h13
                  have hRec :=
                    mergeRecvSorted_assoc tail1 ((l2, c2) :: tail2) ((l3, c3) :: tail3) ihTail1
                  have hRec' :=
                    congrArg
                      (fun x => x.bind (fun rest => some ((l1, c1) :: rest)))
                      hRec

                  by_cases h23 : l2.name < l3.name
                  · have h32 : ¬ l3.name < l2.name := String.lt_asymm h23
                    simpa [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, h23, h32, Option.bind_assoc] using hRec'
                  · by_cases h32 : l3.name < l2.name
                    · simpa [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, h23, h32, Option.bind_assoc] using hRec'
                    · by_cases hEq23 : l2 = l3
                      · subst hEq23
                        simpa [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, h23, h32, Option.bind_assoc] using hRec'
                      · have hEq23' : l3 ≠ l2 := fun h => hEq23 h.symm
                        simpa [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, h23, h32, hEq23, hEq23', Option.bind_assoc] using hRec'
                · by_cases h31 : l3.name < l1.name
                  · have hRec :=
                      mergeRecvSorted_assoc ((l1, c1) :: tail1) ((l2, c2) :: tail2) tail3 ih
                    have h32 : l3.name < l2.name := Std.lt_of_lt_of_le h31 (Std.le_of_lt h12)
                    have h23 : ¬ l2.name < l3.name := String.lt_asymm h32
                    have hRec' :=
                      congrArg
                        (fun x => x.bind (fun rest => some ((l3, c3) :: rest)))
                        hRec
                    simpa [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, h32, h23, Option.bind_assoc] using hRec'
                  · have h32 : l3.name < l2.name := by
                      have hLe : l3.name ≤ l1.name := by
                        have ht : l3.name ≤ l1.name ∨ l1.name ≤ l3.name :=
                          Std.le_total (a := l3.name) (b := l1.name)
                        cases ht with
                        | inl hle => exact hle
                        | inr hle =>
                          by_cases hEq : l1.name = l3.name
                          · simpa [hEq] using (le_rfl : l3.name ≤ l3.name)
                          · have : l1.name < l3.name := Std.lt_of_le_of_ne hle hEq
                            exact False.elim (h13 this)
                      exact Std.lt_of_le_of_lt hLe h12
                    have h23 : ¬ l2.name < l3.name := String.lt_asymm h32
                    by_cases hEq13 : l1 = l3
                    · subst hEq13
                      cases hCont : LocalTypeR.merge c1 c3 with
                      | none =>
                        simp [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, h32, h23, hCont, Option.bind_assoc]
                      | some merged13 =>
                        have hRec :=
                          mergeRecvSorted_assoc tail1 ((l2, c2) :: tail2) tail3 ihTail1
                        have hRec' :=
                          congrArg
                            (fun x => x.bind (fun rest => some ((l1, merged13) :: rest)))
                            hRec
                        simpa [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, h32, h23, hCont, Option.bind_assoc] using hRec'
                    · have hEq13' : l3 ≠ l1 := fun h => hEq13 h.symm
                      simp [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, h32, h23, hEq13, hEq13', Option.bind_assoc]
              · by_cases h21 : l2.name < l1.name
                · by_cases h23 : l2.name < l3.name
                  · have hRec :=
                      mergeRecvSorted_assoc ((l1, c1) :: tail1) tail2 ((l3, c3) :: tail3) ih
                    have h32 : ¬ l3.name < l2.name := String.lt_asymm h23
                    have hRec' :=
                      congrArg
                        (fun x => x.bind (fun rest => some ((l2, c2) :: rest)))
                        hRec
                    simpa [LocalTypeR.mergeRecvSorted, h12, h21, h23, h32, Option.bind_assoc] using hRec'
                  · by_cases h32 : l3.name < l2.name
                    · have hRec :=
                        mergeRecvSorted_assoc ((l1, c1) :: tail1) ((l2, c2) :: tail2) tail3 ih
                      have h31 : l3.name < l1.name := Std.lt_of_lt_of_le h32 (Std.le_of_lt h21)
                      have h13 : ¬ l1.name < l3.name := String.lt_asymm h31
                      have hRec' :=
                        congrArg
                          (fun x => x.bind (fun rest => some ((l3, c3) :: rest)))
                          hRec
                      simpa [LocalTypeR.mergeRecvSorted, h12, h21, h23, h32, h31, h13, Option.bind_assoc] using hRec'
                    · have h31 : l3.name < l1.name := by
                        have hLe : l3.name ≤ l2.name := by
                          have ht : l3.name ≤ l2.name ∨ l2.name ≤ l3.name :=
                            Std.le_total (a := l3.name) (b := l2.name)
                          cases ht with
                          | inl hle => exact hle
                          | inr hle =>
                            by_cases hEq : l2.name = l3.name
                            · simpa [hEq] using (le_rfl : l3.name ≤ l3.name)
                            · have : l2.name < l3.name := Std.lt_of_le_of_ne hle hEq
                              exact False.elim (h23 this)
                        exact Std.lt_of_le_of_lt hLe h21
                      have h13 : ¬ l1.name < l3.name := String.lt_asymm h31
                      by_cases hEq23 : l2 = l3
                      · subst hEq23
                        cases hCont : LocalTypeR.merge c2 c3 with
                        | none =>
                          simp [LocalTypeR.mergeRecvSorted, h12, h21, h23, h32, h31, h13, hCont, Option.bind_assoc]
                        | some merged23 =>
                          have hRec :=
                            mergeRecvSorted_assoc ((l1, c1) :: tail1) tail2 tail3 ih
                          have hRec' :=
                            congrArg
                              (fun x => x.bind (fun rest => some ((l2, merged23) :: rest)))
                              hRec
                          simpa [LocalTypeR.mergeRecvSorted, h12, h21, h23, h32, h31, h13, hCont, Option.bind_assoc] using hRec'
                      · have hEq23' : l3 ≠ l2 := fun h => hEq23 h.symm
                        simp [LocalTypeR.mergeRecvSorted, h12, h21, h23, h32, h31, h13, hEq23, hEq23', Option.bind_assoc]
                · by_cases hEq12 : l1 = l2
                  · subst hEq12
                    by_cases h13 : l1.name < l3.name
                    · have h31 : ¬ l3.name < l1.name := String.lt_asymm h13
                      cases hCont : LocalTypeR.merge c1 c2 with
                      | none =>
                        simp [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, hCont, Option.bind_assoc]
                      | some merged12 =>
                        have hRec := mergeRecvSorted_assoc tail1 tail2 ((l3, c3) :: tail3) ihTail1
                        have hRec' :=
                          congrArg
                            (fun x => x.bind (fun rest => some ((l1, merged12) :: rest)))
                            hRec
                        simpa [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, hCont, Option.bind_assoc] using hRec'
                    · by_cases h31 : l3.name < l1.name
                      · have hRec :=
                          mergeRecvSorted_assoc ((l1, c1) :: tail1) ((l1, c2) :: tail2) tail3 ih
                        have hRec' :=
                          congrArg
                            (fun x => x.bind (fun rest => some ((l3, c3) :: rest)))
                            hRec
                        have h32 : l3.name < l2.name := h31
                        have h23 : ¬ l2.name < l3.name := String.lt_asymm h32
                        simpa [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, h23, h32, Option.bind_assoc] using hRec'
                      · by_cases hEq13 : l1 = l3
                        · subst hEq13
                          cases hCont12 : LocalTypeR.merge c1 c2 with
                          | none =>
                            simp [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, hCont12, Option.bind_assoc]
                          | some merged12 =>
                            cases hCont23 : LocalTypeR.merge c2 c3 with
                            | none =>
                              simp [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, hCont12, hCont23, Option.bind_assoc]
                            | some merged23 =>
                              have hContAssoc :
                                  (LocalTypeR.merge c1 c2).bind (fun m12 => LocalTypeR.merge m12 c3) =
                                  (LocalTypeR.merge c2 c3).bind (fun m23 => LocalTypeR.merge c1 m23) := by
                                exact ihHead c2 c3
                              have hRec := mergeRecvSorted_assoc tail1 tail2 tail3 ihTail1
                              cases hMerge123 : (LocalTypeR.merge c1 c2).bind (fun m12 => LocalTypeR.merge m12 c3) with
                              | none =>
                                rw [hContAssoc] at hMerge123
                                simp only [hCont12, hCont23, Option.some_bind] at hMerge123 ⊢
                                simp [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, hMerge123, Option.bind_assoc]
                              | some merged123 =>
                                rw [hContAssoc] at hMerge123
                                simp only [hCont12, hCont23, Option.some_bind] at hMerge123 ⊢
                                have hRec' :=
                                  congrArg
                                    (fun x => x.bind (fun rest => some ((l1, merged123) :: rest)))
                                    hRec
                                simp only [hCont12, hCont23, Option.some_bind, hMerge123] at hRec' ⊢
                                simpa [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, Option.bind_assoc] using hRec'
                        · have hEq13' : l3 ≠ l1 := fun h => hEq13 h.symm
                          simp [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, hEq13, hEq13', Option.bind_assoc]
                  · have hEq12' : l2 ≠ l1 := fun h => hEq12 h.symm
                    simp [LocalTypeR.mergeRecvSorted, h12, h21, hEq12, hEq12', Option.bind_assoc]
termination_by sizeOf bs1 + sizeOf bs2 + sizeOf bs3
decreasing_by
  all_goals
    simp_wf
    first
      | apply Nat.add_lt_add_of_lt_of_le
        apply Nat.add_lt_add_of_lt_of_le
        exact sizeOf_tail_lt_cons (l1, c1) tail1
        all_goals exact Nat.le_refl _
      | apply Nat.add_lt_add_of_le_of_lt
        apply Nat.add_lt_add_of_le_of_lt
        exact Nat.le_refl _
        exact sizeOf_tail_lt_cons (l2, c2) tail2
        exact Nat.le_refl _
      | apply Nat.add_lt_add_of_le_of_lt
        exact Nat.le_refl _
        exact sizeOf_tail_lt_cons (l3, c3) tail3
      | apply Nat.lt_of_lt_of_le
        · apply Nat.add_lt_add_of_lt_of_le
          apply Nat.add_lt_add_of_lt_of_le
          exact sizeOf_tail_lt_cons (l1, c1) tail1
          exact Nat.le_refl _
          exact Nat.le_refl _
        · exact Nat.le_refl _
      | apply Nat.add_lt_add_of_lt_of_le
        apply Nat.add_lt_add
        exact sizeOf_tail_lt_cons (l1, c1) tail1
        exact sizeOf_tail_lt_cons (l2, c2) tail2
        exact Nat.le_refl _
      | apply Nat.add_lt_add_of_lt_of_lt
        apply Nat.add_lt_add_of_lt_of_le
        exact sizeOf_tail_lt_cons (l1, c1) tail1
        exact Nat.le_refl _
        exact sizeOf_tail_lt_cons (l3, c3) tail3
      | apply Nat.add_lt_add_of_le_of_lt
        apply Nat.add_lt_add_of_le_of_lt
        exact Nat.le_refl _
        exact sizeOf_tail_lt_cons (l2, c2) tail2
        exact sizeOf_tail_lt_cons (l3, c3) tail3
      | apply Nat.add_lt_add
        apply Nat.add_lt_add
        exact sizeOf_tail_lt_cons (l1, c1) tail1
        exact sizeOf_tail_lt_cons (l2, c2) tail2
        exact sizeOf_tail_lt_cons (l3, c3) tail3
      | omega

end Rumpsteak.Proofs.Projection.Merging
