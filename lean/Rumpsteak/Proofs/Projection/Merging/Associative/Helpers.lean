import Rumpsteak.Proofs.Projection.Merging.Basic
import Rumpsteak.Proofs.Projection.Merging.SortLemmas

/-! # Rumpsteak.Proofs.Projection.Merging.Associative.Helpers

Helper lemmas for the merge associativity proof.

## Overview

This module provides helper lemmas about sorted branch merging that preserve
structural properties needed for the associativity proof:
- `mergeSendSorted_map_fst`: Send merge preserves first-component ordering
- `mergeRecvSorted_mem_fst`: Recv merge result labels come from inputs
- `mergeRecvSorted_pairwise`: Recv merge preserves pairwise ordering
- `mergeSendSorted_pairwise`: Send merge preserves pairwise ordering
-/

namespace Rumpsteak.Proofs.Projection.Merging

open Rumpsteak.Protocol.LocalTypeR
open Rumpsteak.Protocol.GlobalType (Label)
open Rumpsteak.Protocol.ProjectionR

attribute [local instance] boolRelToRel

/-! ## Send merge first-component lemma -/

theorem mergeSendSorted_map_fst :
    ∀ {bs1 bs2 rest : List (Label × LocalTypeR)},
      LocalTypeR.mergeSendSorted bs1 bs2 = some rest →
      rest.map Prod.fst = bs1.map Prod.fst := by
  intro bs1 bs2 rest h
  induction bs1 generalizing bs2 rest with
  | nil =>
    cases bs2 with
    | nil =>
      have : rest = [] := by
        simpa [LocalTypeR.mergeSendSorted] using h
      simp [this]
    | cons head2 tail2 =>
      cases (by simpa [LocalTypeR.mergeSendSorted] using h : False)
  | cons head tail ih =>
    cases bs2 with
    | nil =>
      cases (by simpa [LocalTypeR.mergeSendSorted] using h : False)
    | cons head2 tail2 =>
      cases head with
      | mk l1 c1 =>
        cases head2 with
        | mk l2 c2 =>
          by_cases hLabel : l1 = l2
          · subst hLabel
            cases hCont : LocalTypeR.merge c1 c2 with
            | none =>
              cases (by simpa [LocalTypeR.mergeSendSorted, hCont] using h : False)
            | some mergedCont =>
              cases hRest : LocalTypeR.mergeSendSorted tail tail2 with
              | none =>
                cases (by simpa [LocalTypeR.mergeSendSorted, hCont, hRest] using h : False)
              | some restTail =>
                have hEq : (l1, mergedCont) :: restTail = rest := by
                  simpa [LocalTypeR.mergeSendSorted, hCont, hRest] using h
                have ihEq : restTail.map Prod.fst = tail.map Prod.fst :=
                  ih (bs2 := tail2) (rest := restTail) hRest
                rw [← hEq]
                simp [ihEq]
          · cases (by simpa [LocalTypeR.mergeSendSorted, hLabel] using h : False)

/-! ## Recv merge membership lemma -/

theorem mergeRecvSorted_mem_fst
    {bs1 bs2 rest : List (Label × LocalTypeR)}
    (h : LocalTypeR.mergeRecvSorted bs1 bs2 = some rest) :
    ∀ l, l ∈ rest.map Prod.fst → l ∈ bs1.map Prod.fst ∨ l ∈ bs2.map Prod.fst := by
  intro l hl
  rcases List.mem_map.1 hl with ⟨b, hb, hbEq⟩
  have hb' : b.1 ∈ bs1.map Prod.fst ∨ b.1 ∈ bs2.map Prod.fst := by
    cases hbs1 : bs1 with
    | nil =>
      have hEq : bs2 = rest := by
        simpa [hbs1, LocalTypeR.mergeRecvSorted] using h
      right
      have : b ∈ bs2 := by
        simpa [hEq] using hb
      exact List.mem_map_of_mem (f := Prod.fst) this
    | cons head1 tail1 =>
      cases hbs2 : bs2 with
      | nil =>
        have hEq : head1 :: tail1 = rest := by
          simpa [hbs1, hbs2, LocalTypeR.mergeRecvSorted] using h
        left
        have : b ∈ head1 :: tail1 := by
          simpa [hEq] using hb
        exact List.mem_map_of_mem (f := Prod.fst) this
      | cons head2 tail2 =>
        cases head1 with
        | mk l1 c1 =>
          cases head2 with
          | mk l2 c2 =>
            by_cases h12 : l1.name < l2.name
            · cases hRest : LocalTypeR.mergeRecvSorted tail1 ((l2, c2) :: tail2) with
              | none =>
                cases (by simpa [hbs1, hbs2, LocalTypeR.mergeRecvSorted, h12, hRest] using h : False)
              | some restTail =>
                have hEq : (l1, c1) :: restTail = rest := by
                  simpa [hbs1, hbs2, LocalTypeR.mergeRecvSorted, h12, hRest] using h
                have hb'' : b ∈ (l1, c1) :: restTail := by
                  simpa [hEq] using hb
                cases (List.mem_cons.1 hb'') with
                | inl hbHead =>
                  left
                  subst hbHead
                  simp
                | inr hbTail =>
                  have hbFst : b.1 ∈ restTail.map Prod.fst :=
                    List.mem_map_of_mem (f := Prod.fst) hbTail
                  have ih' :
                      b.1 ∈ tail1.map Prod.fst ∨ b.1 ∈ ((l2, c2) :: tail2).map Prod.fst :=
                    mergeRecvSorted_mem_fst (bs1 := tail1) (bs2 := (l2, c2) :: tail2) (rest := restTail) hRest b.1 hbFst
                  cases ih' with
                  | inl hInTail1 =>
                    left
                    exact List.mem_cons_of_mem _ hInTail1
                  | inr hInBs2 =>
                    right
                    simpa using hInBs2
            · by_cases h21 : l2.name < l1.name
              · cases hRest : LocalTypeR.mergeRecvSorted ((l1, c1) :: tail1) tail2 with
                | none =>
                  cases (by
                    simpa [hbs1, hbs2, LocalTypeR.mergeRecvSorted, h12, h21, hRest] using h : False)
                | some restTail =>
                  have hEq : (l2, c2) :: restTail = rest := by
                    simpa [hbs1, hbs2, LocalTypeR.mergeRecvSorted, h12, h21, hRest] using h
                  have hb'' : b ∈ (l2, c2) :: restTail := by
                    simpa [hEq] using hb
                  cases (List.mem_cons.1 hb'') with
                  | inl hbHead =>
                    right
                    subst hbHead
                    simp
                  | inr hbTail =>
                    have hbFst : b.1 ∈ restTail.map Prod.fst :=
                      List.mem_map_of_mem (f := Prod.fst) hbTail
                    have ih' :
                        b.1 ∈ ((l1, c1) :: tail1).map Prod.fst ∨ b.1 ∈ tail2.map Prod.fst :=
                      mergeRecvSorted_mem_fst (bs1 := (l1, c1) :: tail1) (bs2 := tail2) (rest := restTail) hRest b.1 hbFst
                    cases ih' with
                    | inl hInBs1 =>
                      left
                      simpa using hInBs1
                    | inr hInTail2 =>
                      right
                      exact List.mem_cons_of_mem _ hInTail2
              · by_cases hEqLab : l1 = l2
                · subst hEqLab
                  cases hCont : LocalTypeR.merge c1 c2 with
                  | none =>
                    cases (by
                      simpa [hbs1, hbs2, LocalTypeR.mergeRecvSorted, h12, h21, hCont] using h : False)
                  | some mergedCont =>
                    cases hRest : LocalTypeR.mergeRecvSorted tail1 tail2 with
                    | none =>
                      cases (by
                        simpa [hbs1, hbs2, LocalTypeR.mergeRecvSorted, h12, h21, hCont, hRest] using h : False)
                    | some restTail =>
                      have hEq : (l1, mergedCont) :: restTail = rest := by
                        simpa [hbs1, hbs2, LocalTypeR.mergeRecvSorted, h12, h21, hCont, hRest] using h
                      have hb'' : b ∈ (l1, mergedCont) :: restTail := by
                        simpa [hEq] using hb
                      cases (List.mem_cons.1 hb'') with
                      | inl hbHead =>
                        left
                        subst hbHead
                        simp
                      | inr hbTail =>
                        have hbFst : b.1 ∈ restTail.map Prod.fst :=
                          List.mem_map_of_mem (f := Prod.fst) hbTail
                        have ih' :
                            b.1 ∈ tail1.map Prod.fst ∨ b.1 ∈ tail2.map Prod.fst :=
                          mergeRecvSorted_mem_fst (bs1 := tail1) (bs2 := tail2) (rest := restTail) hRest b.1 hbFst
                        cases ih' with
                        | inl hInTail1 =>
                          left
                          exact List.mem_cons_of_mem _ hInTail1
                        | inr hInTail2 =>
                          right
                          exact List.mem_cons_of_mem _ hInTail2
                · cases (by simpa [hbs1, hbs2, LocalTypeR.mergeRecvSorted, h12, h21, hEqLab] using h : False)
  simpa [hbEq] using hb'
  termination_by bs1.length + bs2.length
  decreasing_by
    all_goals
      simp
      simp (config := { failIfUnchanged := false }) [hbs1, hbs2]
      try omega

/-! ## Recv merge pairwise lemma -/

theorem mergeRecvSorted_pairwise
    {bs1 bs2 rest : List (Label × LocalTypeR)}
    (hSorted1 : bs1.Pairwise LocalTypeR.branchLe)
    (hSorted2 : bs2.Pairwise LocalTypeR.branchLe)
    (h : LocalTypeR.mergeRecvSorted bs1 bs2 = some rest) :
    rest.Pairwise LocalTypeR.branchLe := by
  cases hbs1 : bs1 with
  | nil =>
    have hEq : bs2 = rest := by
      simpa [hbs1, LocalTypeR.mergeRecvSorted] using h
    simpa [hEq] using hSorted2
  | cons head1 tail1 =>
    cases hbs2 : bs2 with
    | nil =>
      have hEq : head1 :: tail1 = rest := by
        simpa [hbs1, hbs2, LocalTypeR.mergeRecvSorted] using h
      simpa [hbs1, hEq] using hSorted1
    | cons head2 tail2 =>
      have hCons : LocalTypeR.mergeRecvSorted (head1 :: tail1) (head2 :: tail2) = some rest := by
        simpa [hbs1, hbs2] using h
      have hSorted1' : (head1 :: tail1).Pairwise LocalTypeR.branchLe := by
        simpa [hbs1] using hSorted1
      have hSorted2' : (head2 :: tail2).Pairwise LocalTypeR.branchLe := by
        simpa [hbs2] using hSorted2
      cases head1 with
      | mk l1 c1 =>
        cases head2 with
        | mk l2 c2 =>
          cases hSorted1' with
          | cons hRel1 hTail1 =>
            cases hSorted2' with
            | cons hRel2 hTail2 =>
              by_cases h12 : l1.name < l2.name
              · have h21 : ¬ l2.name < l1.name := String.lt_asymm h12
                cases hRest : LocalTypeR.mergeRecvSorted tail1 ((l2, c2) :: tail2) with
                | none =>
                  cases (by
                    simpa [LocalTypeR.mergeRecvSorted, h12, h21, hRest] using hCons : False)
                | some restTail =>
                  have hEq : (l1, c1) :: restTail = rest := by
                    simpa [LocalTypeR.mergeRecvSorted, h12, h21, hRest] using hCons
                  have hTailPair : restTail.Pairwise LocalTypeR.branchLe :=
                    mergeRecvSorted_pairwise
                      (bs1 := tail1) (bs2 := (l2, c2) :: tail2) (rest := restTail)
                      hTail1 (List.Pairwise.cons hRel2 hTail2) hRest
                  have hHeadRel :
                      ∀ b ∈ restTail, LocalTypeR.branchLe (l1, c1) b = true := by
                    intro b hb
                    have hbFst : b.1 ∈ restTail.map Prod.fst :=
                      List.mem_map_of_mem (f := Prod.fst) hb
                    have hbIn :
                        b.1 ∈ tail1.map Prod.fst ∨ b.1 ∈ ((l2, c2) :: tail2).map Prod.fst :=
                      mergeRecvSorted_mem_fst (bs1 := tail1) (bs2 := (l2, c2) :: tail2) (rest := restTail)
                        hRest b.1 hbFst
                    have hLe12 : l1.name ≤ l2.name := Std.le_of_lt h12
                    cases hbIn with
                    | inl hbInTail1 =>
                      rcases List.mem_map.1 hbInTail1 with ⟨a, ha, haEq⟩
                      have hLe : l1.name ≤ a.1.name := by
                        have hLe' : LocalTypeR.branchLe (l1, c1) a = true := hRel1 a ha
                        simpa [LocalTypeR.branchLe] using hLe'
                      have hLe' : l1.name ≤ b.1.name := by
                        simpa [haEq] using hLe
                      simpa [LocalTypeR.branchLe, hLe']
                    | inr hbInBs2 =>
                      cases (List.mem_cons.1 hbInBs2) with
                      | inl hbHead =>
                        have hLe : l1.name ≤ b.1.name := by
                          simpa [hbHead] using hLe12
                        simpa [LocalTypeR.branchLe, hLe]
                      | inr hbInTail2 =>
                        rcases List.mem_map.1 hbInTail2 with ⟨a, ha, haEq⟩
                        have hLe2 : l2.name ≤ a.1.name := by
                          have hLe' : LocalTypeR.branchLe (l2, c2) a = true := hRel2 a ha
                          simpa [LocalTypeR.branchLe] using hLe'
                        have hLe : l1.name ≤ b.1.name := by
                          have : l1.name ≤ a.1.name := Std.le_trans hLe12 hLe2
                          simpa [haEq] using this
                        simpa [LocalTypeR.branchLe, hLe]
                  rw [← hEq]
                  exact List.Pairwise.cons hHeadRel hTailPair
              · by_cases h21 : l2.name < l1.name
                · cases hRest : LocalTypeR.mergeRecvSorted ((l1, c1) :: tail1) tail2 with
                  | none =>
                    cases (by
                        simpa [LocalTypeR.mergeRecvSorted, h12, h21, hRest] using hCons : False)
                  | some restTail =>
                    have hEq : (l2, c2) :: restTail = rest := by
                      simpa [LocalTypeR.mergeRecvSorted, h12, h21, hRest] using hCons
                    have hTailPair : restTail.Pairwise LocalTypeR.branchLe :=
                      mergeRecvSorted_pairwise
                        (bs1 := (l1, c1) :: tail1) (bs2 := tail2) (rest := restTail)
                        (List.Pairwise.cons hRel1 hTail1) hTail2 hRest
                    have hHeadRel :
                        ∀ b ∈ restTail, LocalTypeR.branchLe (l2, c2) b = true := by
                      intro b hb
                      have hbFst : b.1 ∈ restTail.map Prod.fst :=
                        List.mem_map_of_mem (f := Prod.fst) hb
                      have hbIn :
                          b.1 ∈ ((l1, c1) :: tail1).map Prod.fst ∨ b.1 ∈ tail2.map Prod.fst :=
                        mergeRecvSorted_mem_fst (bs1 := (l1, c1) :: tail1) (bs2 := tail2) (rest := restTail)
                          hRest b.1 hbFst
                      have hLe21 : l2.name ≤ l1.name := Std.le_of_lt h21
                      cases hbIn with
                      | inl hbInBs1 =>
                        cases (List.mem_cons.1 hbInBs1) with
                        | inl hbHead =>
                          have hLe : l2.name ≤ b.1.name := by
                            simpa [hbHead] using hLe21
                          simpa [LocalTypeR.branchLe, hLe]
                        | inr hbInTail1 =>
                          rcases List.mem_map.1 hbInTail1 with ⟨a, ha, haEq⟩
                          have hLe1 : l1.name ≤ a.1.name := by
                            have hLe' : LocalTypeR.branchLe (l1, c1) a = true := hRel1 a ha
                            simpa [LocalTypeR.branchLe] using hLe'
                          have hLe : l2.name ≤ b.1.name := by
                            have : l2.name ≤ a.1.name := Std.le_trans hLe21 hLe1
                            simpa [haEq] using this
                          simpa [LocalTypeR.branchLe, hLe]
                      | inr hbInTail2 =>
                        rcases List.mem_map.1 hbInTail2 with ⟨a, ha, haEq⟩
                        have hLe2 : l2.name ≤ a.1.name := by
                          have hLe' : LocalTypeR.branchLe (l2, c2) a = true := hRel2 a ha
                          simpa [LocalTypeR.branchLe] using hLe'
                        have hLe : l2.name ≤ b.1.name := by
                          simpa [haEq] using hLe2
                        simpa [LocalTypeR.branchLe, hLe]
                    rw [← hEq]
                    exact List.Pairwise.cons hHeadRel hTailPair
                · by_cases hEqLab : l1 = l2
                  · subst hEqLab
                    cases hCont : LocalTypeR.merge c1 c2 with
                    | none =>
                      cases (by
                          simpa [LocalTypeR.mergeRecvSorted, h12, h21, hCont] using hCons : False)
                    | some mergedCont =>
                      cases hRest : LocalTypeR.mergeRecvSorted tail1 tail2 with
                      | none =>
                        cases (by
                          simpa [LocalTypeR.mergeRecvSorted, h12, h21, hCont, hRest] using hCons : False)
                      | some restTail =>
                        have hEq : (l1, mergedCont) :: restTail = rest := by
                          simpa [LocalTypeR.mergeRecvSorted, h12, h21, hCont, hRest] using hCons
                        have hTailPair : restTail.Pairwise LocalTypeR.branchLe :=
                          mergeRecvSorted_pairwise
                            (bs1 := tail1) (bs2 := tail2) (rest := restTail) hTail1 hTail2 hRest
                        have hHeadRel :
                            ∀ b ∈ restTail, LocalTypeR.branchLe (l1, mergedCont) b = true := by
                          intro b hb
                          have hbFst : b.1 ∈ restTail.map Prod.fst :=
                            List.mem_map_of_mem (f := Prod.fst) hb
                          have hbIn :
                              b.1 ∈ tail1.map Prod.fst ∨ b.1 ∈ tail2.map Prod.fst :=
                            mergeRecvSorted_mem_fst (bs1 := tail1) (bs2 := tail2) (rest := restTail)
                              hRest b.1 hbFst
                          cases hbIn with
                          | inl hbInTail1 =>
                            rcases List.mem_map.1 hbInTail1 with ⟨a, ha, haEq⟩
                            have hLe : l1.name ≤ a.1.name := by
                              have hLe' : LocalTypeR.branchLe (l1, c1) a = true := hRel1 a ha
                              simpa [LocalTypeR.branchLe] using hLe'
                            have hLe' : l1.name ≤ b.1.name := by
                              simpa [haEq] using hLe
                            simpa [LocalTypeR.branchLe, hLe']
                          | inr hbInTail2 =>
                            rcases List.mem_map.1 hbInTail2 with ⟨a, ha, haEq⟩
                            have hLe : l1.name ≤ a.1.name := by
                              have hLe' : LocalTypeR.branchLe (l1, c2) a = true := by
                                simpa using hRel2 a ha
                              simpa [LocalTypeR.branchLe] using hLe'
                            have hLe' : l1.name ≤ b.1.name := by
                              simpa [haEq] using hLe
                            simpa [LocalTypeR.branchLe, hLe']
                        rw [← hEq]
                        exact List.Pairwise.cons hHeadRel hTailPair
                  · cases (by
                      simpa [LocalTypeR.mergeRecvSorted, h12, h21, hEqLab] using hCons : False)
  termination_by bs1.length + bs2.length
  decreasing_by
    all_goals
      simp
      simp (config := { failIfUnchanged := false }) [hbs1, hbs2]
      try omega

/-! ## Send merge pairwise lemma -/

theorem mergeSendSorted_pairwise
    {bs1 bs2 rest : List (Label × LocalTypeR)}
    (hSorted : bs1.Pairwise LocalTypeR.branchLe)
    (h : LocalTypeR.mergeSendSorted bs1 bs2 = some rest) :
    rest.Pairwise LocalTypeR.branchLe := by
  induction bs1 generalizing bs2 rest with
  | nil =>
    cases bs2 with
    | nil =>
      have : rest = [] := by
        simpa [LocalTypeR.mergeSendSorted] using h
      simp [this]
    | cons head2 tail2 =>
      cases (by simpa [LocalTypeR.mergeSendSorted] using h : False)
  | cons head tail ih =>
    cases bs2 with
    | nil =>
      cases (by simpa [LocalTypeR.mergeSendSorted] using h : False)
    | cons head2 tail2 =>
      cases head with
      | mk l1 c1 =>
        cases head2 with
        | mk l2 c2 =>
          cases hSorted with
          | cons hRel hTail =>
            by_cases hLabel : l1 = l2
            · subst hLabel
              cases hCont : LocalTypeR.merge c1 c2 with
              | none =>
                cases (by simpa [LocalTypeR.mergeSendSorted, hCont] using h : False)
              | some mergedCont =>
                cases hRest : LocalTypeR.mergeSendSorted tail tail2 with
                | none =>
                  cases (by simpa [LocalTypeR.mergeSendSorted, hCont, hRest] using h : False)
                | some restTail =>
                  have hEq : (l1, mergedCont) :: restTail = rest := by
                    simpa [LocalTypeR.mergeSendSorted, hCont, hRest] using h
                  have hTailPair : restTail.Pairwise LocalTypeR.branchLe :=
                    ih (bs2 := tail2) (rest := restTail) hTail hRest
                  have hHeadRel :
                      ∀ b ∈ restTail, LocalTypeR.branchLe (l1, mergedCont) b = true := by
                    intro b hb
                    have hbFstInRestTail : b.1 ∈ restTail.map Prod.fst :=
                      List.mem_map_of_mem (f := Prod.fst) hb
                    have hFstEq : restTail.map Prod.fst = tail.map Prod.fst :=
                      mergeSendSorted_map_fst (bs1 := tail) (bs2 := tail2) (rest := restTail) hRest
                    have hbFstInTail : b.1 ∈ tail.map Prod.fst := by
                      simpa [hFstEq] using hbFstInRestTail
                    rcases (List.mem_map.1 hbFstInTail) with ⟨a', ha', ha'Eq⟩
                    have hName : l1.name ≤ b.1.name := by
                      have hName' : l1.name ≤ a'.1.name := by
                        have hLe : LocalTypeR.branchLe (l1, c1) a' = true := hRel a' ha'
                        simpa [LocalTypeR.branchLe] using hLe
                      simpa [ha'Eq] using hName'
                    simpa [LocalTypeR.branchLe, hName]
                  rw [← hEq]
                  exact List.Pairwise.cons hHeadRel hTailPair
            · cases (by simpa [LocalTypeR.mergeSendSorted, hLabel] using h : False)

end Rumpsteak.Proofs.Projection.Merging
