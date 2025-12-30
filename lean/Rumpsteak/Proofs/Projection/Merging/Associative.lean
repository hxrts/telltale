import Rumpsteak.Proofs.Projection.Merging.Basic
import Rumpsteak.Proofs.Projection.Merging.SortLemmas

/-! # Rumpsteak.Proofs.Projection.Merging.Associative

Proof that merge is associative (in the 3-way commutative form).

## Overview

This module proves `MergeAssociative`:
∀ T1 T2 T3, (T1.merge T2).bind (·.merge T3) = (T2.merge T3).bind (T1.merge ·)

This is the most complex merge property, requiring extensive case analysis on
all combinations of local type constructors and their branch structures.

## Proof Strategy

1. Define `MergeAssocAt t` as the associativity property for a fixed first argument
2. Prove helper lemmas for sorted branch merging (`mergeSendSorted_assoc`, `mergeRecvSorted_assoc`)
3. Use nested structural induction to prove `MergeAssocAt` for all local types
4. Derive `MergeAssociative` from `MergeAssocAt`
-/

namespace Rumpsteak.Proofs.Projection.Merging

open Rumpsteak.Protocol.LocalTypeR
open Rumpsteak.Protocol.GlobalType (Label)
open Rumpsteak.Protocol.ProjectionR

attribute [local instance] boolRelToRel

/-! ## Helper lemmas -/

private theorem mergeSendSorted_map_fst :
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

private theorem mergeRecvSorted_mem_fst
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
      simp_wf
      simp (config := { failIfUnchanged := false }) [hbs1, hbs2]
      try omega

private theorem mergeRecvSorted_pairwise
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
      simp_wf
      simp (config := { failIfUnchanged := false }) [hbs1, hbs2]
      try omega

private theorem mergeSendSorted_pairwise
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

/-! ## MergeAssocAt predicate -/

private def MergeAssocAt (t : LocalTypeR) : Prop :=
  ∀ u v,
    (LocalTypeR.merge t u).bind (fun m => LocalTypeR.merge m v) =
    (LocalTypeR.merge u v).bind (fun m => LocalTypeR.merge t m)

/-! ## Option bind helpers -/

private theorem option_bind_comm {α β γ : Type} (oa : Option α) (ob : Option β) (f : α → β → Option γ) :
    oa.bind (fun a => ob.bind (fun b => f a b)) =
    ob.bind (fun b => oa.bind (fun a => f a b)) := by
  cases oa <;> cases ob <;> rfl

@[simp] private theorem option_bind_some_id {α : Type} (x : Option α) :
    x.bind (fun a => some a) = x := by
  cases x <;> rfl

@[simp] private theorem option_bind_const_none {α β : Type} (x : Option α) :
    x.bind (fun _ => (none : Option β)) = none := by
  cases x <;> rfl

@[simp] private theorem mergeRecvSorted_nil_left (bs : List (Label × LocalTypeR)) :
    LocalTypeR.mergeRecvSorted [] bs = some bs := by
  simp [LocalTypeR.mergeRecvSorted]

@[simp] private theorem mergeRecvSorted_nil_right (bs : List (Label × LocalTypeR)) :
    LocalTypeR.mergeRecvSorted bs [] = some bs := by
  cases bs <;> simp [LocalTypeR.mergeRecvSorted]

/-! ## Sorted branch merge associativity -/

private theorem mergeSendSorted_assoc :
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

private theorem mergeRecvSorted_assoc
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

/-! ## Main theorem -/

theorem merge_associative : MergeAssociative := by
  intro t1 t2 t3
  have ht1 : MergeAssocAt t1 := by
    refine LocalTypeR.recOn
      (motive_1 := fun t => MergeAssocAt t)
      (motive_2 := fun bs => AllBranches MergeAssocAt bs)
      (motive_3 := fun b => MergeAssocAt b.2)
      t1
      (by
        intro u v
        show (LocalTypeR.merge .end u).bind (fun m => LocalTypeR.merge m v) =
             (LocalTypeR.merge u v).bind (fun m => LocalTypeR.merge .end m)
        match u with
        | .end => cases v <;> simp [LocalTypeR.merge]
        | .send p1 bs1 =>
          simp only [LocalTypeR.merge, Option.none_bind]
          match v with
          | .end => simp [LocalTypeR.merge]
          | .send p2 bs2 =>
            simp only [LocalTypeR.merge]
            by_cases hp : p1 = p2
            · simp only [hp, beq_self_eq_true, ↓reduceIte]
              cases h : LocalTypeR.mergeSendSorted (LocalTypeR.sortBranches bs1) (LocalTypeR.sortBranches bs2) <;>
                simp [Option.bind, LocalTypeR.merge]
            · simp [hp, bne_iff_ne, Option.bind]
          | .recv _ _ => simp [LocalTypeR.merge, Option.bind]
          | .mu _ _ => simp [LocalTypeR.merge, Option.bind]
          | .var _ => simp [LocalTypeR.merge, Option.bind]
        | .recv p1 bs1 =>
          simp only [LocalTypeR.merge, Option.none_bind]
          match v with
          | .end => simp [LocalTypeR.merge]
          | .send _ _ => simp [LocalTypeR.merge, Option.bind]
          | .recv p2 bs2 =>
            simp only [LocalTypeR.merge]
            by_cases hp : p1 = p2
            · simp only [hp, beq_self_eq_true, ↓reduceIte]
              cases h : LocalTypeR.mergeRecvSorted (LocalTypeR.sortBranches bs1) (LocalTypeR.sortBranches bs2) <;>
                simp [Option.bind, LocalTypeR.merge]
            · simp [hp, bne_iff_ne, Option.bind]
          | .mu _ _ => simp [LocalTypeR.merge, Option.bind]
          | .var _ => simp [LocalTypeR.merge, Option.bind]
        | .mu x1 body1 =>
          simp only [LocalTypeR.merge, Option.none_bind]
          match v with
          | .end => simp [LocalTypeR.merge]
          | .send _ _ => simp [LocalTypeR.merge, Option.bind]
          | .recv _ _ => simp [LocalTypeR.merge, Option.bind]
          | .mu x2 body2 =>
            simp only [LocalTypeR.merge]
            by_cases hx : x1 = x2
            · simp only [hx, beq_self_eq_true, ↓reduceIte]
              cases h : LocalTypeR.merge body1 body2 <;>
                simp [Option.bind, LocalTypeR.merge]
            · simp [hx, bne_iff_ne, Option.bind]
          | .var _ => simp [LocalTypeR.merge, Option.bind]
        | .var x1 =>
          simp only [LocalTypeR.merge, Option.none_bind]
          match v with
          | .end => simp [LocalTypeR.merge]
          | .send _ _ => simp [LocalTypeR.merge, Option.bind]
          | .recv _ _ => simp [LocalTypeR.merge, Option.bind]
          | .mu _ _ => simp [LocalTypeR.merge, Option.bind]
          | .var x2 =>
            simp only [LocalTypeR.merge]
            by_cases hx : x1 = x2
            · simp [hx, Option.bind, LocalTypeR.merge]
            · simp [hx, Option.bind])
      (fun partner branches1 ihBranches => by
        intro u v
        cases u with
        | send partner2 branches2 =>
          cases v with
          | send partner3 branches3 =>
            by_cases hP12 : partner = partner2
            · subst hP12
              by_cases hP13 : partner = partner3
              · subst hP13
                let bs1 := LocalTypeR.sortBranches branches1
                let bs2 := LocalTypeR.sortBranches branches2
                let bs3 := LocalTypeR.sortBranches branches3

                have hperm1 : bs1.Perm branches1 := by
                  simpa [bs1, LocalTypeR.sortBranches] using
                    (List.mergeSort_perm branches1 LocalTypeR.branchLe)
                have ihSorted : AllBranches MergeAssocAt bs1 :=
                  AllBranches.of_perm _ hperm1 ihBranches

                have hSorted1 : bs1.Pairwise LocalTypeR.branchLe := by
                  simpa [bs1] using pairwise_sortBranches branches1
                have hSorted2 : bs2.Pairwise LocalTypeR.branchLe := by
                  simpa [bs2] using pairwise_sortBranches branches2
                have hSorted3 : bs3.Pairwise LocalTypeR.branchLe := by
                  simpa [bs3] using pairwise_sortBranches branches3

                have hSort12 :
                    ∀ {m12}, LocalTypeR.mergeSendSorted bs1 bs2 = some m12 →
                      LocalTypeR.sortBranches m12 = m12 := by
                  intro m12 hm12
                  have hPair : m12.Pairwise LocalTypeR.branchLe :=
                    mergeSendSorted_pairwise (bs1 := bs1) (bs2 := bs2) (rest := m12) hSorted1 hm12
                  exact sortBranches_eq_of_pairwise m12 hPair

                have hSort23 :
                    ∀ {m23}, LocalTypeR.mergeSendSorted bs2 bs3 = some m23 →
                      LocalTypeR.sortBranches m23 = m23 := by
                  intro m23 hm23
                  have hPair : m23.Pairwise LocalTypeR.branchLe :=
                    mergeSendSorted_pairwise (bs1 := bs2) (bs2 := bs3) (rest := m23) hSorted2 hm23
                  exact sortBranches_eq_of_pairwise m23 hPair

                have hAssoc :=
                  mergeSendSorted_assoc bs1 bs2 bs3 ihSorted

                have hL :
                    (LocalTypeR.merge (.send partner branches1) (.send partner branches2)).bind
                        (fun m => LocalTypeR.merge m (.send partner branches3)) =
                      (LocalTypeR.mergeSendSorted bs1 bs2).bind (fun m12 =>
                        (LocalTypeR.mergeSendSorted m12 bs3).bind (fun m123 =>
                          some (.send partner m123))) := by
                  simp only [LocalTypeR.merge, bs1, bs2, bs3, beq_self_eq_true, ↓reduceIte, bne_self_eq_false]
                  simp only [Option.bind_eq_bind, Option.bind_some]
                  conv_lhs =>
                    rw [Option.bind_assoc]
                  cases hMerge12 : LocalTypeR.mergeSendSorted (LocalTypeR.sortBranches branches1)
                                                              (LocalTypeR.sortBranches branches2) with
                  | none => simp [Option.bind]
                  | some m12 =>
                    simp only [Option.bind]
                    have hSortM12 : LocalTypeR.sortBranches m12 = m12 := hSort12 hMerge12
                    simp only [LocalTypeR.merge, beq_self_eq_true, ↓reduceIte, bne_self_eq_false]
                    simp only [Option.bind_eq_bind, Option.bind_some]
                    rw [hSortM12]

                have hR :
                    (LocalTypeR.merge (.send partner branches2) (.send partner branches3)).bind
                        (fun m => LocalTypeR.merge (.send partner branches1) m) =
                      (LocalTypeR.mergeSendSorted bs2 bs3).bind (fun m23 =>
                        (LocalTypeR.mergeSendSorted bs1 m23).bind (fun m123 =>
                          some (.send partner m123))) := by
                  simp only [LocalTypeR.merge, bs1, bs2, bs3, beq_self_eq_true, ↓reduceIte, bne_self_eq_false]
                  simp only [Option.bind_eq_bind, Option.bind_some]
                  conv_lhs =>
                    rw [Option.bind_assoc]
                  cases hMerge23 : LocalTypeR.mergeSendSorted (LocalTypeR.sortBranches branches2)
                                                              (LocalTypeR.sortBranches branches3) with
                  | none => simp [Option.bind]
                  | some m23 =>
                    simp only [Option.bind]
                    have hSortM23 : LocalTypeR.sortBranches m23 = m23 := hSort23 hMerge23
                    simp only [LocalTypeR.merge, beq_self_eq_true, ↓reduceIte, bne_self_eq_false]
                    simp only [Option.bind_eq_bind, Option.bind_some]
                    rw [hSortM23]

                simp only [MergeAssocAt]
                intro u v
                rw [hL, hR]
                exact hAssoc
              · simp only [MergeAssocAt]
                intro u v
                simp only [LocalTypeR.merge, bne_iff_ne, Ne.symm hP13, ↓reduceIte, Option.none_bind]
                simp only [bne_iff_ne, Ne.symm hP13, ↓reduceIte, Option.none_bind]
            · simp only [MergeAssocAt]
              intro u v
              simp only [LocalTypeR.merge, bne_iff_ne, Ne.symm hP12, ↓reduceIte, Option.none_bind]
              cases v with
              | send partner3 branches3 =>
                simp only [LocalTypeR.merge, Option.bind]
                by_cases hP23 : partner2 = partner3
                · subst hP23
                  cases h : LocalTypeR.mergeSendSorted (LocalTypeR.sortBranches branches2)
                                                        (LocalTypeR.sortBranches branches3) with
                  | none => simp [Option.bind]
                  | some merged =>
                    simp only [↓reduceIte, Option.some_bind]
                    simp only [LocalTypeR.merge, bne_iff_ne, hP12, ↓reduceIte]
                · simp only [bne_iff_ne, Ne.symm hP23, ↓reduceIte, Option.none_bind]
              | _ => simp [LocalTypeR.merge, Option.bind]
          | _ =>
            simp only [MergeAssocAt]
            intro u v
            simp only [LocalTypeR.merge, Option.none_bind]
            cases v <;> simp [LocalTypeR.merge, Option.bind]
        | _ =>
          simp only [MergeAssocAt]
          intro u v
          simp only [LocalTypeR.merge, Option.none_bind]
          cases v <;> simp [LocalTypeR.merge, Option.bind])
      (fun partner branches1 ihBranches => by
        intro u v
        cases u with
        | recv partner2 branches2 =>
          cases v with
          | recv partner3 branches3 =>
            by_cases hP12 : partner = partner2
            · subst hP12
              by_cases hP13 : partner = partner3
              · subst hP13
                let bs1 := LocalTypeR.sortBranches branches1
                let bs2 := LocalTypeR.sortBranches branches2
                let bs3 := LocalTypeR.sortBranches branches3

                have hperm1 : bs1.Perm branches1 := by
                  simpa [bs1, LocalTypeR.sortBranches] using
                    (List.mergeSort_perm branches1 LocalTypeR.branchLe)
                have ihSorted : AllBranches MergeAssocAt bs1 :=
                  AllBranches.of_perm _ hperm1 ihBranches

                have hSorted1 : bs1.Pairwise LocalTypeR.branchLe := by
                  simpa [bs1] using pairwise_sortBranches branches1
                have hSorted2 : bs2.Pairwise LocalTypeR.branchLe := by
                  simpa [bs2] using pairwise_sortBranches branches2

                have hSort12 :
                    ∀ {m12}, LocalTypeR.mergeRecvSorted bs1 bs2 = some m12 →
                      LocalTypeR.sortBranches m12 = m12 := by
                  intro m12 hm12
                  have hPair : m12.Pairwise LocalTypeR.branchLe :=
                    mergeRecvSorted_pairwise (bs1 := bs1) (bs2 := bs2) (rest := m12) hSorted1 hSorted2 hm12
                  exact sortBranches_eq_of_pairwise m12 hPair

                have hSort23 :
                    ∀ {m23}, LocalTypeR.mergeRecvSorted bs2 bs3 = some m23 →
                      LocalTypeR.sortBranches m23 = m23 := by
                  intro m23 hm23
                  have hSorted3 : bs3.Pairwise LocalTypeR.branchLe := by
                    simpa [bs3] using pairwise_sortBranches branches3
                  have hPair : m23.Pairwise LocalTypeR.branchLe :=
                    mergeRecvSorted_pairwise (bs1 := bs2) (bs2 := bs3) (rest := m23) hSorted2 hSorted3 hm23
                  exact sortBranches_eq_of_pairwise m23 hPair

                have hAssoc :=
                  mergeRecvSorted_assoc bs1 bs2 bs3 ihSorted

                have hL :
                    (LocalTypeR.merge (.recv partner branches1) (.recv partner branches2)).bind
                        (fun m => LocalTypeR.merge m (.recv partner branches3)) =
                      (LocalTypeR.mergeRecvSorted bs1 bs2).bind (fun m12 =>
                        (LocalTypeR.mergeRecvSorted m12 bs3).bind (fun m123 =>
                          some (.recv partner m123))) := by
                  simp only [LocalTypeR.merge, bs1, bs2, bs3, beq_self_eq_true, ↓reduceIte, bne_self_eq_false]
                  simp only [Option.bind_eq_bind, Option.bind_some]
                  conv_lhs =>
                    rw [Option.bind_assoc]
                  cases hMerge12 : LocalTypeR.mergeRecvSorted (LocalTypeR.sortBranches branches1)
                                                              (LocalTypeR.sortBranches branches2) with
                  | none => simp [Option.bind]
                  | some m12 =>
                    simp only [Option.bind]
                    have hSortM12 : LocalTypeR.sortBranches m12 = m12 := hSort12 hMerge12
                    simp only [LocalTypeR.merge, beq_self_eq_true, ↓reduceIte, bne_self_eq_false]
                    simp only [Option.bind_eq_bind, Option.bind_some]
                    rw [hSortM12]

                have hR :
                    (LocalTypeR.merge (.recv partner branches2) (.recv partner branches3)).bind
                        (fun m => LocalTypeR.merge (.recv partner branches1) m) =
                      (LocalTypeR.mergeRecvSorted bs2 bs3).bind (fun m23 =>
                        (LocalTypeR.mergeRecvSorted bs1 m23).bind (fun m123 =>
                          some (.recv partner m123))) := by
                  simp only [LocalTypeR.merge, bs1, bs2, bs3, beq_self_eq_true, ↓reduceIte, bne_self_eq_false]
                  simp only [Option.bind_eq_bind, Option.bind_some]
                  conv_lhs =>
                    rw [Option.bind_assoc]
                  cases hMerge23 : LocalTypeR.mergeRecvSorted (LocalTypeR.sortBranches branches2)
                                                              (LocalTypeR.sortBranches branches3) with
                  | none => simp [Option.bind]
                  | some m23 =>
                    simp only [Option.bind]
                    have hSortM23 : LocalTypeR.sortBranches m23 = m23 := hSort23 hMerge23
                    simp only [LocalTypeR.merge, beq_self_eq_true, ↓reduceIte, bne_self_eq_false]
                    simp only [Option.bind_eq_bind, Option.bind_some]
                    rw [hSortM23]

                simp only [MergeAssocAt]
                intro u v
                rw [hL, hR]
                exact hAssoc
              · simp only [MergeAssocAt]
                intro u v
                simp only [LocalTypeR.merge, bne_iff_ne, Ne.symm hP13, ↓reduceIte, Option.none_bind]
                simp only [bne_iff_ne, Ne.symm hP13, ↓reduceIte, Option.none_bind]
            · simp only [MergeAssocAt]
              intro u v
              simp only [LocalTypeR.merge, bne_iff_ne, Ne.symm hP12, ↓reduceIte, Option.none_bind]
              cases v with
              | recv partner3 branches3 =>
                simp only [LocalTypeR.merge, Option.bind]
                by_cases hP23 : partner2 = partner3
                · subst hP23
                  cases h : LocalTypeR.mergeRecvSorted (LocalTypeR.sortBranches branches2)
                                                        (LocalTypeR.sortBranches branches3) with
                  | none => simp [Option.bind]
                  | some merged =>
                    simp only [↓reduceIte, Option.some_bind, LocalTypeR.merge, bne_iff_ne, hP12, ↓reduceIte]
                · simp only [bne_iff_ne, Ne.symm hP23, ↓reduceIte, Option.none_bind]
              | _ => simp [LocalTypeR.merge, Option.bind]
          | _ =>
            simp only [MergeAssocAt]
            intro u v
            simp only [LocalTypeR.merge, Option.none_bind]
            cases v <;> simp [LocalTypeR.merge, Option.bind]
        | _ =>
          simp only [MergeAssocAt]
          intro u v
          simp only [LocalTypeR.merge, Option.none_bind]
          cases v <;> simp [LocalTypeR.merge, Option.bind])
      (fun v body ihBody => by
        intro u w
        show (LocalTypeR.merge (.mu v body) u).bind (fun m => LocalTypeR.merge m w) =
             (LocalTypeR.merge u w).bind (fun m => LocalTypeR.merge (.mu v body) m)
        match u with
        | .end => simp [LocalTypeR.merge, Option.bind]
        | .send _ _ =>
          simp only [LocalTypeR.merge, Option.none_bind]
          cases w <;> simp [LocalTypeR.merge, Option.bind]
        | .recv _ _ =>
          simp only [LocalTypeR.merge, Option.none_bind]
          cases w <;> simp [LocalTypeR.merge, Option.bind]
        | .var _ =>
          simp only [LocalTypeR.merge, Option.none_bind]
          cases w <;> simp [LocalTypeR.merge, Option.bind]
        | .mu v' body' =>
          match w with
          | .end =>
            simp only [LocalTypeR.merge, Option.bind]
            by_cases hv : v = v'
            · simp [hv, Option.bind]
            · simp [hv, bne_iff_ne, Option.bind]
          | .send _ _ =>
            simp only [LocalTypeR.merge, Option.bind]
            by_cases hv : v = v'
            · simp [hv, Option.bind]
            · simp [hv, bne_iff_ne, Option.bind]
          | .recv _ _ =>
            simp only [LocalTypeR.merge, Option.bind]
            by_cases hv : v = v'
            · simp [hv, Option.bind]
            · simp [hv, bne_iff_ne, Option.bind]
          | .var _ =>
            simp only [LocalTypeR.merge, Option.bind]
            by_cases hv : v = v'
            · simp [hv, Option.bind]
            · simp [hv, bne_iff_ne, Option.bind]
          | .mu v'' body'' =>
            simp only [LocalTypeR.merge, Option.bind]
            by_cases hv : v = v'
            · subst hv
              by_cases hv'' : v = v''
              · subst hv''
                simp only [beq_self_eq_true, ↓reduceIte, bne_self_eq_false, Option.bind_eq_bind]
                have hBodyAssoc := ihBody body' body''
                cases hM12 : LocalTypeR.merge body body' with
                | none =>
                  simp only [Option.none_bind]
                  cases hM23 : LocalTypeR.merge body' body'' with
                  | none => simp [Option.bind]
                  | some m23 =>
                    simp only [Option.some_bind]
                    have : (LocalTypeR.merge body body').bind (fun m => LocalTypeR.merge m body'') =
                           (LocalTypeR.merge body' body'').bind (fun m => LocalTypeR.merge body m) := hBodyAssoc
                    simp only [hM12, hM23, Option.none_bind, Option.some_bind] at this
                    simp [this]
                | some m12 =>
                  simp only [Option.some_bind]
                  cases hM23 : LocalTypeR.merge body' body'' with
                  | none =>
                    simp only [Option.none_bind]
                    have : (LocalTypeR.merge body body').bind (fun m => LocalTypeR.merge m body'') =
                           (LocalTypeR.merge body' body'').bind (fun m => LocalTypeR.merge body m) := hBodyAssoc
                    simp only [hM12, hM23, Option.some_bind, Option.none_bind] at this
                    simp [this]
                  | some m23 =>
                    simp only [Option.some_bind]
                    have : (LocalTypeR.merge body body').bind (fun m => LocalTypeR.merge m body'') =
                           (LocalTypeR.merge body' body'').bind (fun m => LocalTypeR.merge body m) := hBodyAssoc
                    simp only [hM12, hM23, Option.some_bind] at this
                    cases hM123 : LocalTypeR.merge m12 body'' with
                    | none =>
                      simp only [Option.none_bind]
                      rw [← this]
                      simp [hM123]
                    | some m123 =>
                      simp only [Option.some_bind]
                      have hEq : LocalTypeR.merge m12 body'' = LocalTypeR.merge body m23 := this
                      simp only [hM123] at hEq
                      simp [hEq]
              · simp only [beq_self_eq_true, ↓reduceIte, bne_self_eq_false, bne_iff_ne, hv'', ↓reduceIte]
                simp only [Option.bind_eq_bind, Option.none_bind]
                cases hM12 : LocalTypeR.merge body body' with
                | none => simp [Option.bind]
                | some m12 => simp [Option.bind]
            · simp only [bne_iff_ne, hv, ↓reduceIte, Option.none_bind]
              by_cases hv' : v' = v''
              · subst hv'
                simp only [beq_self_eq_true, ↓reduceIte, Option.bind_eq_bind]
                cases hM23 : LocalTypeR.merge body' body'' with
                | none => simp [Option.bind]
                | some m23 =>
                  simp only [Option.some_bind]
                  simp only [LocalTypeR.merge, bne_iff_ne, hv, ↓reduceIte]
              · simp [bne_iff_ne, hv', Option.bind])
      (fun v => by
        intro u w
        show (LocalTypeR.merge (.var v) u).bind (fun m => LocalTypeR.merge m w) =
             (LocalTypeR.merge u w).bind (fun m => LocalTypeR.merge (.var v) m)
        match u with
        | .end =>
          simp only [LocalTypeR.merge, Option.none_bind]
          cases w <;> simp [LocalTypeR.merge, Option.bind]
        | .send p1 bs1 =>
          simp only [LocalTypeR.merge, Option.none_bind]
          match w with
          | .end => simp [LocalTypeR.merge]
          | .send p2 bs2 =>
            simp only [LocalTypeR.merge]
            by_cases hp : p1 = p2
            · simp only [hp, beq_self_eq_true, ↓reduceIte]
              cases h : LocalTypeR.mergeSendSorted (LocalTypeR.sortBranches bs1) (LocalTypeR.sortBranches bs2) <;>
                simp [Option.bind, LocalTypeR.merge]
            · simp [hp, bne_iff_ne, Option.bind]
          | .recv _ _ => simp [LocalTypeR.merge, Option.bind]
          | .mu _ _ => simp [LocalTypeR.merge, Option.bind]
          | .var _ => simp [LocalTypeR.merge, Option.bind]
        | .recv p1 bs1 =>
          simp only [LocalTypeR.merge, Option.none_bind]
          match w with
          | .end => simp [LocalTypeR.merge]
          | .send _ _ => simp [LocalTypeR.merge, Option.bind]
          | .recv p2 bs2 =>
            simp only [LocalTypeR.merge]
            by_cases hp : p1 = p2
            · simp only [hp, beq_self_eq_true, ↓reduceIte]
              cases h : LocalTypeR.mergeRecvSorted (LocalTypeR.sortBranches bs1) (LocalTypeR.sortBranches bs2) <;>
                simp [Option.bind, LocalTypeR.merge]
            · simp [hp, bne_iff_ne, Option.bind]
          | .mu _ _ => simp [LocalTypeR.merge, Option.bind]
          | .var _ => simp [LocalTypeR.merge, Option.bind]
        | .mu x1 body1 =>
          simp only [LocalTypeR.merge, Option.none_bind]
          match w with
          | .end => simp [LocalTypeR.merge]
          | .send _ _ => simp [LocalTypeR.merge, Option.bind]
          | .recv _ _ => simp [LocalTypeR.merge, Option.bind]
          | .mu x2 body2 =>
            simp only [LocalTypeR.merge]
            by_cases hx : x1 = x2
            · simp only [hx, beq_self_eq_true, ↓reduceIte]
              cases h : LocalTypeR.merge body1 body2 <;> simp [Option.bind, LocalTypeR.merge]
            · simp [hx, bne_iff_ne, Option.bind]
          | .var _ => simp [LocalTypeR.merge, Option.bind]
        | .var a =>
          simp only [LocalTypeR.merge]
          by_cases hva : v = a
          · subst hva
            match w with
            | .end => simp [LocalTypeR.merge]
            | .send _ _ => simp [LocalTypeR.merge, Option.bind]
            | .recv _ _ => simp [LocalTypeR.merge, Option.bind]
            | .mu _ _ => simp [LocalTypeR.merge, Option.bind]
            | .var b =>
              by_cases hvb : v = b
              · simp [hvb, LocalTypeR.merge, Option.bind]
              · simp [hvb, LocalTypeR.merge, Option.bind]
          · simp only [hva, ↓reduceIte, Option.none_bind]
            match w with
            | .end => simp [LocalTypeR.merge]
            | .send _ _ => simp [LocalTypeR.merge, Option.bind]
            | .recv _ _ => simp [LocalTypeR.merge, Option.bind]
            | .mu _ _ => simp [LocalTypeR.merge, Option.bind]
            | .var b =>
              by_cases hab : a = b
              · subst hab
                simp [LocalTypeR.merge, Option.bind, hva]
              · simp [hab, LocalTypeR.merge, Option.bind])
      (AllBranches.nil _)
      (fun head tail ihHead ihTail =>
        AllBranches.cons _ head tail ihHead ihTail)
      (fun _fst _snd ihSnd => ihSnd)
  simpa [MergeAssociative, MergeAssocAt] using ht1 t2 t3

end Rumpsteak.Proofs.Projection.Merging
