import Rumpsteak.Proofs.Projection.Merging.Basic

/-! # Rumpsteak.Proofs.Projection.Merging.SortLemmas

Branch sorting lemmas and helper theorems for merge proofs.

## Overview

This module provides helper lemmas about branch sorting that are used by the
self-idempotence and commutativity proofs:
- Branch ordering transitivity and totality
- Sort preservation lemmas
- Sorted merge commutativity and self-merge lemmas
-/

namespace Rumpsteak.Proofs.Projection.Merging

open Rumpsteak.Protocol.LocalTypeR
open Rumpsteak.Protocol.GlobalType (Label)
open Rumpsteak.Protocol.ProjectionR

attribute [local instance] boolRelToRel

/-! ## Branch ordering lemmas -/

theorem branchLe_trans (a b c : Label × LocalTypeR) :
    LocalTypeR.branchLe a b = true →
    LocalTypeR.branchLe b c = true →
    LocalTypeR.branchLe a c = true := by
  intro hab hbc
  have hab' : a.1.name ≤ b.1.name := by
    simpa [LocalTypeR.branchLe] using hab
  have hbc' : b.1.name ≤ c.1.name := by
    simpa [LocalTypeR.branchLe] using hbc
  have hac : a.1.name ≤ c.1.name := Std.le_trans hab' hbc'
  simpa [LocalTypeR.branchLe, hac]

theorem branchLe_total (a b : Label × LocalTypeR) :
    (LocalTypeR.branchLe a b || LocalTypeR.branchLe b a) = true := by
  by_cases hab : a.1.name ≤ b.1.name
  · simp [LocalTypeR.branchLe, hab]
  · have hba : b.1.name ≤ a.1.name := by
      have ht : a.1.name ≤ b.1.name ∨ b.1.name ≤ a.1.name :=
        Std.le_total (a := a.1.name) (b := b.1.name)
      cases ht with
      | inl h => exact (False.elim (hab h))
      | inr h => exact h
    simp [LocalTypeR.branchLe, hab, hba]

theorem pairwise_sortBranches (bs : List (Label × LocalTypeR)) :
    (LocalTypeR.sortBranches bs).Pairwise LocalTypeR.branchLe := by
  simpa [LocalTypeR.sortBranches] using
    (List.sorted_mergeSort (le := LocalTypeR.branchLe)
      (trans := branchLe_trans) (total := branchLe_total) bs)

theorem sortBranches_eq_of_pairwise
    (bs : List (Label × LocalTypeR))
    (h : bs.Pairwise LocalTypeR.branchLe) :
    LocalTypeR.sortBranches bs = bs := by
  simpa [LocalTypeR.sortBranches] using
    (List.mergeSort_of_sorted (le := LocalTypeR.branchLe) (l := bs) h)

/-- Elements are preserved by sortBranches (it's a permutation). -/
theorem mem_sortBranches_iff (b : Label × LocalTypeR) (bs : List (Label × LocalTypeR)) :
    b ∈ LocalTypeR.sortBranches bs ↔ b ∈ bs := by
  simp only [LocalTypeR.sortBranches]
  have hperm := List.mergeSort_perm bs LocalTypeR.branchLe
  exact hperm.mem_iff

/-- The head of a sorted list is ≤ all elements in its tail. -/
theorem head_le_of_pairwise (h : Label × LocalTypeR) (rest : List (Label × LocalTypeR))
    (hsorted : (h :: rest).Pairwise LocalTypeR.branchLe) :
    ∀ b ∈ rest, LocalTypeR.branchLe h b = true := by
  intro b hb
  -- Pairwise on h :: rest means h is related to all elements in rest
  have hpw : List.Pairwise LocalTypeR.branchLe (h :: rest) := hsorted
  rw [List.pairwise_cons] at hpw
  exact hpw.1 b hb

/-- If h is the head of sortBranches (h :: bs), then h ≤ all elements in bs. -/
theorem sortBranches_head_le (h : Label × LocalTypeR) (bs : List (Label × LocalTypeR))
    (hhead : (LocalTypeR.sortBranches (h :: bs)).head? = some h) :
    ∀ b ∈ bs, LocalTypeR.branchLe h b = true := by
  intro b hb
  -- b ∈ bs implies b ∈ sortBranches (h :: bs)
  have hb_in : b ∈ LocalTypeR.sortBranches (h :: bs) := by
    rw [mem_sortBranches_iff]
    exact List.mem_cons_of_mem h hb
  -- sortBranches is sorted
  have hsorted := pairwise_sortBranches (h :: bs)
  -- Get the sorted list and analyze
  match hsorted_list : LocalTypeR.sortBranches (h :: bs) with
  | [] =>
    -- Can't be empty since h :: bs is nonempty
    simp only [LocalTypeR.sortBranches, List.mergeSort] at hsorted_list
    have hperm := List.mergeSort_perm (h :: bs) LocalTypeR.branchLe
    have hlen : (List.mergeSort (h :: bs) LocalTypeR.branchLe).length = (h :: bs).length := hperm.length_eq
    simp only [hsorted_list, List.length_nil, List.length_cons] at hlen
    exact absurd hlen (by omega)
  | x :: rest =>
    -- x is the head, so x = h by hhead
    simp only [hsorted_list, List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    -- Now hsorted : (h :: rest).Pairwise branchLe
    rw [hsorted_list] at hsorted
    -- b is either h or in rest
    rw [hsorted_list] at hb_in
    have branchLe_refl : ∀ x : Label × LocalTypeR, LocalTypeR.branchLe x x = true := fun x => by
      simp [LocalTypeR.branchLe]
    cases hb_in with
    | head => exact branchLe_refl _
    | tail _ hb_rest => exact head_le_of_pairwise _ rest hsorted b hb_rest

/-! ## Recv sorted merge helpers -/

theorem mergeRecvSorted_comm
    (bs1 bs2 : List (Label × LocalTypeR))
    (ih : AllBranches (fun t => ∀ u, LocalTypeR.merge t u = LocalTypeR.merge u t) bs1) :
    LocalTypeR.mergeRecvSorted bs1 bs2 = LocalTypeR.mergeRecvSorted bs2 bs1 := by
  cases bs1 with
  | nil =>
    cases bs2 <;> simp [LocalTypeR.mergeRecvSorted]
  | cons head1 tail1 =>
    cases bs2 with
    | nil =>
      simp [LocalTypeR.mergeRecvSorted]
    | cons head2 tail2 =>
      cases head1 with
      | mk l1 c1 =>
        cases head2 with
        | mk l2 c2 =>
          by_cases h12 : l1.name < l2.name
          · have h21 : ¬ l2.name < l1.name := String.lt_asymm h12
            have ihTail :
                AllBranches (fun t => ∀ u, LocalTypeR.merge t u = LocalTypeR.merge u t) tail1 := by
              intro b hb
              exact ih b (by simp [hb])
            have hRest := mergeRecvSorted_comm tail1 ((l2, c2) :: tail2) ihTail
            simpa [LocalTypeR.mergeRecvSorted, h12, h21, hRest]
          · by_cases h21 : l2.name < l1.name
            · have hRest := mergeRecvSorted_comm ((l1, c1) :: tail1) tail2 ih
              simpa [LocalTypeR.mergeRecvSorted, h12, h21, hRest]
            · by_cases hEq : l1 = l2
              · subst hEq
                have hCont : LocalTypeR.merge c1 c2 = LocalTypeR.merge c2 c1 :=
                  (ih (l1, c1) (by exact List.Mem.head _)) c2
                have ihTail :
                    AllBranches (fun t => ∀ u, LocalTypeR.merge t u = LocalTypeR.merge u t) tail1 := by
                  intro b hb
                  exact ih b (by simp [hb])
                have hRest := mergeRecvSorted_comm tail1 tail2 ihTail
                simpa [LocalTypeR.mergeRecvSorted, h12, h21, hCont, hRest]
              · have hEq' : l2 ≠ l1 := fun h => hEq h.symm
                simpa [LocalTypeR.mergeRecvSorted, h12, h21, hEq, hEq']
  termination_by sizeOf bs1 + sizeOf bs2
  decreasing_by
    all_goals
      simp_wf
      simp (config := { failIfUnchanged := false })
      first
        | -- Left list shrinks (drop head of `bs1`).
          simpa [*] using (sizeOf_tail_lt_cons head1 tail1)
        | -- Right list shrinks (drop head of `bs2`).
          simpa [*] using (sizeOf_tail_lt_cons head2 tail2)
        | -- Right list shrinks (alternative names).
          simpa [*] using (sizeOf_tail_lt_cons head tail)
        | -- Both lists shrink.
          apply Nat.add_lt_add
          · first
            | simpa [*] using (sizeOf_tail_lt_cons head1 tail1)
            | simpa [*] using (sizeOf_tail_lt_cons head tail)
          · first
            | simpa [*] using (sizeOf_tail_lt_cons head2 tail2)
            | simpa [*] using (sizeOf_tail_lt_cons head tail)

theorem mergeRecvSorted_self
    (bs : List (Label × LocalTypeR))
    (ih : AllBranches (fun t => LocalTypeR.merge t t = some (canonical t)) bs) :
    LocalTypeR.mergeRecvSorted bs bs =
      some (bs.map fun (l, t) => (l, canonical t)) := by
  induction bs with
  | nil =>
    simp [LocalTypeR.mergeRecvSorted]
  | cons head tail ihTail =>
    cases head with
    | mk l t =>
      have ht : LocalTypeR.merge t t = some (canonical t) := ih (l, t) (by simp)
      have ih' :
          AllBranches (fun t => LocalTypeR.merge t t = some (canonical t)) tail := by
        intro b hb
        exact ih b (by simp [hb])
      have hRest := ihTail ih'
      simpa [LocalTypeR.mergeRecvSorted, ht, hRest, String.lt_irrefl]

/-! ## Send sorted merge helpers -/

theorem mergeSendSorted_comm :
    ∀ (bs1 bs2 : List (Label × LocalTypeR)),
      AllBranches (fun t => ∀ u, LocalTypeR.merge t u = LocalTypeR.merge u t) bs1 →
      LocalTypeR.mergeSendSorted bs1 bs2 = LocalTypeR.mergeSendSorted bs2 bs1 := by
  intro bs1
  induction bs1 with
  | nil =>
    intro bs2 _ih
    cases bs2 <;> simp [LocalTypeR.mergeSendSorted]
  | cons head tail ihTail =>
    intro bs2 ih
    cases bs2 with
    | nil =>
      simp [LocalTypeR.mergeSendSorted]
    | cons head2 tail2 =>
      cases head with
      | mk l1 c1 =>
        cases head2 with
        | mk l2 c2 =>
          by_cases hLabel : l1 = l2
          · subst hLabel
            have hCont : LocalTypeR.merge c1 c2 = LocalTypeR.merge c2 c1 :=
              (ih (l1, c1) (by simp)) c2
            have ihTail' :
                AllBranches (fun t => ∀ u, LocalTypeR.merge t u = LocalTypeR.merge u t) tail := by
              intro b hb
              exact ih b (by simp [hb])
            have hRest := ihTail tail2 ihTail'
            simpa [LocalTypeR.mergeSendSorted, hCont, hRest]
          ·
            have hLabel' : ¬ l2 = l1 := fun h => hLabel h.symm
            simpa [LocalTypeR.mergeSendSorted, hLabel, hLabel']

theorem mergeSendSorted_self
    (bs : List (Label × LocalTypeR))
    (ih : AllBranches (fun t => LocalTypeR.merge t t = some (canonical t)) bs) :
    LocalTypeR.mergeSendSorted bs bs =
      some (bs.map fun (l, t) => (l, canonical t)) := by
  induction bs with
  | nil =>
    simp [LocalTypeR.mergeSendSorted]
  | cons head tail ihTail =>
    cases head with
    | mk l t =>
      have ht : LocalTypeR.merge t t = some (canonical t) := ih (l, t) (by simp)
      have ih' :
          AllBranches (fun t => LocalTypeR.merge t t = some (canonical t)) tail := by
        intro b hb
        exact ih b (by simp [hb])
      have hRest := ihTail ih'
      simpa [LocalTypeR.mergeSendSorted, ht, hRest]

end Rumpsteak.Proofs.Projection.Merging
