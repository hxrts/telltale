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

/-! ## sortBranches preservation for merge operations -/

/-- mergeSendSorted preserves the label sequence from the first list.
    If mergeSendSorted bs1 bs2 = some merged, then merged.map (·.1) = bs1.map (·.1). -/
theorem mergeSendSorted_labels_eq
    (bs1 bs2 merged : List (Label × LocalTypeR))
    (hmerge : LocalTypeR.mergeSendSorted bs1 bs2 = some merged)
    : merged.map (·.1) = bs1.map (·.1) := by
  induction bs1 generalizing bs2 merged with
  | nil =>
    cases bs2 with
    | nil =>
      unfold LocalTypeR.mergeSendSorted at hmerge
      simp at hmerge; subst hmerge; rfl
    | cons _ _ =>
      unfold LocalTypeR.mergeSendSorted at hmerge
      simp at hmerge
  | cons h1 t1 ih =>
    cases bs2 with
    | nil =>
      unfold LocalTypeR.mergeSendSorted at hmerge
      simp at hmerge
    | cons h2 t2 =>
      unfold LocalTypeR.mergeSendSorted at hmerge
      split at hmerge
      · next heq =>
        simp only [Option.bind_eq_bind] at hmerge
        cases hmc : LocalTypeR.merge h1.2 h2.2 with
        | none => simp [hmc] at hmerge
        | some mc =>
          simp only [hmc, Option.bind_some] at hmerge
          cases hmr : LocalTypeR.mergeSendSorted t1 t2 with
          | none => simp [hmr] at hmerge
          | some mr =>
            simp only [hmr, Option.bind_some] at hmerge
            simp at hmerge; subst hmerge
            simp only [List.map_cons, Prod.fst]
            congr
            exact ih t2 mr hmr
      · simp at hmerge

/-- If bs1 is sorted (Pairwise branchLe), and mergeSendSorted bs1 bs2 = some merged,
    then merged is also sorted. -/
theorem mergeSendSorted_pairwise
    (bs1 bs2 merged : List (Label × LocalTypeR))
    (hsorted : bs1.Pairwise LocalTypeR.branchLe)
    (hmerge : LocalTypeR.mergeSendSorted bs1 bs2 = some merged)
    : merged.Pairwise LocalTypeR.branchLe := by
  -- merged has the same labels as bs1, so if bs1 is sorted, merged is sorted
  have hlabels := mergeSendSorted_labels_eq bs1 bs2 merged hmerge
  induction bs1 generalizing bs2 merged with
  | nil =>
    cases bs2 with
    | nil =>
      unfold LocalTypeR.mergeSendSorted at hmerge
      simp at hmerge; subst hmerge
      exact List.Pairwise.nil
    | cons _ _ =>
      unfold LocalTypeR.mergeSendSorted at hmerge
      simp at hmerge
  | cons h1 t1 ih =>
    cases bs2 with
    | nil =>
      unfold LocalTypeR.mergeSendSorted at hmerge
      simp at hmerge
    | cons h2 t2 =>
      unfold LocalTypeR.mergeSendSorted at hmerge
      split at hmerge
      · next heq =>
        simp only [Option.bind_eq_bind] at hmerge
        cases hmc : LocalTypeR.merge h1.2 h2.2 with
        | none => simp [hmc] at hmerge
        | some mc =>
          simp only [hmc, Option.bind_some] at hmerge
          cases hmr : LocalTypeR.mergeSendSorted t1 t2 with
          | none => simp [hmr] at hmerge
          | some mr =>
            simp only [hmr, Option.bind_some] at hmerge
            simp at hmerge; subst hmerge
            -- Goal: ((h1.1, mc) :: mr).Pairwise branchLe
            rw [List.pairwise_cons]
            constructor
            · -- h1.1 is ≤ all elements in mr
              intro b hb
              -- b ∈ mr, and mr has labels from t1
              have hmr_labels := mergeSendSorted_labels_eq t1 t2 mr hmr
              -- b.1 ∈ mr.map fst = t1.map fst
              have hb_label : b.1 ∈ mr.map (·.1) := List.mem_map_of_mem (·.1) hb
              rw [hmr_labels] at hb_label
              -- So b.1 is in t1.map fst, meaning there's some (b.1, _) in t1
              obtain ⟨c, hc_mem, hc_fst⟩ := List.mem_map.mp hb_label
              -- Since h1 :: t1 is sorted, h1 ≤ c (which has first component b.1)
              rw [List.pairwise_cons] at hsorted
              have h1_le_c := hsorted.1 c hc_mem
              -- branchLe compares first components
              simp only [LocalTypeR.branchLe] at h1_le_c ⊢
              rw [← hc_fst]
              exact h1_le_c
            · -- mr is Pairwise branchLe
              have htail_sorted : t1.Pairwise LocalTypeR.branchLe := by
                rw [List.pairwise_cons] at hsorted
                exact hsorted.2
              exact ih t2 mr htail_sorted hmr
      · simp at hmerge

/-- Main theorem: If bs1 = sortBranches bs1 and bs2 = sortBranches bs2,
    and mergeSendSorted bs1 bs2 = some merged, then sortBranches merged = merged. -/
theorem sortBranches_mergeSendSorted_id'
    (bs1 bs2 merged : List (Label × LocalTypeR))
    (h1 : bs1 = LocalTypeR.sortBranches bs1)
    (h2 : bs2 = LocalTypeR.sortBranches bs2)
    (hmerge : LocalTypeR.mergeSendSorted bs1 bs2 = some merged)
    : LocalTypeR.sortBranches merged = merged := by
  -- bs1 is sorted because sortBranches returns a sorted list
  have hs1 : bs1.Pairwise LocalTypeR.branchLe := by
    rw [h1]
    exact pairwise_sortBranches bs1
  -- merged is sorted by mergeSendSorted_pairwise
  have hm : merged.Pairwise LocalTypeR.branchLe :=
    mergeSendSorted_pairwise bs1 bs2 merged hs1 hmerge
  -- Sorted lists are fixed by sortBranches
  exact sortBranches_eq_of_pairwise merged hm

/-! ## mergeRecvSorted sorting preservation -/

/-- Helper: every label in the output of mergeRecvSorted comes from either bs1 or bs2.
    More precisely: for any (l, c) in merged, there exists (l, c') in bs1 or (l, c') in bs2
    (possibly with different continuation). -/
theorem mergeRecvSorted_label_mem
    (bs1 bs2 merged : List (Label × LocalTypeR))
    (hmerge : LocalTypeR.mergeRecvSorted bs1 bs2 = some merged)
    (b : Label × LocalTypeR) (hb : b ∈ merged)
    : (∃ c, (b.1, c) ∈ bs1) ∨ (∃ c, (b.1, c) ∈ bs2) := by
  induction bs1 generalizing bs2 merged with
  | nil =>
    unfold LocalTypeR.mergeRecvSorted at hmerge
    simp at hmerge; subst hmerge
    right; exact ⟨b.2, hb⟩
  | cons h1 t1 ih1 =>
    cases bs2 with
    | nil =>
      unfold LocalTypeR.mergeRecvSorted at hmerge
      simp at hmerge; subst hmerge
      left; exact ⟨b.2, hb⟩
    | cons h2 t2 =>
      unfold LocalTypeR.mergeRecvSorted at hmerge
      simp only at hmerge
      split at hmerge
      · next hlt1 =>
        simp only [Option.bind_eq_bind] at hmerge
        cases hmr : LocalTypeR.mergeRecvSorted t1 ((h2.1, h2.2) :: t2) with
        | none => simp [hmr] at hmerge
        | some mr =>
          simp only [hmr, Option.bind_some] at hmerge
          simp at hmerge; subst hmerge
          cases hb with
          | head => left; exact ⟨h1.2, List.Mem.head _⟩
          | tail _ hb' =>
            have := ih1 ((h2.1, h2.2) :: t2) mr hmr b hb'
            cases this with
            | inl h => left; obtain ⟨c, hc⟩ := h; exact ⟨c, List.Mem.tail _ hc⟩
            | inr h => right; exact h
      · split at hmerge
        · next hlt2 =>
          simp only [Option.bind_eq_bind] at hmerge
          cases hmr : LocalTypeR.mergeRecvSorted ((h1.1, h1.2) :: t1) t2 with
          | none => simp [hmr] at hmerge
          | some mr =>
            simp only [hmr, Option.bind_some] at hmerge
            simp at hmerge; subst hmerge
            cases hb with
            | head => right; exact ⟨h2.2, List.Mem.head _⟩
            | tail _ hb' =>
              have := ih1 t2 mr hmr b hb'
              cases this with
              | inl h => left; exact h
              | inr h => right; obtain ⟨c, hc⟩ := h; exact ⟨c, List.Mem.tail _ hc⟩
        · split at hmerge
          · next heq =>
            simp only [Option.bind_eq_bind] at hmerge
            cases hmc : LocalTypeR.merge h1.2 h2.2 with
            | none => simp [hmc] at hmerge
            | some mc =>
              simp only [hmc, Option.bind_some] at hmerge
              cases hmr : LocalTypeR.mergeRecvSorted t1 t2 with
              | none => simp [hmr] at hmerge
              | some mr =>
                simp only [hmr, Option.bind_some] at hmerge
                simp at hmerge; subst hmerge
                cases hb with
                | head =>
                  -- b = (h1.1, mc), and h1.1 = h2.1
                  left; exact ⟨h1.2, List.Mem.head _⟩
                | tail _ hb' =>
                  have := ih1 t2 mr hmr b hb'
                  cases this with
                  | inl h => left; obtain ⟨c, hc⟩ := h; exact ⟨c, List.Mem.tail _ hc⟩
                  | inr h => right; obtain ⟨c, hc⟩ := h; exact ⟨c, List.Mem.tail _ hc⟩
          · simp at hmerge
  termination_by sizeOf bs1 + sizeOf bs2
  decreasing_by
    all_goals
      simp_wf
      first
        | apply Nat.add_lt_add_right; exact sizeOf_tail_lt_cons h1 t1
        | apply Nat.add_lt_add_left; exact sizeOf_tail_lt_cons h2 t2
        | apply Nat.add_lt_add; exact sizeOf_tail_lt_cons h1 t1; exact sizeOf_tail_lt_cons h2 t2

/-- mergeRecvSorted preserves sortedness.
    If both inputs are sorted, the output is sorted.
    This is essentially the merge step of merge sort. -/
theorem mergeRecvSorted_pairwise
    (bs1 bs2 merged : List (Label × LocalTypeR))
    (hs1 : bs1.Pairwise LocalTypeR.branchLe)
    (hs2 : bs2.Pairwise LocalTypeR.branchLe)
    (hmerge : LocalTypeR.mergeRecvSorted bs1 bs2 = some merged)
    : merged.Pairwise LocalTypeR.branchLe := by
  induction bs1 generalizing bs2 merged with
  | nil =>
    -- bs1 = [], so merged = bs2
    unfold LocalTypeR.mergeRecvSorted at hmerge
    simp at hmerge; subst hmerge
    exact hs2
  | cons h1 t1 ih1 =>
    induction bs2 generalizing merged with
    | nil =>
      -- bs2 = [], so merged = h1 :: t1
      unfold LocalTypeR.mergeRecvSorted at hmerge
      simp at hmerge; subst hmerge
      exact hs1
    | cons h2 t2 ih2 =>
      unfold LocalTypeR.mergeRecvSorted at hmerge
      simp only at hmerge
      split at hmerge
      · next hlt1 =>
        -- l1.name < l2.name: merged = h1 :: (mergeRecvSorted t1 (h2::t2))
        simp only [Option.bind_eq_bind] at hmerge
        cases hmr : LocalTypeR.mergeRecvSorted t1 ((h2.1, h2.2) :: t2) with
        | none => simp [hmr] at hmerge
        | some mr =>
          simp only [hmr, Option.bind_some] at hmerge
          simp at hmerge; subst hmerge
          -- Goal: (h1 :: mr).Pairwise branchLe
          rw [List.pairwise_cons]
          have ht1_sorted : t1.Pairwise LocalTypeR.branchLe := by
            rw [List.pairwise_cons] at hs1
            exact hs1.2
          have hmr_sorted := ih1 ((h2.1, h2.2) :: t2) mr ht1_sorted hs2 hmr
          constructor
          · -- h1 ≤ all elements in mr
            intro b hb
            simp only [LocalTypeR.branchLe]
            -- b's label comes from either t1 or h2::t2
            have hmem := mergeRecvSorted_label_mem t1 ((h2.1, h2.2) :: t2) mr hmr b hb
            cases hmem with
            | inl h =>
              -- b.1 comes from t1, so h1.1.name ≤ b.1.name by hs1
              obtain ⟨c, hc⟩ := h
              rw [List.pairwise_cons] at hs1
              have := hs1.1 (b.1, c) hc
              simp only [LocalTypeR.branchLe] at this
              exact this
            | inr h =>
              -- b.1 comes from h2::t2, so h1.1.name < h2.1.name ≤ b.1.name
              obtain ⟨c, hc⟩ := h
              cases hc with
              | head =>
                -- b.1 = h2.1, so h1.1.name < h2.1.name means h1.1.name ≤ h2.1.name
                exact String.le_of_lt hlt1
              | tail _ hc' =>
                -- b.1 is in t2, and h2 ≤ all of t2 by hs2
                rw [List.pairwise_cons] at hs2
                have h2_le_c := hs2.1 (b.1, c) hc'
                simp only [LocalTypeR.branchLe] at h2_le_c
                exact Std.le_trans (String.le_of_lt hlt1) h2_le_c
          · exact hmr_sorted
      · split at hmerge
        · next hlt2 =>
          -- l2.name < l1.name: merged = h2 :: (mergeRecvSorted (h1::t1) t2)
          simp only [Option.bind_eq_bind] at hmerge
          cases hmr : LocalTypeR.mergeRecvSorted ((h1.1, h1.2) :: t1) t2 with
          | none => simp [hmr] at hmerge
          | some mr =>
            simp only [hmr, Option.bind_some] at hmerge
            simp at hmerge; subst hmerge
            rw [List.pairwise_cons]
            have ht2_sorted : t2.Pairwise LocalTypeR.branchLe := by
              rw [List.pairwise_cons] at hs2
              exact hs2.2
            have hmr_sorted := ih2 ht2_sorted mr hmr
            constructor
            · -- h2 ≤ all elements in mr
              intro b hb
              simp only [LocalTypeR.branchLe]
              -- b's label comes from either h1::t1 or t2
              have hmem := mergeRecvSorted_label_mem ((h1.1, h1.2) :: t1) t2 mr hmr b hb
              cases hmem with
              | inl h =>
                -- b.1 comes from h1::t1, so h2.1.name < h1.1.name ≤ b.1.name
                obtain ⟨c, hc⟩ := h
                cases hc with
                | head =>
                  -- b.1 = h1.1, so h2.1.name < h1.1.name means h2.1.name ≤ h1.1.name
                  exact String.le_of_lt hlt2
                | tail _ hc' =>
                  -- b.1 is in t1, and h1 ≤ all of t1 by hs1
                  rw [List.pairwise_cons] at hs1
                  have h1_le_c := hs1.1 (b.1, c) hc'
                  simp only [LocalTypeR.branchLe] at h1_le_c
                  exact Std.le_trans (String.le_of_lt hlt2) h1_le_c
              | inr h =>
                -- b.1 comes from t2, so h2.1.name ≤ b.1.name by hs2
                obtain ⟨c, hc⟩ := h
                rw [List.pairwise_cons] at hs2
                have := hs2.1 (b.1, c) hc
                simp only [LocalTypeR.branchLe] at this
                exact this
            · exact hmr_sorted
        · split at hmerge
          · next heq =>
            -- l1 = l2: merge continuations
            simp only [Option.bind_eq_bind] at hmerge
            cases hmc : LocalTypeR.merge h1.2 h2.2 with
            | none => simp [hmc] at hmerge
            | some mc =>
              simp only [hmc, Option.bind_some] at hmerge
              cases hmr : LocalTypeR.mergeRecvSorted t1 t2 with
              | none => simp [hmr] at hmerge
              | some mr =>
                simp only [hmr, Option.bind_some] at hmerge
                simp at hmerge; subst hmerge
                rw [List.pairwise_cons]
                have ht1_sorted : t1.Pairwise LocalTypeR.branchLe := by
                  rw [List.pairwise_cons] at hs1
                  exact hs1.2
                have ht2_sorted : t2.Pairwise LocalTypeR.branchLe := by
                  rw [List.pairwise_cons] at hs2
                  exact hs2.2
                have hmr_sorted := ih1 t2 mr ht1_sorted ht2_sorted hmr
                constructor
                · -- (h1.1, mc) ≤ all elements in mr
                  intro b hb
                  simp only [LocalTypeR.branchLe]
                  -- b's label comes from either t1 or t2
                  have hmem := mergeRecvSorted_label_mem t1 t2 mr hmr b hb
                  cases hmem with
                  | inl h =>
                    -- b.1 comes from t1, so h1.1.name ≤ b.1.name by hs1
                    obtain ⟨c, hc⟩ := h
                    rw [List.pairwise_cons] at hs1
                    have := hs1.1 (b.1, c) hc
                    simp only [LocalTypeR.branchLe] at this
                    exact this
                  | inr h =>
                    -- b.1 comes from t2, so h2.1.name ≤ b.1.name by hs2
                    -- And h1.1 = h2.1 (by heq), so h1.1.name ≤ b.1.name
                    obtain ⟨c, hc⟩ := h
                    rw [List.pairwise_cons] at hs2
                    have := hs2.1 (b.1, c) hc
                    simp only [LocalTypeR.branchLe] at this
                    rw [heq]
                    exact this
                · exact hmr_sorted
          · simp at hmerge
  termination_by sizeOf bs1 + sizeOf bs2
  decreasing_by
    all_goals
      simp_wf
      first
        | -- Left shrinks
          apply Nat.add_lt_add_right
          exact sizeOf_tail_lt_cons h1 t1
        | -- Right shrinks
          apply Nat.add_lt_add_left
          exact sizeOf_tail_lt_cons h2 t2
        | -- Both shrink
          apply Nat.add_lt_add
          · exact sizeOf_tail_lt_cons h1 t1
          · exact sizeOf_tail_lt_cons h2 t2

/-- Main theorem: If bs1 = sortBranches bs1 and bs2 = sortBranches bs2,
    and mergeRecvSorted bs1 bs2 = some merged, then sortBranches merged = merged. -/
theorem sortBranches_mergeRecvSorted_id'
    (bs1 bs2 merged : List (Label × LocalTypeR))
    (h1 : bs1 = LocalTypeR.sortBranches bs1)
    (h2 : bs2 = LocalTypeR.sortBranches bs2)
    (hmerge : LocalTypeR.mergeRecvSorted bs1 bs2 = some merged)
    : LocalTypeR.sortBranches merged = merged := by
  have hs1 : bs1.Pairwise LocalTypeR.branchLe := by
    rw [h1]
    exact pairwise_sortBranches bs1
  have hs2 : bs2.Pairwise LocalTypeR.branchLe := by
    rw [h2]
    exact pairwise_sortBranches bs2
  have hm : merged.Pairwise LocalTypeR.branchLe :=
    mergeRecvSorted_pairwise bs1 bs2 merged hs1 hs2 hmerge
  exact sortBranches_eq_of_pairwise merged hm

end Rumpsteak.Proofs.Projection.Merging
