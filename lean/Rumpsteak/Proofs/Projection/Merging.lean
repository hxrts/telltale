import Rumpsteak.Protocol.LocalTypeR
import Rumpsteak.Protocol.ProjectionR
import Init.Data.List.Sort.Lemmas
import Init.Data.Order.Lemmas
import Init.Data.Option.Lemmas

/-! # Rumpsteak.Proofs.Projection.Merging

Proofs about the merge operator on recursive local types (`LocalTypeR.merge`).

## Overview

In MPST projection with merging (Yoshida & Gheri), when a role is *not* involved in a global
choice, we merge that role's projected local types across the branches. The merge operator is
partial:

- For **external choice** (`recv` / branching), merge unions labels and merges shared continuations.
- For **internal choice** (`send` / selection), merge is defined only when both sides have the same
  labels (a role cannot be forced to choose different outgoing labels based on an unseen choice).

This file proves algebraic laws that justify folding merge across multiple branch projections.

## Claims

- `MergeSelf`: merging a type with itself succeeds and returns a canonicalized form.
- `MergeCommutative`: merge is commutative.
- `MergeAssociative`: 3-way merge is associative/commutative (in `Option` form).
-/

namespace Rumpsteak.Proofs.Projection.Merging

open Rumpsteak.Protocol.LocalTypeR
open Rumpsteak.Protocol.GlobalType (Label)
open Rumpsteak.Protocol.ProjectionR

attribute [local instance] boolRelToRel

/-! ## Canonical Form -/

/- Canonicalize a local type by sorting every branch list (and recursively canonicalizing
   continuations). This matches the ordering used internally by `LocalTypeR.merge`. -/
/-! ### Termination helpers -/

private theorem sizeOf_cons {α : Type} [SizeOf α] (x : α) (l : List α) :
    sizeOf (x :: l) = 1 + sizeOf x + sizeOf l := by
  simp [sizeOf, List._sizeOf_1]

private theorem sizeOf_prod {α β : Type} [SizeOf α] [SizeOf β] (a : α) (b : β) :
    sizeOf (a, b) = 1 + sizeOf a + sizeOf b := by
  simp [sizeOf, Prod._sizeOf_1]

private theorem sizeOf_snd_lt_prod {α β : Type} [SizeOf α] [SizeOf β] (a : α) (b : β) :
    sizeOf b < sizeOf (a, b) := by
  have hk : 0 < 1 + sizeOf a := by
    simpa [Nat.one_add] using (Nat.succ_pos (sizeOf a))
  have h : sizeOf b < (1 + sizeOf a) + sizeOf b :=
    Nat.lt_add_of_pos_left (n := sizeOf b) (k := 1 + sizeOf a) hk
  simpa [sizeOf_prod] using h

private theorem sizeOf_head_lt_cons {α : Type} [SizeOf α] (x : α) (l : List α) :
    sizeOf x < sizeOf (x :: l) := by
  have h1 : sizeOf x < 1 + sizeOf x := by
    simpa [Nat.one_add] using (Nat.lt_succ_self (sizeOf x))
  have h2 : 1 + sizeOf x ≤ 1 + sizeOf x + sizeOf l := Nat.le_add_right _ _
  have h : sizeOf x < 1 + sizeOf x + sizeOf l := Nat.lt_of_lt_of_le h1 h2
  simpa [sizeOf_cons] using h

private theorem sizeOf_tail_lt_cons {α : Type} [SizeOf α] (x : α) (l : List α) :
    sizeOf l < sizeOf (x :: l) := by
  have hk : 0 < 1 + sizeOf x := by
    simpa [Nat.one_add] using (Nat.succ_pos (sizeOf x))
  have h : sizeOf l < (1 + sizeOf x) + sizeOf l :=
    Nat.lt_add_of_pos_left (n := sizeOf l) (k := 1 + sizeOf x) hk
  simpa [sizeOf_cons] using h

private theorem sizeOf_list_eq_of_perm {α : Type} [SizeOf α] {l1 l2 : List α} (p : l1.Perm l2) :
    sizeOf l1 = sizeOf l2 := by
  induction p with
  | nil =>
    simp [sizeOf, List._sizeOf_1]
  | cons x p ih =>
    simpa [sizeOf_cons, ih, Nat.add_assoc]
  | swap x y l =>
    simp [sizeOf_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | trans p1 p2 ih1 ih2 =>
    exact ih1.trans ih2

@[simp] private theorem sizeOf_sortBranches (bs : List (Label × LocalTypeR)) :
    sizeOf (LocalTypeR.sortBranches bs) = sizeOf bs := by
  have p : (LocalTypeR.sortBranches bs).Perm bs := by
    simpa [LocalTypeR.sortBranches] using (List.mergeSort_perm bs LocalTypeR.branchLe)
  simpa using sizeOf_list_eq_of_perm p

private theorem add_lt_add_succ_succ (a b : Nat) : a + b < a + 1 + (b + 1) := by
  have h1 : a + b < a + (b + 1) := by
    exact Nat.add_lt_add_left (Nat.lt_succ_self b) _
  have h2 : a + (b + 1) ≤ a + 1 + (b + 1) := by
    exact Nat.add_le_add_right (Nat.le_succ a) _
  exact Nat.lt_of_lt_of_le h1 h2

private theorem add_lt_add_succ_succ' {a b : Nat} : a + b < a + 1 + (b + 1) :=
  add_lt_add_succ_succ a b

/-! ### Canonicalization -/

mutual
  /-- Canonicalize a local type by sorting branch lists and canonicalizing continuations. -/
  def canonical (t : LocalTypeR) : LocalTypeR :=
    match t with
    | .end => .end
    | .var v => .var v
    | .mu v body => .mu v (canonical body)
    | .send partner branches =>
      let bs := LocalTypeR.sortBranches branches
      .send partner (canonicalBranches bs)
    | .recv partner branches =>
      let bs := LocalTypeR.sortBranches branches
      .recv partner (canonicalBranches bs)
  termination_by sizeOf t
  decreasing_by
    all_goals
      simp_wf
      apply Nat.lt_add_of_pos_left
      simp [Nat.one_add]

  /-- Canonicalize every continuation in a branch list, preserving order. -/
  def canonicalBranches (bs : List (Label × LocalTypeR)) : List (Label × LocalTypeR) :=
    match bs with
    | [] => []
    | (l, t) :: rest => (l, canonical t) :: canonicalBranches rest
  termination_by sizeOf bs
  decreasing_by
    all_goals
      first
        | -- Recursive call to `canonical` on the continuation.
          have h1 : sizeOf t < sizeOf (l, t) := sizeOf_snd_lt_prod l t
          have h2 : sizeOf (l, t) < sizeOf ((l, t) :: rest) := sizeOf_head_lt_cons (l, t) rest
          exact Nat.lt_trans h1 h2
        | -- Recursive call to `canonicalBranches` on the tail.
          exact sizeOf_tail_lt_cons (l, t) rest
end

private theorem canonicalBranches_eq_map (bs : List (Label × LocalTypeR)) :
    canonicalBranches bs = bs.map (fun b => (b.1, canonical b.2)) := by
  induction bs with
  | nil =>
    simp [canonicalBranches]
  | cons head tail ih =>
    cases head with
    | mk l t =>
      simp [canonicalBranches, ih]

/-! ## Claims -/

/-- Self-merge always succeeds and returns the canonical form.
    Formal: ∀ T, T.merge T = some (canonical T). -/
def MergeSelf : Prop :=
  ∀ (t : LocalTypeR), LocalTypeR.merge t t = some (canonical t)

/-- Merge is commutative.
    Formal: ∀ T1 T2, T1.merge T2 = T2.merge T1. -/
def MergeCommutative : Prop :=
  ∀ (t1 t2 : LocalTypeR), LocalTypeR.merge t1 t2 = LocalTypeR.merge t2 t1

/-- Merge is associative (3-way commutative form).
    Formal: ∀ T1 T2 T3, (T1.merge T2).bind (·.merge T3) = (T2.merge T3).bind (T1.merge ·). -/
def MergeAssociative : Prop :=
  ∀ (t1 t2 t3 : LocalTypeR),
    (LocalTypeR.merge t1 t2).bind (fun m => LocalTypeR.merge m t3) =
    (LocalTypeR.merge t2 t3).bind (fun m => LocalTypeR.merge t1 m)

/-- Claims bundle for merge properties. -/
structure Claims where
  /-- Self-merge returns the canonical form. -/
  mergeSelf : MergeSelf
  /-- Merge is commutative. -/
  mergeCommutative : MergeCommutative
  /-- Merge is associative (3-way commutative form). -/
  mergeAssociative : MergeAssociative

/-! ## Proofs -/

/-! ### Helper lemmas -/

private def AllBranches (P : LocalTypeR → Prop) (bs : List (Label × LocalTypeR)) : Prop :=
  ∀ b ∈ bs, P b.2

private theorem AllBranches.nil (P : LocalTypeR → Prop) : AllBranches P [] := by
  intro b hb
  cases hb

private theorem AllBranches.cons
    (P : LocalTypeR → Prop)
    (head : Label × LocalTypeR)
    (tail : List (Label × LocalTypeR))
    (hHead : P head.2)
    (hTail : AllBranches P tail) :
    AllBranches P (head :: tail) := by
  intro b hb
  cases hb with
  | head =>
    simpa using hHead
  | tail _ hbTail =>
    exact hTail b hbTail

private theorem AllBranches.of_perm
    (P : LocalTypeR → Prop)
    {bs1 bs2 : List (Label × LocalTypeR)}
    (hperm : bs1.Perm bs2)
    (h : AllBranches P bs2) :
    AllBranches P bs1 := by
  intro b hb
  have hb' : b ∈ bs2 := (List.Perm.mem_iff hperm).1 hb
  exact h b hb'

private theorem pairwise_map_snd
    (bs : List (Label × LocalTypeR))
    (f : LocalTypeR → LocalTypeR)
    (h : bs.Pairwise LocalTypeR.branchLe) :
    (bs.map fun b => (b.1, f b.2)).Pairwise LocalTypeR.branchLe := by
  induction bs with
  | nil =>
    simpa using h
  | cons head tail ih =>
    cases h with
    | cons hHead hTail =>
      apply List.Pairwise.cons
      · intro b hb
        rcases List.mem_map.1 hb with ⟨a, ha, rfl⟩
        -- `branchLe` depends only on label name, and mapping preserves labels.
        simpa using hHead a ha
      · exact ih hTail

private theorem mergeRecvSorted_comm
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

private theorem mergeSendSorted_comm :
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

private theorem mergeSendSorted_self
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

private theorem mergeRecvSorted_self
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

/-! ### Branch sorting lemmas -/

private theorem branchLe_trans (a b c : Label × LocalTypeR) :
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

private theorem branchLe_total (a b : Label × LocalTypeR) :
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

private theorem pairwise_sortBranches (bs : List (Label × LocalTypeR)) :
    (LocalTypeR.sortBranches bs).Pairwise LocalTypeR.branchLe := by
  simpa [LocalTypeR.sortBranches] using
    (List.sorted_mergeSort (le := LocalTypeR.branchLe)
      (trans := branchLe_trans) (total := branchLe_total) bs)

private theorem sortBranches_eq_of_pairwise
    (bs : List (Label × LocalTypeR))
    (h : bs.Pairwise LocalTypeR.branchLe) :
    LocalTypeR.sortBranches bs = bs := by
  simpa [LocalTypeR.sortBranches] using
    (List.mergeSort_of_sorted (le := LocalTypeR.branchLe) (l := bs) h)

theorem merge_self : MergeSelf := by
  intro t
  -- Use the nested recursor (Lean 4.24 `induction` does not support nested inductives).
  refine LocalTypeR.recOn
    (motive_1 := fun t => LocalTypeR.merge t t = some (canonical t))
    (motive_2 := fun bs => AllBranches (fun t => LocalTypeR.merge t t = some (canonical t)) bs)
    (motive_3 := fun b => LocalTypeR.merge b.2 b.2 = some (canonical b.2))
    t
    (by simp [canonical, LocalTypeR.merge])
    (fun partner branches ihBranches => by
      -- Canonicalization matches the internal sorting performed by `mergeSendBranches`.
      let bs := LocalTypeR.sortBranches branches
      have hperm : bs.Perm branches := by
        simpa [bs, LocalTypeR.sortBranches] using (List.mergeSort_perm branches LocalTypeR.branchLe)
      have ihSorted :
          AllBranches (fun t => LocalTypeR.merge t t = some (canonical t)) bs :=
        AllBranches.of_perm _ hperm ihBranches
      have hSendSorted :
          LocalTypeR.mergeSendSorted bs bs =
            some (bs.map fun (l, t) => (l, canonical t)) :=
        mergeSendSorted_self bs ihSorted
      simp [canonical, canonicalBranches_eq_map, LocalTypeR.merge, bs, hSendSorted])
    (fun partner branches ihBranches => by
      let bs := LocalTypeR.sortBranches branches
      have hperm : bs.Perm branches := by
        simpa [bs, LocalTypeR.sortBranches] using (List.mergeSort_perm branches LocalTypeR.branchLe)
      have ihSorted :
          AllBranches (fun t => LocalTypeR.merge t t = some (canonical t)) bs :=
        AllBranches.of_perm _ hperm ihBranches
      have hRecvSorted :
          LocalTypeR.mergeRecvSorted bs bs =
            some (bs.map fun (l, t) => (l, canonical t)) :=
        mergeRecvSorted_self bs ihSorted
      have hPair : bs.Pairwise LocalTypeR.branchLe := by
        simpa [bs] using pairwise_sortBranches branches
      have hPairMap :
          (bs.map fun b => (b.1, canonical b.2)).Pairwise LocalTypeR.branchLe :=
        pairwise_map_snd bs canonical hPair
      have hSort : LocalTypeR.sortBranches (bs.map fun b => (b.1, canonical b.2)) =
          (bs.map fun b => (b.1, canonical b.2)) :=
        sortBranches_eq_of_pairwise _ hPairMap
      simp [canonical, canonicalBranches_eq_map, LocalTypeR.merge, bs, hRecvSorted, hSort])
    (fun v body ihBody => by
      simp [canonical, LocalTypeR.merge, ihBody])
    (fun v => by simp [canonical, LocalTypeR.merge])
    (AllBranches.nil _)
    (fun head tail ihHead ihTail =>
      AllBranches.cons _ head tail ihHead ihTail)
    (fun _fst _snd ihSnd => ihSnd)

theorem merge_commutative : MergeCommutative := by
  intro t1 t2
  -- Structural case split on both types.
  have ht1 :
      (∀ t1 : LocalTypeR, ∀ t2 : LocalTypeR, LocalTypeR.merge t1 t2 = LocalTypeR.merge t2 t1) := by
    intro t1
    refine LocalTypeR.recOn
      (motive_1 := fun t1 => ∀ t2, LocalTypeR.merge t1 t2 = LocalTypeR.merge t2 t1)
      (motive_2 := fun bs =>
        AllBranches (fun t => ∀ u, LocalTypeR.merge t u = LocalTypeR.merge u t) bs)
      (motive_3 := fun b => ∀ u, LocalTypeR.merge b.2 u = LocalTypeR.merge u b.2)
      t1
      (by
        intro t2
        cases t2 <;> simp [LocalTypeR.merge])
      (fun partner branches ihBranches => by
        intro t2
        cases t2 with
        | send partner2 branches2 =>
          by_cases hPartner : partner = partner2
          · subst hPartner
            -- Reduce to commutativity of send-branch merging.
            let bs1 := LocalTypeR.sortBranches branches
            let bs2 := LocalTypeR.sortBranches branches2
            have hperm : bs1.Perm branches := by
              simpa [bs1, LocalTypeR.sortBranches] using (List.mergeSort_perm branches LocalTypeR.branchLe)
            have ihSorted :
                AllBranches (fun t => ∀ u, LocalTypeR.merge t u = LocalTypeR.merge u t) bs1 :=
              AllBranches.of_perm _ hperm ihBranches
            have hSend :
                LocalTypeR.mergeSendSorted bs1 bs2 = LocalTypeR.mergeSendSorted bs2 bs1 := by
              exact mergeSendSorted_comm bs1 bs2 ihSorted
            simp [LocalTypeR.merge, bs1, bs2, hSend]
          · have hPartner' : partner2 ≠ partner := fun h => hPartner (Eq.symm h)
            simp [LocalTypeR.merge, hPartner, hPartner']
        | _ =>
          simp [LocalTypeR.merge])
      (fun partner branches ihBranches => by
        intro t2
        cases t2 with
        | recv partner2 branches2 =>
          by_cases hPartner : partner = partner2
          · subst hPartner
            -- Reduce to commutativity of recv-branch merging.
            let bs1 := LocalTypeR.sortBranches branches
            let bs2 := LocalTypeR.sortBranches branches2
            have hperm : bs1.Perm branches := by
              simpa [bs1, LocalTypeR.sortBranches] using (List.mergeSort_perm branches LocalTypeR.branchLe)
            have ihSorted :
                AllBranches (fun t => ∀ u, LocalTypeR.merge t u = LocalTypeR.merge u t) bs1 :=
              AllBranches.of_perm _ hperm ihBranches
            have hRecv :
                LocalTypeR.mergeRecvSorted bs1 bs2 = LocalTypeR.mergeRecvSorted bs2 bs1 :=
              by
                exact mergeRecvSorted_comm bs1 bs2 ihSorted
            simp [LocalTypeR.merge, bs1, bs2, hRecv]
          · have hPartner' : partner2 ≠ partner := fun h => hPartner (Eq.symm h)
            simp [LocalTypeR.merge, hPartner, hPartner']
        | _ =>
          simp [LocalTypeR.merge])
      (fun v body ihBody => by
        intro t2
        cases t2 with
        | mu v2 body2 =>
          by_cases h : v = v2
          · subst h
            have hBody : LocalTypeR.merge body body2 = LocalTypeR.merge body2 body := ihBody body2
            simp [LocalTypeR.merge, hBody]
          · have h' : v2 ≠ v := fun hv => h hv.symm
            simp [LocalTypeR.merge, h, h']
        | _ =>
          simp [LocalTypeR.merge])
      (fun v => by
        intro t2
        cases t2 with
        | var a =>
          by_cases h : v = a
          · subst h
            simp [LocalTypeR.merge]
          · have h' : a ≠ v := fun h2 => h h2.symm
            simp [LocalTypeR.merge, h, h']
        | _ =>
          simp [LocalTypeR.merge])
      (AllBranches.nil _)
      (fun head tail ihHead ihTail =>
        AllBranches.cons _ head tail ihHead ihTail)
      (fun _fst _snd ihSnd => ihSnd)
  exact ht1 t1 t2

/-! ### Associativity helper lemmas -/

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
      first
        | -- Left list shrinks.
          have h1 : tail1.length < bs1.length := by
            simpa [hbs1] using Nat.lt_succ_self tail1.length
          have hlt : tail1.length + bs2.length < bs1.length + bs2.length :=
            Nat.add_lt_add_right h1 bs2.length
          simpa [hbs2] using hlt
        | -- Right list shrinks.
          have h2 : tail2.length < bs2.length := by
            simpa [hbs2] using Nat.lt_succ_self tail2.length
          have hlt : bs1.length + tail2.length < bs1.length + bs2.length :=
            Nat.add_lt_add_left bs1.length h2
          simpa [hbs1] using hlt
        | -- Both lists shrink.
          have h1 : tail1.length < bs1.length := by
            simpa [hbs1] using Nat.lt_succ_self tail1.length
          have h2 : tail2.length < bs2.length := by
            simpa [hbs2] using Nat.lt_succ_self tail2.length
          exact Nat.add_lt_add h1 h2

private theorem mergeRecvSorted_pairwise
    {bs1 bs2 rest : List (Label × LocalTypeR)}
    (hSorted1 : bs1.Pairwise LocalTypeR.branchLe)
    (hSorted2 : bs2.Pairwise LocalTypeR.branchLe)
    (h : LocalTypeR.mergeRecvSorted bs1 bs2 = some rest) :
    rest.Pairwise LocalTypeR.branchLe := by
  cases bs1 with
  | nil =>
    have hEq : bs2 = rest := by
      simpa [LocalTypeR.mergeRecvSorted] using h
    simpa [hEq] using hSorted2
  | cons head1 tail1 =>
    cases bs2 with
    | nil =>
      have hEq : head1 :: tail1 = rest := by
        simpa [LocalTypeR.mergeRecvSorted] using h
      simpa [hEq] using hSorted1
    | cons head2 tail2 =>
      cases head1 with
      | mk l1 c1 =>
        cases head2 with
        | mk l2 c2 =>
          cases hSorted1 with
          | cons hRel1 hTail1 =>
            cases hSorted2 with
            | cons hRel2 hTail2 =>
              by_cases h12 : l1.name < l2.name
              · have h21 : ¬ l2.name < l1.name := String.lt_asymm h12
                cases hRest : LocalTypeR.mergeRecvSorted tail1 ((l2, c2) :: tail2) with
                | none =>
                  cases (by
                    simpa [LocalTypeR.mergeRecvSorted, h12, h21, hRest] using h : False)
                | some restTail =>
                  have hEq : (l1, c1) :: restTail = rest := by
                    simpa [LocalTypeR.mergeRecvSorted, h12, h21, hRest] using h
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
                        simpa [LocalTypeR.mergeRecvSorted, h12, h21, hRest] using h : False)
                  | some restTail =>
                    have hEq : (l2, c2) :: restTail = rest := by
                      simpa [LocalTypeR.mergeRecvSorted, h12, h21, hRest] using h
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
                          simpa [LocalTypeR.mergeRecvSorted, h12, h21, hCont] using h : False)
                    | some mergedCont =>
                      cases hRest : LocalTypeR.mergeRecvSorted tail1 tail2 with
                      | none =>
                        cases (by
                          simpa [LocalTypeR.mergeRecvSorted, h12, h21, hCont, hRest] using h : False)
                      | some restTail =>
                        have hEq : (l1, mergedCont) :: restTail = rest := by
                          simpa [LocalTypeR.mergeRecvSorted, h12, h21, hCont, hRest] using h
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
                      simpa [LocalTypeR.mergeRecvSorted, h12, h21, hEqLab] using h : False)
  termination_by bs1.length + bs2.length
  decreasing_by
    all_goals
      simp_wf
      simp (config := { failIfUnchanged := false })
      first
        | -- Left list shrinks.
          simpa using Nat.add_lt_add_right (a := tail1.length) (b := (head1 :: tail1).length)
            (by simp) _
        | -- Right list shrinks.
          simpa using Nat.add_lt_add_left (c := (head1 :: tail1).length)
            (a := tail2.length) (b := (head2 :: tail2).length) (by simp)
        | -- Both lists shrink.
          have h1 : tail1.length < (head1 :: tail1).length := by
            simpa using Nat.lt_succ_self tail1.length
          have h2 : tail2.length < (head2 :: tail2).length := by
            simpa using Nat.lt_succ_self tail2.length
          exact Nat.add_lt_add h1 h2

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
                  -- Reassemble `Pairwise` for the whole result.
                  rw [← hEq]
                  exact List.Pairwise.cons hHeadRel hTailPair
            · cases (by simpa [LocalTypeR.mergeSendSorted, hLabel] using h : False)

private def MergeAssocAt (t : LocalTypeR) : Prop :=
  ∀ u v,
    (LocalTypeR.merge t u).bind (fun m => LocalTypeR.merge m v) =
    (LocalTypeR.merge u v).bind (fun m => LocalTypeR.merge t m)

private theorem option_bind_comm {α β γ : Type} (oa : Option α) (ob : Option β) (f : α → β → Option γ) :
    oa.bind (fun a => ob.bind (fun b => f a b)) =
    ob.bind (fun b => oa.bind (fun a => f a b)) := by
  cases oa <;> cases ob <;> rfl

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
        -- LHS is `none`; show RHS is `none` by case splitting on the first merge.
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
        -- RHS is `none`; show LHS is `none` by case splitting on the first merge.
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
                      -- Expand both merges and reassociate binds to expose the head+tail triple merges.
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

                  -- Finish by rewriting both sides to the canonical forms and using the IH equalities.
                  simpa [hLhs, hRhs, hHeadEq, hTailEq]
                · -- Head labels match in bs1/bs2 but not with bs3: both sides fail.
                  have hRhsNone : LocalTypeR.mergeSendSorted ((l1, c2) :: tail2) ((l3, c3) :: tail3) = none := by
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
              · -- Head labels differ between bs1 and bs2: both sides fail.
                have hLhsNone : LocalTypeR.mergeSendSorted ((l1, c1) :: tail) ((l2, c2) :: tail2) = none := by
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

private theorem mergeRecvSorted_assoc :
    ∀ (bs1 bs2 bs3 : List (Label × LocalTypeR)),
      AllBranches MergeAssocAt bs1 →
      (LocalTypeR.mergeRecvSorted bs1 bs2).bind (fun m12 => LocalTypeR.mergeRecvSorted m12 bs3) =
      (LocalTypeR.mergeRecvSorted bs2 bs3).bind (fun m23 => LocalTypeR.mergeRecvSorted bs1 m23) := by
  intro bs1 bs2 bs3 ih
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
                  -- Head of `bs1` is the smallest: peel it off and use IH on the tail.
                  have hRec :=
                    mergeRecvSorted_assoc tail1 ((l2, c2) :: tail2) ((l3, c3) :: tail3) ihTail1
                  -- Both sides build the same head and reduce to the recursive equation on the tails.
                  simpa [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, Option.bind_assoc, hRec]
                · by_cases h31 : l3.name < l1.name
                  · -- Head of `bs3` is the smallest: peel it off and recurse on `bs3` tail.
                    have hRec :=
                      mergeRecvSorted_assoc ((l1, c1) :: tail1) ((l2, c2) :: tail2) tail3 ih
                    -- `l3.name < l2.name` follows from `l3.name < l1.name < l2.name`.
                    have h32 : l3.name < l2.name := Std.lt_of_lt_of_le h31 (Std.le_of_lt h12)
                    have h23 : ¬ l2.name < l3.name := String.lt_asymm h32
                    simpa [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, h32, h23, Option.bind_assoc, hRec]
                  · -- `l1.name` and `l3.name` are equal (since neither is less): merge them.
                    have h32 : l3.name < l2.name := by
                      -- From `¬ l1.name < l3.name`, we can derive `l3.name ≤ l1.name`;
                      -- then `l3.name < l2.name` follows from `l1.name < l2.name`.
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
                        simp [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, h32, h23, hCont]
                      | some merged13 =>
                        have hRec :=
                          mergeRecvSorted_assoc tail1 ((l2, c2) :: tail2) tail3 ihTail1
                        -- Both sides merge the shared label `l1` (from bs1/bs3) and recurse on tails.
                        simpa [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, h32, h23, hCont, Option.bind_assoc, hRec]
                    · -- Label mismatch at equal name: both sides fail.
                      have hEq13' : l3 ≠ l1 := fun h => hEq13 h.symm
                      simp [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, h32, h23, hEq13, hEq13']
              · by_cases h21 : l2.name < l1.name
                · by_cases h23 : l2.name < l3.name
                  · -- Head of `bs2` is the smallest: peel it off and recurse on `bs2` tail.
                    have hRec :=
                      mergeRecvSorted_assoc ((l1, c1) :: tail1) tail2 ((l3, c3) :: tail3) ih
                    have h32 : ¬ l3.name < l2.name := String.lt_asymm h23
                    simpa [LocalTypeR.mergeRecvSorted, h12, h21, h23, h32, Option.bind_assoc, hRec]
                  · by_cases h32 : l3.name < l2.name
                    · -- Head of `bs3` is the smallest: peel it off and recurse on `bs3` tail.
                      have hRec :=
                        mergeRecvSorted_assoc ((l1, c1) :: tail1) ((l2, c2) :: tail2) tail3 ih
                      -- `l3.name < l1.name` from `l3.name < l2.name < l1.name`.
                      have h31 : l3.name < l1.name := Std.lt_of_lt_of_le h32 (Std.le_of_lt h21)
                      have h13 : ¬ l1.name < l3.name := String.lt_asymm h31
                      simpa [LocalTypeR.mergeRecvSorted, h12, h21, h23, h32, h31, h13, Option.bind_assoc, hRec]
                    · -- `l2.name` and `l3.name` are equal: merge them.
                      have h31 : l3.name < l1.name := by
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
                          simp [LocalTypeR.mergeRecvSorted, h12, h21, h23, h32, hCont]
                        | some merged23 =>
                          have hRec :=
                            mergeRecvSorted_assoc ((l1, c1) :: tail1) tail2 tail3 ih
                          simpa [LocalTypeR.mergeRecvSorted, h12, h21, h23, h32, hCont, Option.bind_assoc, hRec]
                      · have hEq23' : l3 ≠ l2 := fun h => hEq23 h.symm
                        simp [LocalTypeR.mergeRecvSorted, h12, h21, h23, h32, hEq23, hEq23']
                · -- `l1.name` and `l2.name` are equal: merge them (or fail).
                  by_cases hEq12 : l1 = l2
                  · subst hEq12
                    by_cases h13 : l1.name < l3.name
                    · have h31 : ¬ l3.name < l1.name := String.lt_asymm h13
                      cases hCont : LocalTypeR.merge c1 c2 with
                      | none =>
                        simp [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, hCont]
                      | some merged12 =>
                        have hRec := mergeRecvSorted_assoc tail1 tail2 ((l3, c3) :: tail3) ihTail1
                        simpa [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, hCont, Option.bind_assoc, hRec]
                    · by_cases h31 : l3.name < l1.name
                      · -- Head of `bs3` is smaller.
                        have h32 : l3.name < l2.name := by
                          -- `l3.name < l1.name = l2.name`
                          simpa using h31
                        have h23 : ¬ l2.name < l3.name := String.lt_asymm h32
                        have hRec := mergeRecvSorted_assoc ((l1, c1) :: tail1) ((l2, c2) :: tail2) tail3 ih
                        simpa [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, h32, h23, Option.bind_assoc, hRec]
                      · -- All head names are equal.
                        by_cases hEq13 : l1 = l3
                        · subst hEq13
                          cases hCont12 : LocalTypeR.merge c1 c2 with
                          | none =>
                            simp [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, hCont12]
                          | some merged12 =>
                            cases hCont23 : LocalTypeR.merge c2 c3 with
                            | none =>
                              simp [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, hCont23]
                            | some merged23 =>
                              -- Use associativity of continuation merge at `c1`.
                              have hContAssoc :
                                  (LocalTypeR.merge c1 c2).bind (fun m12 => LocalTypeR.merge m12 c3) =
                                  (LocalTypeR.merge c2 c3).bind (fun m23 => LocalTypeR.merge c1 m23) := by
                                simpa [MergeAssocAt] using ihHead c2 c3
                              have hRec := mergeRecvSorted_assoc tail1 tail2 tail3 ihTail1
                              simpa [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, Option.bind_assoc, hContAssoc, hRec]
                        · have hEq13' : l3 ≠ l1 := fun h => hEq13 h.symm
                          simp [LocalTypeR.mergeRecvSorted, h12, h21, h13, h31, hEq13, hEq13']
                  · have hEq12' : l2 ≠ l1 := fun h => hEq12 h.symm
                    simp [LocalTypeR.mergeRecvSorted, h12, h21, hEq12, hEq12']
  termination_by sizeOf bs1 + sizeOf bs2 + sizeOf bs3
  decreasing_by
    all_goals
      simp_wf
      simp (config := { failIfUnchanged := false })
      first
        | -- Left list shrinks.
          simpa [*] using (sizeOf_tail_lt_cons head1 tail1)
        | -- Middle list shrinks.
          simpa [*] using (sizeOf_tail_lt_cons head2 tail2)
        | -- Right list shrinks.
          simpa [*] using (sizeOf_tail_lt_cons head3 tail3)
        | -- Both lists shrink.
          apply Nat.add_lt_add_left (sizeOf_tail_lt_cons head3 tail3) (sizeOf ((head1 :: tail1)) + sizeOf ((head2 :: tail2)))

theorem merge_associative : MergeAssociative := by
  intro t1 t2 t3
  have ht1 : MergeAssocAt t1 := by
    -- Nested recursor for `LocalTypeR` + branch lists.
    refine LocalTypeR.recOn
      (motive_1 := fun t => MergeAssocAt t)
      (motive_2 := fun bs => AllBranches MergeAssocAt bs)
      (motive_3 := fun b => MergeAssocAt b.2)
      t1
      (by
        intro u v
        cases u <;> cases v <;> simp [MergeAssocAt, LocalTypeR.merge])
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

                -- Unfold `merge` and rewrite away the redundant re-sorting of intermediate results.
                -- (The first merge returns a sorted branch list; the second merge sorts again.)
                -- After normalization, this is exactly `mergeSendSorted_assoc`.
                --
                -- We do this by rewriting `sortBranches m12 = m12` whenever `m12` is a successful merge result.
                have hL :
                    (LocalTypeR.merge (.send partner branches1) (.send partner branches2)).bind
                        (fun m => LocalTypeR.merge m (.send partner branches3)) =
                      (LocalTypeR.mergeSendSorted bs1 bs2).bind (fun m12 =>
                        (LocalTypeR.mergeSendSorted m12 bs3).bind (fun m123 =>
                          some (.send partner m123))) := by
                  -- Expand the two merges and use `hSort12` to remove re-sorting.
                  simp [LocalTypeR.merge, bs1, bs2, bs3, Option.bind_assoc]
                  -- `simp` leaves `sortBranches` on the intermediate branch list; remove it using `hSort12`.
                  · intro m12 hm12
                    simp [hSort12 hm12]

                have hR :
                    (LocalTypeR.merge (.send partner branches2) (.send partner branches3)).bind
                        (fun m => LocalTypeR.merge (.send partner branches1) m) =
                      (LocalTypeR.mergeSendSorted bs2 bs3).bind (fun m23 =>
                        (LocalTypeR.mergeSendSorted bs1 m23).bind (fun m123 =>
                          some (.send partner m123))) := by
                  simp [LocalTypeR.merge, bs1, bs2, bs3, Option.bind_assoc]
                  · intro m23 hm23
                    simp [hSort23 hm23]

                -- Finish by rewriting both sides via branch-level associativity.
                -- (`some (.send partner ·)` is applied uniformly.)
                -- Note: `Option.bind` associativity is handled by `Option.bind_assoc` in the expansions above.
                simpa [hL, hR, Option.bind_assoc] using congrArg (fun x =>
                  x.bind (fun m123 => some (.send partner m123))) hAssoc
              · have hP13' : partner3 ≠ partner := fun h => hP13 h.symm
                simp [MergeAssocAt, LocalTypeR.merge, hP13, hP13']
            · have hP12' : partner2 ≠ partner := fun h => hP12 h.symm
              simp [MergeAssocAt, LocalTypeR.merge, hP12, hP12']
          | _ =>
            simp [MergeAssocAt, LocalTypeR.merge]
        | _ =>
          cases v <;> simp [MergeAssocAt, LocalTypeR.merge])
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

                -- Normalize both sides to branch-level merges, using that `mergeRecvSorted` results are already
                -- sorted (so the extra `sortBranches` in `merge` is redundant).
                have hL :
                    (LocalTypeR.merge (.recv partner branches1) (.recv partner branches2)).bind
                        (fun m => LocalTypeR.merge m (.recv partner branches3)) =
                      (LocalTypeR.mergeRecvSorted bs1 bs2).bind (fun m12 =>
                        (LocalTypeR.mergeRecvSorted m12 bs3).bind (fun m123 =>
                          some (.recv partner m123))) := by
                  simp [LocalTypeR.merge, bs1, bs2, bs3, Option.bind_assoc]
                  · intro m12 hm12
                    simp [hSort12 hm12]

                have hR :
                    (LocalTypeR.merge (.recv partner branches2) (.recv partner branches3)).bind
                        (fun m => LocalTypeR.merge (.recv partner branches1) m) =
                      (LocalTypeR.mergeRecvSorted bs2 bs3).bind (fun m23 =>
                        (LocalTypeR.mergeRecvSorted bs1 m23).bind (fun m123 =>
                          some (.recv partner m123))) := by
                  simp [LocalTypeR.merge, bs1, bs2, bs3, Option.bind_assoc]
                  · intro m23 hm23
                    simp [hSort23 hm23]

                simpa [hL, hR, Option.bind_assoc] using congrArg (fun x =>
                  x.bind (fun m123 => some (.recv partner m123))) hAssoc
              · have hP13' : partner3 ≠ partner := fun h => hP13 h.symm
                simp [MergeAssocAt, LocalTypeR.merge, hP13, hP13']
            · have hP12' : partner2 ≠ partner := fun h => hP12 h.symm
              simp [MergeAssocAt, LocalTypeR.merge, hP12, hP12']
          | _ =>
            simp [MergeAssocAt, LocalTypeR.merge]
        | _ =>
          cases v <;> simp [MergeAssocAt, LocalTypeR.merge])
      (fun v body ihBody => by
        intro u w
        cases u <;> cases w <;> simp [MergeAssocAt, LocalTypeR.merge, ihBody])
      (fun v => by
        intro u w
        cases u with
        | var a =>
          cases w with
          | var b =>
            by_cases hva : v = a
            · subst hva
              by_cases hab : a = b
              · subst hab
                simp [MergeAssocAt, LocalTypeR.merge]
              · have hba : b ≠ a := fun h => hab h.symm
                simp [MergeAssocAt, LocalTypeR.merge, hab, hba]
            · have hav : a ≠ v := fun h => hva h.symm
              by_cases hab : a = b
              · subst hab
                simp [MergeAssocAt, LocalTypeR.merge, hva, hav]
              · have hba : b ≠ a := fun h => hab h.symm
                simp [MergeAssocAt, LocalTypeR.merge, hva, hav, hab, hba]
          | _ =>
            cases w <;> simp [MergeAssocAt, LocalTypeR.merge]
        | _ =>
          cases w <;> simp [MergeAssocAt, LocalTypeR.merge])
      (AllBranches.nil _)
      (fun head tail ihHead ihTail =>
        AllBranches.cons _ head tail ihHead ihTail)
      (fun _fst _snd ihSnd => ihSnd)
  simpa [MergeAssociative, MergeAssocAt] using ht1 t2 t3

/-- Construct the claims bundle with all proven properties. -/
def claims : Claims := ⟨merge_self, merge_commutative, merge_associative⟩

end Rumpsteak.Proofs.Projection.Merging
