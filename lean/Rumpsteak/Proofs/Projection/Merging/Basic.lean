import Rumpsteak.Protocol.LocalTypeR
import Rumpsteak.Protocol.ProjectionR
import Init.Data.List.Sort.Lemmas
import Init.Data.Order.Lemmas
import Init.Data.Option.Lemmas

/-! # Rumpsteak.Proofs.Projection.Merging.Basic

Basic infrastructure for merge proofs: termination helpers, canonicalization,
and claim definitions.

## Overview

This module provides shared infrastructure for the merge property proofs:
- Size/termination helpers for recursive definitions
- Canonical form computation for local types
- AllBranches predicate for inductive proofs over branch lists
- Claim type definitions

## Expose

- `canonical`: Canonicalizes a local type by sorting branches
- `MergeSelf`, `MergeCommutative`, `MergeAssociative`: Claim type definitions
- `Claims`: Bundle structure for all merge properties
- `AllBranches`: Predicate over branch lists
-/

namespace Rumpsteak.Proofs.Projection.Merging

open Rumpsteak.Protocol.LocalTypeR
open Rumpsteak.Protocol.GlobalType (Label)
open Rumpsteak.Protocol.ProjectionR

attribute [local instance] boolRelToRel

/-! ## Termination helpers -/

theorem sizeOf_cons {α : Type} [SizeOf α] (x : α) (l : List α) :
    sizeOf (x :: l) = 1 + sizeOf x + sizeOf l := by
  simp [sizeOf, List._sizeOf_1]

theorem sizeOf_prod {α β : Type} [SizeOf α] [SizeOf β] (a : α) (b : β) :
    sizeOf (a, b) = 1 + sizeOf a + sizeOf b := by
  simp [sizeOf, Prod._sizeOf_1]

theorem sizeOf_snd_lt_prod {α β : Type} [SizeOf α] [SizeOf β] (a : α) (b : β) :
    sizeOf b < sizeOf (a, b) := by
  have hk : 0 < 1 + sizeOf a := by
    simpa [Nat.one_add] using (Nat.succ_pos (sizeOf a))
  have h : sizeOf b < (1 + sizeOf a) + sizeOf b :=
    Nat.lt_add_of_pos_left (n := sizeOf b) (k := 1 + sizeOf a) hk
  simpa [sizeOf_prod] using h

theorem sizeOf_head_lt_cons {α : Type} [SizeOf α] (x : α) (l : List α) :
    sizeOf x < sizeOf (x :: l) := by
  have h1 : sizeOf x < 1 + sizeOf x := by
    simpa [Nat.one_add] using (Nat.lt_succ_self (sizeOf x))
  have h2 : 1 + sizeOf x ≤ 1 + sizeOf x + sizeOf l := Nat.le_add_right _ _
  have h : sizeOf x < 1 + sizeOf x + sizeOf l := Nat.lt_of_lt_of_le h1 h2
  simpa [sizeOf_cons] using h

theorem sizeOf_tail_lt_cons {α : Type} [SizeOf α] (x : α) (l : List α) :
    sizeOf l < sizeOf (x :: l) := by
  have hk : 0 < 1 + sizeOf x := by
    simpa [Nat.one_add] using (Nat.succ_pos (sizeOf x))
  have h : sizeOf l < (1 + sizeOf x) + sizeOf l :=
    Nat.lt_add_of_pos_left (n := sizeOf l) (k := 1 + sizeOf x) hk
  simpa [sizeOf_cons] using h

theorem sizeOf_list_eq_of_perm {α : Type} [SizeOf α] {l1 l2 : List α} (p : l1.Perm l2) :
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

@[simp] theorem sizeOf_sortBranches (bs : List (Label × LocalTypeR)) :
    sizeOf (LocalTypeR.sortBranches bs) = sizeOf bs := by
  have p : (LocalTypeR.sortBranches bs).Perm bs := by
    simpa [LocalTypeR.sortBranches] using (List.mergeSort_perm bs LocalTypeR.branchLe)
  simpa using sizeOf_list_eq_of_perm p

theorem add_lt_add_succ_succ (a b : Nat) : a + b < a + 1 + (b + 1) := by
  have h1 : a + b < a + (b + 1) := by
    exact Nat.add_lt_add_left (Nat.lt_succ_self b) _
  have h2 : a + (b + 1) ≤ a + 1 + (b + 1) := by
    exact Nat.add_le_add_right (Nat.le_succ a) _
  exact Nat.lt_of_lt_of_le h1 h2

theorem add_lt_add_succ_succ' {a b : Nat} : a + b < a + 1 + (b + 1) :=
  add_lt_add_succ_succ a b

/-! ## Canonicalization -/

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

theorem canonicalBranches_eq_map (bs : List (Label × LocalTypeR)) :
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

/-! ## AllBranches predicate -/

/-- A property holds for all continuations in a branch list. -/
def AllBranches (P : LocalTypeR → Prop) (bs : List (Label × LocalTypeR)) : Prop :=
  ∀ b ∈ bs, P b.2

theorem AllBranches.nil (P : LocalTypeR → Prop) : AllBranches P [] := by
  intro b hb
  cases hb

theorem AllBranches.cons
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

theorem AllBranches.of_perm
    (P : LocalTypeR → Prop)
    {bs1 bs2 : List (Label × LocalTypeR)}
    (hperm : bs1.Perm bs2)
    (h : AllBranches P bs2) :
    AllBranches P bs1 := by
  intro b hb
  have hb' : b ∈ bs2 := (List.Perm.mem_iff hperm).1 hb
  exact h b hb'

/-! ## Branch pairwise lemmas -/

theorem pairwise_map_snd
    (bs : List (Label × LocalTypeR))
    (f : LocalTypeR → LocalTypeR)
    (h : bs.Pairwise LocalTypeR.branchLe) :
    (bs.map fun b => (b.1, f b.2)).Pairwise LocalTypeR.branchLe := by
  induction h with
  | nil =>
    exact List.Pairwise.nil
  | cons ha hpair ih =>
    constructor
    · intro b hb
      simp only [List.mem_map, Prod.exists] at hb
      obtain ⟨l, t, hmem, heq⟩ := hb
      have hle : LocalTypeR.branchLe _ (l, t) := ha (l, t) hmem
      simp [LocalTypeR.branchLe] at hle ⊢
      simpa [← heq] using hle
    · exact ih

end Rumpsteak.Proofs.Projection.Merging
