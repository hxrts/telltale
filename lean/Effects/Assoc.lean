/-
Copyright (c) 2025 Rumpsteak Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Association List Utilities

This module provides a simple association list implementation with
lookup, erase, and update operations, along with key lemmas for reasoning
about these operations.

Association lists are used as the underlying representation for stores,
typing environments, and buffer maps throughout the effects formalization.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

namespace Assoc

variable {κ α : Type} [DecidableEq κ]

/-- Look up a value by key in an association list. Returns the first match. -/
def lookup : List (κ × α) → κ → Option α
  | [], _ => none
  | (k, v) :: xs, q => if k = q then some v else lookup xs q

/-- Erase all entries with a given key from an association list. -/
def erase : List (κ × α) → κ → List (κ × α)
  | [], _ => []
  | (k, v) :: xs, q => if k = q then erase xs q else (k, v) :: erase xs q

/-- Update (or insert) an entry in an association list.
    Removes any existing entries with the key first. -/
def update (m : List (κ × α)) (q : κ) (v : α) : List (κ × α) :=
  (q, v) :: erase m q

/-! ## Lookup/Update Lemmas -/

@[simp]
theorem lookup_nil (q : κ) : lookup ([] : List (κ × α)) q = none := rfl

theorem lookup_cons (k : κ) (v : α) (xs : List (κ × α)) (q : κ) :
    lookup ((k, v) :: xs) q = if k = q then some v else lookup xs q := rfl

@[simp]
theorem lookup_update_eq (m : List (κ × α)) (q : κ) (v : α) :
    lookup (update m q v) q = some v := by
  unfold update lookup
  simp

theorem lookup_update_neq (m : List (κ × α)) (q q' : κ) (v : α) :
    q' ≠ q → lookup (update m q v) q' = lookup m q' := by
  intro hne
  unfold update lookup
  simp [hne]
  induction m with
  | nil => simp [erase, lookup]
  | cons hd tl ih =>
    cases hd with
    | mk k a =>
      unfold erase lookup
      by_cases hkq : k = q
      · simp [hkq, ih]
      · by_cases hkq' : k = q'
        · simp [hkq, hkq', lookup, erase]
        · simp [hkq, hkq', lookup, erase, ih]

/-! ## Erase Lemmas -/

@[simp]
theorem erase_nil (q : κ) : erase ([] : List (κ × α)) q = [] := rfl

theorem mem_erase_of_mem (m : List (κ × α)) (q : κ) (k : κ) (v : α) :
    (k, v) ∈ erase m q → (k, v) ∈ m := by
  induction m with
  | nil => intro h; cases h
  | cons hd tl ih =>
    cases hd with
    | mk k' a =>
      unfold erase
      by_cases hk : k' = q
      · simp [hk]
        exact ih
      · simp [hk]
        intro h
        cases h with
        | inl h1 =>
          left
          exact h1
        | inr h2 =>
          right
          exact ih h2

theorem lookup_erase_eq (m : List (κ × α)) (q : κ) :
    lookup (erase m q) q = none := by
  induction m with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with
    | mk k v =>
      unfold erase
      by_cases hkq : k = q
      · simp [hkq, ih]
      · simp [hkq, lookup, ih]
        exact hkq

theorem lookup_erase_neq (m : List (κ × α)) (q q' : κ) :
    q' ≠ q → lookup (erase m q) q' = lookup m q' := by
  intro hne
  induction m with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with
    | mk k v =>
      unfold erase
      by_cases hkq : k = q
      · simp [hkq, lookup]
        by_cases hkq' : k = q'
        · exact absurd (hkq' ▸ hkq) hne.symm
        · simp [hkq', ih]
      · simp [hkq, lookup]
        by_cases hkq' : k = q'
        · simp [hkq']
        · simp [hkq', ih]

/-! ## Membership Lemmas -/

theorem mem_update (m : List (κ × α)) (q : κ) (v : α) :
    (q, v) ∈ update m q v := by
  unfold update
  exact List.mem_cons_self _ _

theorem mem_update_of_mem_neq (m : List (κ × α)) (q k : κ) (v a : α) :
    k ≠ q → (k, a) ∈ m → (k, a) ∈ update m q v := by
  intro hne hmem
  unfold update
  right
  induction m with
  | nil => cases hmem
  | cons hd tl ih =>
    cases hd with
    | mk k' a' =>
      unfold erase
      by_cases hk' : k' = q
      · simp [hk']
        cases hmem with
        | inl h =>
          cases h
          exact absurd hk' hne
        | inr h =>
          exact ih h
      · simp [hk']
        cases hmem with
        | inl h =>
          left
          exact h
        | inr h =>
          right
          exact ih h

end Assoc

end
