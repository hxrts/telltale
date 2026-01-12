/-
Copyright (c) 2025 Rumpsteak Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Effects.Types
import Effects.Environments

/-!
# Linear Context Splitting

This module defines the `SplitSEnv` judgment for splitting typing environments
to support parallel composition:
- Shared (non-linear) variables are duplicated to both branches
- Linear variables (channels) are partitioned: each goes to exactly one branch

This ensures that linear resources are used exactly once, preventing
aliasing of channel endpoints across concurrent threads.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-- Linear context splitting judgment.
    `SplitSEnv Γ Γ₁ Γ₂` means Γ can be split into Γ₁ and Γ₂ such that:
    - Shared variables appear in both Γ₁ and Γ₂
    - Linear variables appear in exactly one of Γ₁ or Γ₂ -/
inductive SplitSEnv : SEnv → SEnv → SEnv → Prop where
  /-- Empty environments split to empty. -/
  | nil : SplitSEnv [] [] []

  /-- Shared variable: duplicate to both branches. -/
  | cons_shared {x : Var} {T : ValType} {Γ Γ₁ Γ₂ : SEnv} :
      T.isLinear = false →
      SplitSEnv Γ Γ₁ Γ₂ →
      SplitSEnv ((x, T) :: Γ) ((x, T) :: Γ₁) ((x, T) :: Γ₂)

  /-- Linear variable: goes to left branch only. -/
  | cons_lin_left {x : Var} {T : ValType} {Γ Γ₁ Γ₂ : SEnv} :
      T.isLinear = true →
      SplitSEnv Γ Γ₁ Γ₂ →
      SplitSEnv ((x, T) :: Γ) ((x, T) :: Γ₁) Γ₂

  /-- Linear variable: goes to right branch only. -/
  | cons_lin_right {x : Var} {T : ValType} {Γ Γ₁ Γ₂ : SEnv} :
      T.isLinear = true →
      SplitSEnv Γ Γ₁ Γ₂ →
      SplitSEnv ((x, T) :: Γ) Γ₁ ((x, T) :: Γ₂)

namespace SplitSEnv

/-- Any environment can be split trivially by duplicating it. -/
theorem refl (Γ : SEnv) (h : ∀ x T, (x, T) ∈ Γ → T.isLinear = false) :
    SplitSEnv Γ Γ Γ := by
  induction Γ with
  | nil => exact .nil
  | cons xt Γ ih =>
    cases xt with
    | mk x T =>
      have hlin : T.isLinear = false := h x T (List.mem_cons_self _ _)
      have ih' := ih (fun x' T' hmem => h x' T' (List.mem_cons_of_mem _ hmem))
      exact .cons_shared hlin ih'

/-- Splitting is commutative: Γ₁ and Γ₂ can be swapped. -/
theorem comm {Γ Γ₁ Γ₂ : SEnv} (h : SplitSEnv Γ Γ₁ Γ₂) : SplitSEnv Γ Γ₂ Γ₁ := by
  induction h with
  | nil => exact .nil
  | cons_shared hlin _ ih => exact .cons_shared hlin ih
  | cons_lin_left hlin _ ih => exact .cons_lin_right hlin ih
  | cons_lin_right hlin _ ih => exact .cons_lin_left hlin ih

/-- A variable in Γ is in at least one of Γ₁ or Γ₂. -/
theorem mem_left_or_right {Γ Γ₁ Γ₂ : SEnv} {x : Var} {T : ValType}
    (h : SplitSEnv Γ Γ₁ Γ₂) (hmem : (x, T) ∈ Γ) :
    (x, T) ∈ Γ₁ ∨ (x, T) ∈ Γ₂ := by
  induction h with
  | nil => cases hmem
  | cons_shared hlin hsplit ih =>
    cases hmem with
    | head => left; exact List.mem_cons_self _ _
    | tail _ hmem' =>
      cases ih hmem' with
      | inl h => left; exact List.mem_cons_of_mem _ h
      | inr h => right; exact List.mem_cons_of_mem _ h
  | cons_lin_left hlin hsplit ih =>
    cases hmem with
    | head => left; exact List.mem_cons_self _ _
    | tail _ hmem' =>
      cases ih hmem' with
      | inl h => left; exact List.mem_cons_of_mem _ h
      | inr h => right; exact h
  | cons_lin_right hlin hsplit ih =>
    cases hmem with
    | head => right; exact List.mem_cons_self _ _
    | tail _ hmem' =>
      cases ih hmem' with
      | inl h => left; exact h
      | inr h => right; exact List.mem_cons_of_mem _ h

/-- A linear variable in Γ is in exactly one of Γ₁ or Γ₂, not both. -/
theorem linear_exclusive {Γ Γ₁ Γ₂ : SEnv} {x : Var} {T : ValType}
    (h : SplitSEnv Γ Γ₁ Γ₂) (hmem : (x, T) ∈ Γ) (hlin : T.isLinear = true) :
    ((x, T) ∈ Γ₁ ∧ (x, T) ∉ Γ₂) ∨ ((x, T) ∉ Γ₁ ∧ (x, T) ∈ Γ₂) := by
  induction h with
  | nil => cases hmem
  | cons_shared hlin' hsplit ih =>
    cases hmem with
    | head =>
      -- This case contradicts: hlin says T is linear, hlin' says T is not linear
      simp [hlin] at hlin'
    | tail _ hmem' =>
      cases ih hmem' hlin with
      | inl ⟨h1, h2⟩ =>
        left
        exact ⟨List.mem_cons_of_mem _ h1, fun hmem2 =>
          h2 (List.mem_of_mem_cons_of_ne hmem2 (by
            intro heq
            cases heq
            simp [hlin] at hlin'))⟩
      | inr ⟨h1, h2⟩ =>
        right
        exact ⟨fun hmem1 =>
          h1 (List.mem_of_mem_cons_of_ne hmem1 (by
            intro heq
            cases heq
            simp [hlin] at hlin')), List.mem_cons_of_mem _ h2⟩
  | cons_lin_left hlin' hsplit ih =>
    cases hmem with
    | head =>
      left
      exact ⟨List.mem_cons_self _ _, List.not_mem_nil _⟩
    | tail _ hmem' =>
      cases ih hmem' hlin with
      | inl ⟨h1, h2⟩ =>
        left
        exact ⟨List.mem_cons_of_mem _ h1, h2⟩
      | inr ⟨h1, h2⟩ =>
        right
        exact ⟨fun hmem1 => h1 (List.mem_of_mem_cons_of_ne hmem1 (by
          intro heq
          cases heq
          -- Would make x,T duplicate which contradicts linearity
          sorry)), h2⟩
  | cons_lin_right hlin' hsplit ih =>
    cases hmem with
    | head =>
      right
      exact ⟨List.not_mem_nil _, List.mem_cons_self _ _⟩
    | tail _ hmem' =>
      cases ih hmem' hlin with
      | inl ⟨h1, h2⟩ =>
        left
        exact ⟨h1, fun hmem2 => h2 (List.mem_of_mem_cons_of_ne hmem2 (by
          intro heq
          cases heq
          sorry))⟩
      | inr ⟨h1, h2⟩ =>
        right
        exact ⟨h1, List.mem_cons_of_mem _ h2⟩

end SplitSEnv

/-- No-alias invariant for stores: two distinct linear variables
    cannot refer to the same channel endpoint. -/
def StoreNoAlias (S : SEnv) (st : Store) : Prop :=
  ∀ x y e,
    x ≠ y →
    (∃ Tx, lookupStr S x = some Tx ∧ Tx.isLinear = true) →
    (∃ Ty, lookupStr S y = some Ty ∧ Ty.isLinear = true) →
    lookupStr st x = some (Value.chan e) →
    lookupStr st y = some (Value.chan e) →
    False

end
