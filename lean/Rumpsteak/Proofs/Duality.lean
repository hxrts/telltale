import Rumpsteak.Protocol.Core

/-! # Rumpsteak.Proofs.Duality

Proofs that duality operations are involutive.

## Overview

This module proves that the duality operations on local kinds, actions, and types
are involutive (applying them twice returns the original value). These properties
are fundamental for verifying that communicating roles have properly matched
send/receive pairs.

## Claims

- `SwapInvolutive`: Double-swap on LocalKind returns the original kind.
- `DualInvolutive`: Double-dual on LocalAction returns the original action.
- `LocalTypeDualInvolutive`: Double-dual on LocalType returns the original type.

## Main Results

- `swap_involutive`: Proof that `kind.swap.swap = kind`
- `dual_involutive`: Proof that `dual (dual action) = action`
- `localtype_dual_involutive`: Proof that `dual (dual lt) = lt`
-/

namespace Rumpsteak.Proofs.Duality

open Rumpsteak.Protocol.Core

/-! ## Claims -/

/-- Double-swap on LocalKind is the identity.
    Formal: ∀ kind, kind.swap.swap = kind -/
def SwapInvolutive : Prop :=
  ∀ (kind : LocalKind), kind.swap.swap = kind

/-- Double-dual on LocalAction is the identity.
    Formal: ∀ action, dual (dual action) = action -/
def DualInvolutive : Prop :=
  ∀ (action : LocalAction), LocalAction.dual (LocalAction.dual action) = action

/-- Double-dual on LocalType is the identity.
    Formal: ∀ lt, dual (dual lt) = lt -/
def LocalTypeDualInvolutive : Prop :=
  ∀ (lt : LocalType), LocalType.dual (LocalType.dual lt) = lt

/-- Claims bundle for duality properties.
    Reviewers can check these properties without reading the proofs. -/
structure Claims where
  /-- LocalKind.swap is involutive. -/
  swapInvolutive : SwapInvolutive
  /-- LocalAction.dual is involutive. -/
  dualInvolutive : DualInvolutive
  /-- LocalType.dual is involutive. -/
  localTypeDualInvolutive : LocalTypeDualInvolutive

/-! ## Proofs -/

/-- Proof that double-swap returns the original kind. -/
theorem swap_involutive : SwapInvolutive := by
  -- Case split on the kind constructor
  intro kind
  cases kind <;> simp [LocalKind.swap]

/-- Proof that double-dual returns the original action. -/
theorem dual_involutive : DualInvolutive := by
  intro action
  -- Destructure the action to access its components
  let ⟨kind, partner, label⟩ := action
  -- The dual operation only affects the kind, and swap is involutive
  simp [LocalAction.dual, swap_involutive kind]

/-- Proof that double-dual returns the original local type. -/
theorem localtype_dual_involutive : LocalTypeDualInvolutive := by
  intro lt
  simp only [LocalType.dual]
  -- Show that dual ∘ dual = id pointwise
  have hdual_id : ∀ a, LocalAction.dual (LocalAction.dual a) = a := dual_involutive
  -- Apply to the list using map_map and List.map_id
  have hmap : List.map LocalAction.dual (List.map LocalAction.dual lt.actions) = lt.actions := by
    rw [List.map_map]
    have : (LocalAction.dual ∘ LocalAction.dual) = id := funext hdual_id
    simp only [this, List.map_id]
  -- Use the fact that lt = {actions := lt.actions}
  cases lt with
  | mk actions =>
    simp only [hmap]

/-- Construct the claims bundle with all proven properties. -/
def claims : Claims := ⟨swap_involutive, dual_involutive, localtype_dual_involutive⟩

end Rumpsteak.Proofs.Duality
