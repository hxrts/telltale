import Rumpsteak.Protocol.Core
import Rumpsteak.Protocol.Subtyping

/-! # Rumpsteak.Proofs.Subtyping

Proofs about subsequence and subtyping operations.

## Overview

This module proves that the subsequence and subtyping relations are reflexive.
Reflexivity ensures that comparing a local type to itself always succeeds,
which is essential for the verification pipeline.

## Claims

- `SubsequenceReflexive`: Any list is a subsequence of itself.
- `SubtypeReflexive`: Any local type is a subtype of itself.

## Main Results

- `isSubsequence_refl`: Proof that `isSubsequence xs xs = true`
- `isSubtype_refl`: Proof that `isSubtype lt lt = true`
-/

namespace Rumpsteak.Proofs.Subtyping

open Rumpsteak.Protocol.Core
open Rumpsteak.Protocol.Subtyping

/-! ## Claims -/

/-- Any list is a subsequence of itself.
    Formal: ∀ xs, isSubsequence xs xs = true -/
def SubsequenceReflexive : Prop :=
  ∀ {α : Type} [DecidableEq α] (xs : List α), isSubsequence xs xs = true

/-- Any local type is a subtype of itself.
    Formal: ∀ lt, isSubtype lt lt = true -/
def SubtypeReflexive : Prop :=
  ∀ (lt : LocalType), isSubtype lt lt = true

/-- Claims bundle for subtyping properties.
    Reviewers can check these properties without reading the proofs. -/
structure Claims where
  /-- isSubsequence is reflexive. -/
  subsequenceReflexive : SubsequenceReflexive
  /-- isSubtype is reflexive. -/
  subtypeReflexive : SubtypeReflexive

/-! ## Proofs -/

/-- Proof that any list is a subsequence of itself.
    Proceeds by induction on the list structure. -/
theorem isSubsequence_refl : SubsequenceReflexive := by
  intro α _ xs
  -- Induction on the list
  induction xs with
  | nil =>
    -- Empty list is trivially a subsequence of itself
    simp [isSubsequence]
  | cons a t ih =>
    -- For cons, the head matches itself, then recurse
    simp [isSubsequence, ih]

/-- Proof that any local type is a subtype of itself.
    Combines length equality with subsequence reflexivity. -/
theorem isSubtype_refl : SubtypeReflexive := by
  intro lt
  -- isSubtype checks length and subsequence; both hold reflexively
  simp [isSubtype, isSubsequence_refl]

/-- Construct the claims bundle with all proven properties. -/
def claims : Claims := ⟨isSubsequence_refl, isSubtype_refl⟩

end Rumpsteak.Proofs.Subtyping
