import Rumpsteak.Protocol.Core
import Rumpsteak.Protocol.Projection

/-! # Rumpsteak.Proofs.Projection

Proofs about projection and label subset operations.

## Overview

This module proves properties of the projection-related operations, particularly
that the `subLabelsOf` check is reflexive. This ensures that comparing a local
type to itself always succeeds.

## Claims

- `AllAnySelf`: Every element of a list witnesses itself in an `all/any` check.
- `SubLabelsReflexive`: A local type's actions are always a subset of themselves.

## Main Results

- `all_any_self`: Proof that `xs.all (λ a => xs.any (λ b => a = b)) = true`
- `subLabelsOf_refl`: Proof that `subLabelsOf lt lt = true`
-/

namespace Rumpsteak.Proofs.Projection

open Rumpsteak.Protocol.Core
open Rumpsteak.Protocol.Projection

/-! ## Claims -/

/-- Every element of a list is witnessed by `any` on the same list.
    Formal: ∀ xs, xs.all (λ a => xs.any (λ b => a = b)) = true -/
def AllAnySelf : Prop :=
  ∀ {α : Type} [DecidableEq α] (xs : List α),
    xs.all (fun a => xs.any fun b => decide (b = a)) = true

/-- A local type is always a sublabel of itself.
    Formal: ∀ lt, subLabelsOf lt lt = true -/
def SubLabelsReflexive : Prop :=
  ∀ (lt : LocalType), subLabelsOf lt lt = true

/-- Claims bundle for projection properties.
    Reviewers can check these properties without reading the proofs. -/
structure Claims where
  /-- Every element witnesses itself in all/any checks. -/
  allAnySelf : AllAnySelf
  /-- subLabelsOf is reflexive. -/
  subLabelsReflexive : SubLabelsReflexive

/-! ## Proofs -/

/-- Proof that every element of a list is witnessed by `any` on the same list.
    This is the key lemma for proving `subLabelsOf` reflexivity. -/
theorem all_any_self : AllAnySelf := by
  intro α _ xs
  -- Use the standard characterizations of all and any
  simp [List.all_eq_true, List.any_eq_true]

/-- Proof that a local type's actions are always a subset of themselves. -/
theorem subLabelsOf_refl : SubLabelsReflexive := by
  intro lt
  -- Unfold the definition and apply the all_any_self lemma
  unfold subLabelsOf
  simp [all_any_self]

/-- Construct the claims bundle with all proven properties. -/
def claims : Claims := ⟨all_any_self, subLabelsOf_refl⟩

end Rumpsteak.Proofs.Projection
