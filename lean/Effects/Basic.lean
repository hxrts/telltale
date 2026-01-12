/-
Copyright (c) 2025 Rumpsteak Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Basic Definitions for Async Session Effects

This module defines the foundational types for channel endpoints:
- `Polarity`: distinguishes the two ends of a channel
- `ChanId`: unique identifiers for channels
- `Endpoint`: a channel endpoint is a (ChanId, Polarity) pair
- Duality operations on polarities and endpoints
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-- Polarity of a channel endpoint. Each channel has a left (L) and right (R) endpoint. -/
inductive Polarity where
  | L
  | R
  deriving Repr, DecidableEq

namespace Polarity

/-- The dual polarity: L ↔ R. -/
def dual : Polarity → Polarity
  | .L => .R
  | .R => .L

@[simp]
theorem dual_dual (p : Polarity) : p.dual.dual = p := by
  cases p <;> rfl

@[simp]
theorem dual_ne_self (p : Polarity) : p.dual ≠ p := by
  cases p <;> simp [dual]

end Polarity

/-- Channel identifiers are natural numbers. -/
abbrev ChanId := Nat

/-- An endpoint is a pair of channel ID and polarity. -/
abbrev Endpoint := ChanId × Polarity

namespace Endpoint

/-- The dual endpoint: same channel, opposite polarity. -/
def dual : Endpoint → Endpoint
  | (n, p) => (n, p.dual)

@[simp]
theorem dual_dual (e : Endpoint) : e.dual.dual = e := by
  cases e with
  | mk n p => simp [dual, Polarity.dual_dual]

@[simp]
theorem dual_fst (e : Endpoint) : e.dual.1 = e.1 := by
  cases e; rfl

@[simp]
theorem dual_ne_self (e : Endpoint) : e.dual ≠ e := by
  cases e with
  | mk n p =>
    simp [dual]
    exact Polarity.dual_ne_self p

/-- Two endpoints are duals iff they have the same channel ID but opposite polarities. -/
def areDual (e₁ e₂ : Endpoint) : Prop :=
  e₁.1 = e₂.1 ∧ e₁.2 = e₂.2.dual

theorem areDual_iff_dual_eq (e₁ e₂ : Endpoint) : areDual e₁ e₂ ↔ e₁ = e₂.dual := by
  constructor
  · intro ⟨hid, hpol⟩
    cases e₁; cases e₂
    simp only [dual] at *
    simp [hid, hpol, Polarity.dual_dual]
  · intro h
    subst h
    simp [areDual, dual, Polarity.dual_dual]

end Endpoint

-- Export commonly used definitions
export Polarity (dual)
export Endpoint (dual areDual)

end
