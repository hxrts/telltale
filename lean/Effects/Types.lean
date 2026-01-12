/-
Copyright (c) 2025 Rumpsteak Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Effects.Basic

/-!
# Session Types and Value Types

This module defines the type system for async session effects:
- `SType`: session types describing communication protocols
- `ValType`: value types including channels, references, and base types
- Duality for session types
- Linearity predicate for value types
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-- Session types describe communication protocols on a channel endpoint.
- `end_`: terminated session
- `send T S`: send a value of type T, then continue as S
- `recv T S`: receive a value of type T, then continue as S
-/
inductive SType where
  | end_ : SType
  | send : ValType → SType → SType
  | recv : ValType → SType → SType
  deriving Repr, DecidableEq

/-- Value types classify runtime values.
- `unit`: the unit type
- `bool`: booleans
- `chan S`: a channel endpoint with session type S
- `ref T`: a reference to a value of type T
-/
inductive ValType where
  | unit : ValType
  | bool : ValType
  | chan : SType → ValType
  | ref : ValType → ValType
  deriving Repr, DecidableEq

namespace SType

/-- The dual of a session type: send ↔ recv, with recursive duality on continuations. -/
def dual : SType → SType
  | .end_ => .end_
  | .send T S => .recv T S.dual
  | .recv T S => .send T S.dual

@[simp]
theorem dual_end : dual .end_ = .end_ := rfl

@[simp]
theorem dual_send (T : ValType) (S : SType) : dual (.send T S) = .recv T S.dual := rfl

@[simp]
theorem dual_recv (T : ValType) (S : SType) : dual (.recv T S) = .send T S.dual := rfl

theorem dual_dual : ∀ S : SType, S.dual.dual = S := by
  intro S
  induction S with
  | end_ => rfl
  | send T S ih => simp [dual, ih]
  | recv T S ih => simp [dual, ih]

/-- Two session types are dual iff one is the dual of the other. -/
def areDual (S₁ S₂ : SType) : Prop := S₁ = S₂.dual

theorem areDual_symm (S₁ S₂ : SType) : areDual S₁ S₂ ↔ areDual S₂ S₁ := by
  simp [areDual]
  constructor
  · intro h
    rw [h, dual_dual]
  · intro h
    rw [h, dual_dual]

end SType

namespace ValType

/-- A value type is linear if it represents a channel.
Linear values must be used exactly once. -/
def isLinear : ValType → Bool
  | .chan _ => true
  | _ => false

@[simp]
theorem isLinear_unit : isLinear .unit = false := rfl

@[simp]
theorem isLinear_bool : isLinear .bool = false := rfl

@[simp]
theorem isLinear_chan (S : SType) : isLinear (.chan S) = true := rfl

@[simp]
theorem isLinear_ref (T : ValType) : isLinear (.ref T) = false := rfl

/-- A value type is shared (can be duplicated) if it is not linear. -/
def isShared (T : ValType) : Bool := !T.isLinear

end ValType

end
