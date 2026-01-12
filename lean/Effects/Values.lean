/-
Copyright (c) 2025 Rumpsteak Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Effects.Basic
import Effects.Types

/-!
# Runtime Values

This module defines the runtime values that can be stored and transmitted
in async session effects:
- Unit values
- Boolean values
- Channel endpoints (carrying polarity information)
- Heap locations (references)
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-- Runtime values that can be stored in variables and transmitted over channels. -/
inductive Value where
  | unit : Value
  | bool : Bool → Value
  | chan : Endpoint → Value
  | loc : Nat → Value
  deriving Repr, DecidableEq, Inhabited

namespace Value

/-- Extract the channel ID from a channel value, if present. -/
def chanId? : Value → Option ChanId
  | .chan (n, _) => some n
  | _ => none

/-- Extract the endpoint from a channel value, if present. -/
def endpoint? : Value → Option Endpoint
  | .chan e => some e
  | _ => none

/-- Check if a value is a channel. -/
def isChannel : Value → Bool
  | .chan _ => true
  | _ => false

/-- Check if a value's channel ID (if any) is less than n. -/
def idLt (n : Nat) : Value → Prop
  | .unit => True
  | .bool _ => True
  | .loc _ => True
  | .chan (id, _) => id < n

instance : Decidable (Value.idLt n v) := by
  cases v <;> simp [idLt] <;> infer_instance

@[simp]
theorem idLt_unit (n : Nat) : idLt n .unit = True := rfl

@[simp]
theorem idLt_bool (n : Nat) (b : Bool) : idLt n (.bool b) = True := rfl

@[simp]
theorem idLt_loc (n : Nat) (l : Nat) : idLt n (.loc l) = True := rfl

@[simp]
theorem idLt_chan (n : Nat) (id : ChanId) (p : Polarity) :
    idLt n (.chan (id, p)) ↔ id < n := by
  simp [idLt]

theorem idLt_mono {m n : Nat} (v : Value) (hmn : m ≤ n) :
    idLt m v → idLt n v := by
  cases v <;> simp [idLt]
  intro h
  exact Nat.lt_of_lt_of_le h hmn

end Value

/-- Variable names are strings. -/
abbrev Var := String

end
