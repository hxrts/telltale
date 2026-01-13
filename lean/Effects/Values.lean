import Effects.LocalType

/-!
# MPST Runtime Values

This module defines the runtime values for multiparty session types.
Values include base types (unit, bool, nat, string), products, and
channel endpoints that carry session identifiers and role names.

## Linear Capability Tokens

For proof-carrying runtime, we extend values with linear capability tokens.
A token `tok e S` represents the capability to use endpoint `e` with local
type `S`. Tokens are:
- **Linear**: Cannot be duplicated or discarded
- **Unforgeable**: Only created by the monitor during session creation

The monitor tracks tokens in a linear context (`LinCtx`) and ensures
proper consumption/production during protocol steps.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-- Runtime values for MPST. -/
inductive Value where
  | unit : Value
  | bool : Bool → Value
  | nat : Nat → Value
  | string : String → Value
  | prod : Value → Value → Value
  | chan : Endpoint → Value  -- channel endpoint (sid, role)
  deriving Repr, DecidableEq

namespace Value

/-- Extract session ID from a channel value, if it is one. -/
def sessionId? : Value → Option SessionId
  | .chan e => some e.sid
  | _ => none

/-- Extract role from a channel value, if it is one. -/
def role? : Value → Option Role
  | .chan e => some e.role
  | _ => none

/-- Extract endpoint from a channel value, if it is one. -/
def endpoint? : Value → Option Endpoint
  | .chan e => some e
  | _ => none

/-- Check if a value is a channel. -/
def isChan : Value → Bool
  | .chan _ => true
  | _ => false

/-- Check if a session ID appears in a value. -/
def containsSid (sid : SessionId) : Value → Bool
  | .chan e => e.sid == sid
  | .prod v₁ v₂ => containsSid sid v₁ || containsSid sid v₂
  | _ => false

/-- All session IDs in a value are less than n. -/
def sidLt (v : Value) (n : SessionId) : Prop :=
  ∀ sid, v.containsSid sid → sid < n

/-- simdLt for unit is trivial. -/
theorem sidLt_unit (n : SessionId) : Value.unit.sidLt n := by
  intro sid hcontains
  simp only [containsSid, Bool.false_eq_true] at hcontains

/-- sidLt for bool is trivial. -/
theorem sidLt_bool (b : Bool) (n : SessionId) : (Value.bool b).sidLt n := by
  intro sid hcontains
  simp only [containsSid, Bool.false_eq_true] at hcontains

/-- sidLt for nat is trivial. -/
theorem sidLt_nat (m : Nat) (n : SessionId) : (Value.nat m).sidLt n := by
  intro sid hcontains
  simp only [containsSid, Bool.false_eq_true] at hcontains

/-- sidLt for string is trivial. -/
theorem sidLt_string (s : String) (n : SessionId) : (Value.string s).sidLt n := by
  intro sid hcontains
  simp only [containsSid, Bool.false_eq_true] at hcontains

/-- sidLt for chan. -/
theorem sidLt_chan (e : Endpoint) (n : SessionId) (h : e.sid < n) : (Value.chan e).sidLt n := by
  intro sid hcontains
  simp only [containsSid, beq_iff_eq] at hcontains
  rw [← hcontains]
  exact h

end Value

/-! ## Linear Capability Tokens -/

/-- A capability token represents the right to use an endpoint with a specific type.

Tokens are created by the monitor during session initialization and consumed/
produced during protocol steps. They are the key to proof-carrying runtime:
- The token type matches the expected local type at the endpoint
- Token consumption corresponds to performing the head action
- Token production provides the continuation capability -/
structure Token where
  /-- The endpoint this token grants access to -/
  endpoint : Endpoint
  /-- The current local type at this endpoint -/
  localType : LocalType
  deriving Repr

/-- Linear context: tracks which tokens are currently available.
    Each entry is an endpoint with its current local type. -/
abbrev LinCtx := List (Endpoint × LocalType)

namespace LinCtx

/-- Empty linear context. -/
def empty : LinCtx := []

/-- Look up a token for an endpoint. -/
def find (ctx : LinCtx) (e : Endpoint) : Option LocalType :=
  ctx.lookup e

/-- Remove a token from the context (consume it).
    Returns None if the token doesn't exist. -/
def consumeToken (ctx : LinCtx) (e : Endpoint) : Option (LinCtx × LocalType) :=
  match ctx with
  | [] => none
  | (e', S') :: rest =>
    if e = e' then
      some (rest, S')
    else
      match consumeToken rest e with
      | some (ctx', S) => some ((e', S') :: ctx', S)
      | none => none

/-- Add a token to the context (produce it). -/
def produceToken (ctx : LinCtx) (e : Endpoint) (S : LocalType) : LinCtx :=
  (e, S) :: ctx

/-- Consume one token and produce another (for protocol steps).
    Returns the old type that was consumed. -/
def stepToken (ctx : LinCtx) (e : Endpoint) (newS : LocalType) : Option (LinCtx × LocalType) :=
  match consumeToken ctx e with
  | some (ctx', oldS) => some (produceToken ctx' e newS, oldS)
  | none => none

/-- Check if context contains a token for endpoint. -/
def contains (ctx : LinCtx) (e : Endpoint) : Bool :=
  ctx.any fun (e', _) => e == e'

/-- Get all endpoints in the context. -/
def endpoints (ctx : LinCtx) : List Endpoint :=
  ctx.map Prod.fst

end LinCtx

/-! ## Buffer Value Predicates -/

/-- All values in a buffer have session IDs less than n. -/
def Buffer.sidLt (buf : List Value) (n : SessionId) : Prop :=
  ∀ v, v ∈ buf → v.sidLt n

theorem Buffer.sidLt_nil (n : SessionId) : Buffer.sidLt [] n := by
  intro v hv
  simp at hv

theorem Buffer.sidLt_cons (v : Value) (buf : List Value) (n : SessionId)
    (hv : v.sidLt n) (hbuf : Buffer.sidLt buf n) : Buffer.sidLt (v :: buf) n := by
  intro w hw
  simp only [List.mem_cons] at hw
  cases hw with
  | inl h => rw [h]; exact hv
  | inr h => exact hbuf w h

theorem Buffer.sidLt_append (buf₁ buf₂ : List Value) (n : SessionId)
    (h₁ : Buffer.sidLt buf₁ n) (h₂ : Buffer.sidLt buf₂ n) :
    Buffer.sidLt (buf₁ ++ buf₂) n := by
  intro v hv
  simp only [List.mem_append] at hv
  cases hv with
  | inl h => exact h₁ v h
  | inr h => exact h₂ v h

end
