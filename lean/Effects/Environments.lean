/-
Copyright (c) 2025 Rumpsteak Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Effects.Basic
import Effects.Types
import Effects.Values
import Effects.Assoc

/-!
# Typing Environments and Runtime State

This module defines the various environments used for typing and runtime execution:
- `Store`: maps variables to runtime values
- `SEnv`: maps variables to static types
- `Buffer`: FIFO queue of values for async communication
- `Buffers`: maps endpoints to their message buffers
- `GEnv`: maps endpoints to their current session types
- `DEnv`: maps endpoints to their "in-flight" type traces

The type-level queue traces (DEnv) track what types have been sent but not
yet received, enabling the coherence invariant for async communication.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-! ## Type Abbreviations -/

/-- Runtime store: maps variable names to values. -/
abbrev Store := List (Var × Value)

/-- Static typing environment: maps variable names to value types. -/
abbrev SEnv := List (Var × ValType)

/-- Message buffer: FIFO queue of values waiting to be received. -/
abbrev Buffer := List Value

/-- Buffer map: maps endpoints to their message buffers. -/
abbrev Buffers := List (Endpoint × Buffer)

/-- Global session type environment: maps endpoints to current session types. -/
abbrev GEnv := List (Endpoint × SType)

/-- Delayed type environment: maps endpoints to lists of value types "in flight". -/
abbrev DEnv := List (Endpoint × List ValType)

/-! ## Store Operations -/

/-- Look up a variable in the store. -/
def lookupStr {α : Type} (m : List (Var × α)) (x : Var) : Option α :=
  Assoc.lookup m x

/-- Update (or insert) a variable binding in the store. -/
def updateStr {α : Type} (m : List (Var × α)) (x : Var) (v : α) : List (Var × α) :=
  Assoc.update m x v

@[simp]
theorem lookupStr_update_eq {α : Type} (m : List (Var × α)) (x : Var) (v : α) :
    lookupStr (updateStr m x v) x = some v := by
  simp [lookupStr, updateStr, Assoc.lookup_update_eq]

theorem lookupStr_update_neq {α : Type} (m : List (Var × α)) (x y : Var) (v : α) :
    y ≠ x → lookupStr (updateStr m x v) y = lookupStr m y := by
  intro hne
  simp [lookupStr, updateStr, Assoc.lookup_update_neq _ _ _ _ hne]

/-! ## Buffer Operations -/

/-- Look up a buffer for an endpoint. Returns empty list if not found. -/
def lookupBuf (B : Buffers) (e : Endpoint) : Buffer :=
  (Assoc.lookup B e).getD []

/-- Update the buffer for an endpoint. -/
def updateBuf (B : Buffers) (e : Endpoint) (q : Buffer) : Buffers :=
  Assoc.update B e q

@[simp]
theorem lookupBuf_update_eq (B : Buffers) (e : Endpoint) (q : Buffer) :
    lookupBuf (updateBuf B e q) e = q := by
  simp [lookupBuf, updateBuf, Assoc.lookup_update_eq]

theorem lookupBuf_update_neq (B : Buffers) (e e' : Endpoint) (q : Buffer) :
    e' ≠ e → lookupBuf (updateBuf B e q) e' = lookupBuf B e' := by
  intro hne
  simp [lookupBuf, updateBuf, Assoc.lookup_update_neq _ _ _ _ hne]

/-! ## Session Type Environment Operations -/

/-- Look up the session type for an endpoint. -/
def lookupG (G : GEnv) (e : Endpoint) : Option SType :=
  Assoc.lookup G e

/-- Update the session type for an endpoint. -/
def updateG (G : GEnv) (e : Endpoint) (S : SType) : GEnv :=
  Assoc.update G e S

@[simp]
theorem lookupG_update_eq (G : GEnv) (e : Endpoint) (S : SType) :
    lookupG (updateG G e S) e = some S := by
  simp [lookupG, updateG, Assoc.lookup_update_eq]

theorem lookupG_update_neq (G : GEnv) (e e' : Endpoint) (S : SType) :
    e' ≠ e → lookupG (updateG G e S) e' = lookupG G e' := by
  intro hne
  simp [lookupG, updateG, Assoc.lookup_update_neq _ _ _ _ hne]

/-! ## Delayed Type Environment Operations -/

/-- Look up the in-flight type list for an endpoint. Returns empty if not found. -/
def lookupD (D : DEnv) (e : Endpoint) : List ValType :=
  (Assoc.lookup D e).getD []

/-- Update the in-flight type list for an endpoint. -/
def updateD (D : DEnv) (e : Endpoint) (ts : List ValType) : DEnv :=
  Assoc.update D e ts

@[simp]
theorem lookupD_update_eq (D : DEnv) (e : Endpoint) (ts : List ValType) :
    lookupD (updateD D e ts) e = ts := by
  simp [lookupD, updateD, Assoc.lookup_update_eq]

theorem lookupD_update_neq (D : DEnv) (e e' : Endpoint) (ts : List ValType) :
    e' ≠ e → lookupD (updateD D e ts) e' = lookupD D e' := by
  intro hne
  simp [lookupD, updateD, Assoc.lookup_update_neq _ _ _ _ hne]

end
