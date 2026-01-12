/-
Copyright (c) 2025 Rumpsteak Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Effects.Basic
import Effects.Types
import Effects.Values
import Effects.Environments

/-!
# Value Typing, Buffer Typing, and Coherence

This module defines the core typing judgments and invariants for async session effects:
- `HasTypeVal`: value typing judgment (depends on GEnv for channels)
- `BufferTyping`: typing for message buffers
- `Consume`: consume a session type by "receiving" a sequence of types
- `Coherent`: the coherence invariant for async communication
- `StoreTyped`: store is well-typed against an environment
- `BuffersTyped`: all buffers match their type traces
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-! ## Value Typing -/

/-- Value typing judgment. Depends on GEnv for typing channel values.
- `unit`: unit value has unit type
- `bool`: boolean value has bool type
- `chan`: channel endpoint has chan type if GEnv maps it to a session type
- `loc`: location has reference type (heap typing not tracked here)
-/
inductive HasTypeVal (G : GEnv) : Value → ValType → Prop where
  | unit : HasTypeVal G Value.unit ValType.unit
  | bool (b : Bool) : HasTypeVal G (Value.bool b) ValType.bool
  | chan {e : Endpoint} {S : SType} :
      lookupG G e = some S → HasTypeVal G (Value.chan e) (ValType.chan S)
  | loc {l : Nat} {T : ValType} : HasTypeVal G (Value.loc l) (ValType.ref T)

namespace HasTypeVal

/-- Value typing is deterministic: a value has at most one type under a given G.
    (Modulo the fact that loc can have any ref type - in practice, use heap typing.) -/
theorem type_unique {G : GEnv} {v : Value} {T₁ T₂ : ValType}
    (h₁ : HasTypeVal G v T₁) (h₂ : HasTypeVal G v T₂) : T₁ = T₂ := by
  cases h₁ <;> cases h₂ <;> try rfl
  case chan.chan h₁ h₂ =>
    congr
    have := congrArg (·) (h₁.symm.trans h₂)
    simp at this
    exact this

end HasTypeVal

/-! ## Buffer Typing -/

/-- A buffer is typed by a list of value types if they match element-wise. -/
def BufferTyping (G : GEnv) (q : Buffer) (ts : List ValType) : Prop :=
  List.Forall₂ (fun v T => HasTypeVal G v T) q ts

namespace BufferTyping

@[simp]
theorem nil (G : GEnv) : BufferTyping G [] [] :=
  List.Forall₂.nil

theorem cons {G : GEnv} {v : Value} {T : ValType} {q : Buffer} {ts : List ValType}
    (hv : HasTypeVal G v T) (hq : BufferTyping G q ts) :
    BufferTyping G (v :: q) (T :: ts) :=
  List.Forall₂.cons hv hq

/-- Appending a typed value to a typed buffer produces a typed buffer. -/
theorem append (G : GEnv) (q : Buffer) (ts : List ValType) (v : Value) (T : ValType) :
    BufferTyping G q ts →
    HasTypeVal G v T →
    BufferTyping G (q ++ [v]) (ts ++ [T]) := by
  intro hq hv
  induction hq with
  | nil =>
    exact List.Forall₂.cons hv List.Forall₂.nil
  | @cons a b q' ts' hab hrest ih =>
    simpa [List.cons_append] using List.Forall₂.cons hab (ih hv)

/-- Popping from a typed buffer with a matching head type. -/
theorem pop {G : GEnv} {v : Value} {T : ValType} {q : Buffer} {ts : List ValType}
    (hq : BufferTyping G (v :: q) (T :: ts)) :
    HasTypeVal G v T ∧ BufferTyping G q ts := by
  cases hq with
  | cons hv hrest => exact ⟨hv, hrest⟩

end BufferTyping

/-! ## Session Type Consumption -/

/-- Consume a session type by "receiving" a sequence of value types.
    This tracks how a session type evolves as messages arrive in the buffer. -/
def Consume : SType → List ValType → Option SType
  | S, [] => some S
  | .recv T S, (T' :: ts) =>
      if T = T' then Consume S ts else none
  | _, _ => none

namespace Consume

@[simp]
theorem nil (S : SType) : Consume S [] = some S := rfl

@[simp]
theorem recv_match (T : ValType) (S : SType) (ts : List ValType) :
    Consume (.recv T S) (T :: ts) = Consume S ts := by
  simp [Consume]

theorem recv_mismatch {T T' : ValType} {S : SType} {ts : List ValType}
    (hne : T ≠ T') : Consume (.recv T S) (T' :: ts) = none := by
  simp [Consume, hne]

theorem send_nonempty (T : ValType) (U : SType) (ts : List ValType) :
    ts ≠ [] → Consume (.send T U) ts = none := by
  intro hne
  cases ts with
  | nil => exact absurd rfl hne
  | cons _ _ => rfl

theorem end_nonempty (ts : List ValType) :
    ts ≠ [] → Consume .end_ ts = none := by
  intro hne
  cases ts with
  | nil => exact absurd rfl hne
  | cons _ _ => rfl

/-- Consuming send type with non-empty list always fails. -/
theorem send_some {T : ValType} {U S1 : SType} {q : List ValType} :
    Consume (.send T U) q = some S1 → q = [] ∧ S1 = .send T U := by
  cases q with
  | nil =>
    intro h
    simp [Consume] at h
    exact ⟨rfl, h.symm⟩
  | cons a q =>
    intro h
    simp [Consume] at h

/-- Consumption distributes over append. -/
theorem append (S : SType) (Q : List ValType) (T : ValType) :
    Consume S (Q ++ [T]) = (Consume S Q).bind (fun S' => Consume S' [T]) := by
  induction Q generalizing S with
  | nil => simp [Consume]
  | cons a Q ih =>
    cases S with
    | end_ => simp [Consume]
    | send T0 S0 => simp [Consume]
    | recv T0 S0 =>
      by_cases h : T0 = a
      · simp [Consume, h, ih]
      · simp [Consume, h]

/-- Consuming then receiving T when we're at recv T. -/
theorem append_recv (S : SType) (Q : List ValType) (T : ValType) (S2 : SType) :
    Consume S Q = some (.recv T S2) →
    Consume S (Q ++ [T]) = some S2 := by
  intro h
  have := append S Q T
  simp [h, Consume] at this
  exact this

end Consume

/-! ## Coherence Invariant -/

/-- The coherence invariant for async communication.
    For every endpoint e with session type S in G:
    - The dual endpoint e' also has a session type S' in G
    - After consuming their respective in-flight type traces from D,
      the remaining session types are duals of each other.

    This ensures that sent messages will eventually be receivable with
    the correct types, maintaining type safety across async boundaries. -/
def Coherent (G : GEnv) (D : DEnv) : Prop :=
  ∀ e S, lookupG G e = some S →
    let e' := e.dual
    ∃ S' q q',
      lookupG G e' = some S' ∧
      q = lookupD D e ∧
      q' = lookupD D e' ∧
      match Consume S q, Consume S' q' with
      | some S1, some S2 => S1 = S2.dual
      | _, _ => False

/-! ## Store Typing -/

/-- A store is well-typed if every variable maps to a value of the declared type. -/
def StoreTyped (S : SEnv) (G : GEnv) (st : Store) : Prop :=
  ∀ x v T, lookupStr st x = some v → lookupStr S x = some T → HasTypeVal G v T

/-! ## Buffers Typed -/

/-- All buffers are well-typed according to their type traces in D. -/
def BuffersTyped (G : GEnv) (D : DEnv) (B : Buffers) : Prop :=
  ∀ e, BufferTyping G (lookupBuf B e) (lookupD D e)

namespace BuffersTyped

/-- Enqueuing a value updates both the buffer and type trace consistently. -/
theorem enqueue (G : GEnv) (D : DEnv) (B : Buffers) (e : Endpoint) (v : Value) (T : ValType) :
    BuffersTyped G D B →
    HasTypeVal G v T →
    BuffersTyped G (updateD D e (lookupD D e ++ [T])) (updateBuf B e (lookupBuf B e ++ [v])) := by
  intro hBT hv
  intro e'
  by_cases h : e' = e
  · subst h
    have hOld : BufferTyping G (lookupBuf B e) (lookupD D e) := hBT e
    have hNew : BufferTyping G (lookupBuf B e ++ [v]) (lookupD D e ++ [T]) :=
      BufferTyping.append G (lookupBuf B e) (lookupD D e) v T hOld hv
    simpa [lookupBuf_update_eq, lookupD_update_eq] using hNew
  · have hb : lookupBuf (updateBuf B e (lookupBuf B e ++ [v])) e' = lookupBuf B e' :=
      lookupBuf_update_neq B e e' (lookupBuf B e ++ [v]) h
    have hd : lookupD (updateD D e (lookupD D e ++ [T])) e' = lookupD D e' :=
      lookupD_update_neq D e e' (lookupD D e ++ [T]) h
    simpa [hb, hd] using hBT e'

end BuffersTyped

end
