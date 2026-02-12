import Protocol.LocalType
import Protocol.Values
import Batteries.Data.RBMap
import Batteries.Data.RBMap.Lemmas

/-! # MPST Environments

This module defines the runtime environments for multiparty session types. -/

/-
The Problem. MPST execution requires tracking local types per endpoint, value
stores, in-flight message traces, and message buffers. These environments must
support efficient lookup and update with clear semantics.

Solution Structure. We define:
1. `VarStore/SEnv`: variable stores and type environments
2. `GEnv`: session environment (endpoint → local type)
3. `DEnv`: delayed type environment (edge → trace)
4. `Buffers`: per-edge FIFO message buffers
The key insight is that buffers/traces are keyed by directed edges, not endpoints.
-/


/- `Store`: Variable store mapping variables to runtime values
- `SEnv`: Type environment mapping variables to value types
- `GEnv`: Session environment mapping endpoints to local types
- `DEnv`: Delayed type environment for in-flight message traces per directed edge
- `Buffers`: Per-edge FIFO message buffers keyed by (sid, from, to)

The key difference from binary session types is that buffers and type traces
are keyed by **directed edges** `(sid, from, to)` rather than endpoints.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section

/-! ## Variables -/

/-- Variables are strings. -/
abbrev Var := String

/-! ## VarStore: Variable → Value -/

/-- VarStore maps variables to runtime values.
    Named VarStore to avoid collision with Iris.Std.Heap.Store. -/
abbrev VarStore := List (Var × Value)

/-- Lookup a value in the store. -/
def lookupStr (store : VarStore) (x : Var) : Option Value :=
  store.lookup x

/-- Update or insert a variable in the store. -/
def updateStr (store : VarStore) (x : Var) (v : Value) : VarStore :=
  match store with
  | [] => [(x, v)]
  | (y, w) :: rest =>
    if x = y then (x, v) :: rest
    else (y, w) :: updateStr rest x v

/-! ## SEnv: Variable → ValType -/

open Batteries

/-- SEnv maps variables to their value types (list-backed). -/
abbrev SEnv := List (Var × ValType)

/-- Lookup a type in SEnv. -/
def lookupSEnv (env : SEnv) (x : Var) : Option ValType :=
  env.lookup x

/-- Update or insert in SEnv. -/
def updateSEnv (env : SEnv) (x : Var) (T : ValType) : SEnv :=
  match env with
  | [] => [(x, T)]
  | (y, U) :: rest =>
    if x = y then (x, T) :: rest
    else (y, U) :: updateSEnv rest x T

/-- Remove all bindings for a variable from SEnv. -/
def eraseSEnv (env : SEnv) (x : Var) : SEnv :=
  match env with
  | [] => []
  | (y, T) :: rest =>
    if x = y then eraseSEnv rest x
    else (y, T) :: eraseSEnv rest x

theorem eraseSEnv_of_lookup_none {env : SEnv} {x : Var}
    (hNone : lookupSEnv env x = none) :
    eraseSEnv env x = env := by
  induction env with
  | nil =>
      simp [eraseSEnv]
  | cons hd tl ih =>
      cases hd with
      | mk y T =>
          by_cases hxy : x = y
          · subst hxy
            simp [lookupSEnv] at hNone
          · have htl : lookupSEnv tl x = none := by
              have hbeq : (x == y) = false := beq_eq_false_iff_ne.mpr hxy
              simpa [lookupSEnv, List.lookup, hbeq] using hNone
            simp [eraseSEnv, hxy, ih htl]

@[simp] theorem lookupSEnv_empty (x : Var) : lookupSEnv (∅ : SEnv) x = none := by
  rfl

/-- Union of SEnvs (list append, left-biased on lookup). -/
def SEnvUnion (S₁ S₂ : SEnv) : SEnv :=
  S₁ ++ S₂

/-! ## OwnedEnv: Explicit Right/Left Boundary -/

/-- OwnedEnv splits owned variables into a right (framed) prefix and a left (local) suffix. -/
structure OwnedEnv where
  right : SEnv
  left : SEnv

@[simp] theorem OwnedEnv.eta (o : OwnedEnv) :
    OwnedEnv.mk o.right o.left = o := by cases o; rfl

instance : Inhabited OwnedEnv where
  default := { right := [], left := [] }

instance : Coe SEnv OwnedEnv where
  coe s := { right := [], left := s }

instance : EmptyCollection OwnedEnv := ⟨{ right := (∅ : SEnv), left := (∅ : SEnv) }⟩

namespace OwnedEnv

/-- Full owned environment as a single SEnv. -/
def all (S : OwnedEnv) : SEnv :=
  S.right ++ S.left

instance : Coe OwnedEnv SEnv := ⟨OwnedEnv.all⟩

/-- Lookup in the full owned environment. -/
def lookup (S : OwnedEnv) (x : Var) : Option ValType :=
  lookupSEnv (all S) x

/-- Lookup only in the right (framed) portion. -/
def lookupRight (S : OwnedEnv) (x : Var) : Option ValType :=
  lookupSEnv S.right x

/-- Lookup only in the left (local) portion. -/
def lookupLeft (S : OwnedEnv) (x : Var) : Option ValType :=
  lookupSEnv S.left x

/-- Update only the left (local) portion. -/
def updateLeft (S : OwnedEnv) (x : Var) (T : ValType) : OwnedEnv :=
  { right := eraseSEnv S.right x, left := updateSEnv S.left x T }

/-- Add a frame to the right portion (low priority within right). -/
def frameRight (Sframe : SEnv) (S : OwnedEnv) : OwnedEnv :=
  { right := S.right ++ Sframe, left := S.left }

/-- Add a frame to the left (local) portion (low priority within left). -/
def frameLeft (Sframe : SEnv) (S : OwnedEnv) : OwnedEnv :=
  { right := S.right, left := S.left ++ Sframe }

instance : HAppend OwnedEnv SEnv OwnedEnv where
  hAppend := fun S Sframe => OwnedEnv.frameLeft Sframe S

/-- Treat a plain SEnv as an owned env with empty right frame. -/
def ofLeft (S : SEnv) : OwnedEnv :=
  { right := [], left := S }

@[simp] theorem toSEnv_coe (S : OwnedEnv) : (S : SEnv) = S.right ++ S.left := by
  rfl

@[simp] theorem frameLeft_left (S : OwnedEnv) (Sframe : SEnv) :
    (S ++ Sframe).left = S.left ++ Sframe := by
  rfl

@[simp] theorem frameLeft_right (S : OwnedEnv) (Sframe : SEnv) :
    (S ++ Sframe).right = S.right := by
  rfl

@[simp] theorem toSEnv_frameLeft (S : OwnedEnv) (Sframe : SEnv) :
    ((S ++ Sframe : OwnedEnv) : SEnv) = (S : SEnv) ++ Sframe := by
  simp [OwnedEnv.all, List.append_assoc]

end OwnedEnv

/-! ## GEnv: Endpoint → LocalType -/

/-- GEnv maps session endpoints to their current local session types. -/
abbrev GEnv := List (Endpoint × LocalType)

/-- Lookup a local type in GEnv. -/
def lookupG (env : GEnv) (e : Endpoint) : Option LocalType :=
  env.lookup e

/-- Update or insert in GEnv. -/
def updateG (env : GEnv) (e : Endpoint) (L : LocalType) : GEnv :=
  match env with
  | [] => [(e, L)]
  | (e', L') :: rest =>
    if e = e' then (e, L) :: rest
    else (e', L') :: updateG rest e L

/-- Lookup at the updated endpoint returns the new value. -/
@[simp] theorem lookupG_updateG_eq {env : GEnv} {e : Endpoint} {L : LocalType} :
    lookupG (updateG env e L) e = some L := by
  induction env with
  | nil =>
      simp [lookupG, updateG]
  | cons hd tl ih =>
      by_cases h : e = hd.1
      · simp [updateG, lookupG, h]
      · have hne : (e == hd.1) = false := beq_eq_false_iff_ne.mpr h
        simpa [updateG, lookupG, List.lookup, h, hne] using ih

/-- Lookup at a different endpoint is unchanged. -/
theorem lookupG_updateG_ne {env : GEnv} {e e' : Endpoint} {L : LocalType}
    (hne : e' ≠ e) :
    lookupG (updateG env e L) e' = lookupG env e' := by
  induction env with
  | nil =>
      have hbeq : (e' == e) = false := beq_eq_false_iff_ne.mpr hne
      simp [lookupG, updateG, List.lookup, hbeq]
  | cons hd tl ih =>
      by_cases h : e = hd.1
      · have hbeq : (e' == e) = false := beq_eq_false_iff_ne.mpr hne
        have hbeq' : (e' == hd.1) = false := by
          simpa [h] using (beq_eq_false_iff_ne.mpr hne)
        simp [updateG, lookupG, List.lookup, h, hbeq']
      · by_cases hy : e' = hd.1
        · simp [updateG, lookupG, List.lookup, h, hy]
        · have hbeq' : (e' == hd.1) = false := beq_eq_false_iff_ne.mpr hy
          simp [updateG, lookupG, List.lookup, h, hbeq']
          simpa [lookupG] using ih

/-! ## Directed Edge Buffers -/

/-- A buffer is a FIFO queue of values. -/
abbrev Buffer := List Value

/-- Buffers maps directed edges to their message queues.
    Each buffer holds messages from `e.sender` to `e.receiver`. -/
abbrev Buffers := List (Edge × Buffer)

/-- Lookup a buffer for a directed edge. -/
def lookupBuf (bufs : Buffers) (e : Edge) : Buffer :=
  bufs.lookup e |>.getD []

/-- Update a buffer for a directed edge. -/
def updateBuf (bufs : Buffers) (e : Edge) (buf : Buffer) : Buffers :=
  match bufs with
  | [] => [(e, buf)]
  | (e', buf') :: rest =>
    if e = e' then (e, buf) :: rest
    else (e', buf') :: updateBuf rest e buf

/-! ## Buffer Queue Operations -/
/-- Enqueue a value at a directed edge buffer. -/
def enqueueBuf (bufs : Buffers) (e : Edge) (v : Value) : Buffers :=
  updateBuf bufs e (lookupBuf bufs e ++ [v])

/-- Dequeue from a directed edge buffer (returns updated buffers and value). -/
def dequeueBuf (bufs : Buffers) (e : Edge) : Option (Buffers × Value) :=
  match lookupBuf bufs e with
  | [] => none
  | v :: vs => some (updateBuf bufs e vs, v)

/-! ## Buffer Lookup Preservation Lemmas -/
/-- Lookup at the updated edge returns the new buffer. -/
@[simp] theorem lookupBuf_updateBuf_eq {bufs : Buffers} {e : Edge} {buf : Buffer} :
    lookupBuf (updateBuf bufs e buf) e = buf := by
  induction bufs with
  | nil =>
      simp [lookupBuf, updateBuf, Option.getD]
  | cons hd tl ih =>
      by_cases h : e = hd.1
      · simp [updateBuf, lookupBuf, h, Option.getD]
      · have hne : (e == hd.1) = false := beq_eq_false_iff_ne.mpr h
        simpa [updateBuf, lookupBuf, List.lookup, h, hne, Option.getD] using ih

/-- Lookup at a different edge is unchanged. -/
theorem lookupBuf_updateBuf_ne {bufs : Buffers} {e e' : Edge} {buf : Buffer}
    (hne : e' ≠ e) :
    lookupBuf (updateBuf bufs e buf) e' = lookupBuf bufs e' := by
  induction bufs with
  | nil =>
      have hbeq : (e' == e) = false := beq_eq_false_iff_ne.mpr hne
      simp [lookupBuf, updateBuf, List.lookup, hbeq, Option.getD]
  | cons hd tl ih =>
      by_cases h : e = hd.1
      · have hbeq : (e' == e) = false := beq_eq_false_iff_ne.mpr hne
        have hbeq' : (e' == hd.1) = false := by
          simpa [h] using (beq_eq_false_iff_ne.mpr hne)
        simp [updateBuf, lookupBuf, List.lookup, h, hbeq', Option.getD]
      · by_cases hy : e' = hd.1
        · simp [updateBuf, lookupBuf, List.lookup, h, hy, Option.getD]
        · have hbeq' : (e' == hd.1) = false := beq_eq_false_iff_ne.mpr hy
          simp [updateBuf, lookupBuf, List.lookup, h, hbeq', Option.getD]
          simpa [lookupBuf] using ih

/-! ## Buffer Non-target Edge Corollaries -/
/-- Enqueue at a different edge doesn't change lookup. -/
theorem lookupBuf_enqueueBuf_ne {bufs : Buffers} {e e' : Edge} {v : Value}
    (hne : e' ≠ e) :
    lookupBuf (enqueueBuf bufs e v) e' = lookupBuf bufs e' := by
  simp only [enqueueBuf]
  exact lookupBuf_updateBuf_ne hne

/-- Dequeue at a different edge doesn't change lookup. -/
theorem lookupBuf_dequeueBuf_ne {bufs bufs' : Buffers} {e e' : Edge} {v : Value}
    (hDeq : dequeueBuf bufs e = some (bufs', v))
    (hne : e' ≠ e) :
    lookupBuf bufs' e' = lookupBuf bufs e' := by
  simp only [dequeueBuf] at hDeq
  split at hDeq
  · simp at hDeq
  · simp only [Option.some.injEq, Prod.mk.injEq] at hDeq
    rw [← hDeq.1]
    exact lookupBuf_updateBuf_ne hne


end
