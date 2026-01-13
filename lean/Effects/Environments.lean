import Effects.LocalType
import Effects.Values

/-!
# MPST Environments

This module defines the runtime environments for multiparty session types:

- `Store`: Variable store mapping variables to runtime values
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

noncomputable section

/-! ## Variables -/

/-- Variables are strings. -/
abbrev Var := String

/-! ## Store: Variable → Value -/

/-- Store maps variables to runtime values. -/
abbrev Store := List (Var × Value)

/-- Lookup a value in the store. -/
def lookupStr (store : Store) (x : Var) : Option Value :=
  store.lookup x

/-- Update or insert a variable in the store. -/
def updateStr (store : Store) (x : Var) (v : Value) : Store :=
  match store with
  | [] => [(x, v)]
  | (y, w) :: rest =>
    if x = y then (x, v) :: rest
    else (y, w) :: updateStr rest x v

/-! ## SEnv: Variable → ValType -/

/-- SEnv maps variables to their value types. -/
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

/-- Enqueue a value at a directed edge buffer. -/
def enqueueBuf (bufs : Buffers) (e : Edge) (v : Value) : Buffers :=
  updateBuf bufs e (lookupBuf bufs e ++ [v])

/-- Dequeue from a directed edge buffer (returns updated buffers and value). -/
def dequeueBuf (bufs : Buffers) (e : Edge) : Option (Buffers × Value) :=
  match lookupBuf bufs e with
  | [] => none
  | v :: vs => some (updateBuf bufs e vs, v)

/-! ## DEnv: Directed Edge → Type Trace -/

/-- DEnv maps directed edges to their in-flight type traces.
    This tracks the types of messages that have been sent but not yet received
    on each directed edge. -/
abbrev DEnv := List (Edge × List ValType)

/-- Lookup a type trace for a directed edge. -/
def lookupD (env : DEnv) (e : Edge) : List ValType :=
  env.lookup e |>.getD []

/-- Update a type trace for a directed edge. -/
def updateD (env : DEnv) (e : Edge) (ts : List ValType) : DEnv :=
  match env with
  | [] => [(e, ts)]
  | (e', ts') :: rest =>
    if e = e' then (e, ts) :: rest
    else (e', ts') :: updateD rest e ts

/-- Append a type to the in-flight trace. -/
def appendD (env : DEnv) (e : Edge) (T : ValType) : DEnv :=
  updateD env e (lookupD env e ++ [T])

/-- Pop a type from the in-flight trace. -/
def popD (env : DEnv) (e : Edge) : Option (DEnv × ValType) :=
  match lookupD env e with
  | [] => none
  | T :: ts => some (updateD env e ts, T)

/-! ## Session Management -/

/-- Initialize empty buffers for all directed edges between roles. -/
def initBuffers (sid : SessionId) (roles : RoleSet) : Buffers :=
  (RoleSet.allEdges sid roles).map fun e => (e, [])

/-- Initialize empty type traces for all directed edges. -/
def initDEnv (sid : SessionId) (roles : RoleSet) : DEnv :=
  (RoleSet.allEdges sid roles).map fun e => (e, [])

/-! ## Environment Lemmas -/

theorem lookupStr_update_eq (store : Store) (x : Var) (v : Value) :
    lookupStr (updateStr store x v) x = some v := by
  induction store with
  | nil =>
    simp only [updateStr, lookupStr, List.lookup, beq_self_eq_true]
  | cons hd tl ih =>
    simp only [updateStr]
    split_ifs with h
    · simp only [lookupStr, List.lookup, beq_self_eq_true]
    · simp only [lookupStr, List.lookup]
      have hne : (x == hd.1) = false := beq_eq_false_iff_ne.mpr h
      simp only [hne]
      exact ih

theorem lookupStr_update_neq (store : Store) (x y : Var) (v : Value) (hne : x ≠ y) :
    lookupStr (updateStr store x v) y = lookupStr store y := by
  induction store with
  | nil =>
    simp only [updateStr, lookupStr, List.lookup]
    have h : (y == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
    simp only [h]
  | cons hd tl ih =>
    simp only [updateStr]
    split_ifs with h
    · -- h : x = hd.1, so y ≠ x implies y ≠ hd.1
      simp only [lookupStr, List.lookup]
      have hyx : (y == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
      have hyh : (y == hd.1) = false := beq_eq_false_iff_ne.mpr (h ▸ Ne.symm hne)
      simp only [hyx, hyh]
    · simp only [lookupStr, List.lookup]
      by_cases hy : y = hd.1
      · simp only [hy, beq_self_eq_true]
      · have hne' : (y == hd.1) = false := beq_eq_false_iff_ne.mpr hy
        simp only [hne']
        exact ih

theorem lookupSEnv_update_eq (env : SEnv) (x : Var) (T : ValType) :
    lookupSEnv (updateSEnv env x T) x = some T := by
  induction env with
  | nil =>
    simp only [updateSEnv, lookupSEnv, List.lookup, beq_self_eq_true]
  | cons hd tl ih =>
    simp only [updateSEnv]
    split_ifs with h
    · simp only [lookupSEnv, List.lookup, beq_self_eq_true]
    · simp only [lookupSEnv, List.lookup]
      have hne : (x == hd.1) = false := beq_eq_false_iff_ne.mpr h
      simp only [hne]
      exact ih

theorem lookupSEnv_update_neq (env : SEnv) (x y : Var) (T : ValType) (hne : x ≠ y) :
    lookupSEnv (updateSEnv env x T) y = lookupSEnv env y := by
  induction env with
  | nil =>
    simp only [updateSEnv, lookupSEnv, List.lookup]
    have h : (y == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
    simp only [h]
  | cons hd tl ih =>
    simp only [updateSEnv]
    split_ifs with h
    · -- h : x = hd.1, so y ≠ x implies y ≠ hd.1
      simp only [lookupSEnv, List.lookup]
      have hyx : (y == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
      have hyh : (y == hd.1) = false := beq_eq_false_iff_ne.mpr (h ▸ Ne.symm hne)
      simp only [hyx, hyh]
    · simp only [lookupSEnv, List.lookup]
      by_cases hy : y = hd.1
      · simp only [hy, beq_self_eq_true]
      · have hne' : (y == hd.1) = false := beq_eq_false_iff_ne.mpr hy
        simp only [hne']
        exact ih

theorem lookupG_update_eq (env : GEnv) (e : Endpoint) (L : LocalType) :
    lookupG (updateG env e L) e = some L := by
  induction env with
  | nil =>
    simp only [updateG, lookupG, List.lookup, beq_self_eq_true]
  | cons hd tl ih =>
    simp only [updateG]
    split_ifs with h
    · simp only [lookupG, List.lookup, beq_self_eq_true]
    · simp only [lookupG, List.lookup]
      have hne : (e == hd.1) = false := beq_eq_false_iff_ne.mpr h
      simp only [hne]
      exact ih

theorem lookupG_update_neq (env : GEnv) (e e' : Endpoint) (L : LocalType) (hne : e ≠ e') :
    lookupG (updateG env e L) e' = lookupG env e' := by
  induction env with
  | nil =>
    simp only [updateG, lookupG, List.lookup]
    have h : (e' == e) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
    simp only [h]
  | cons hd tl ih =>
    simp only [updateG]
    split_ifs with h
    · -- h : e = hd.1, so e' ≠ e implies e' ≠ hd.1
      simp only [lookupG, List.lookup]
      have h1 : (e' == e) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
      have h2 : (e' == hd.1) = false := beq_eq_false_iff_ne.mpr (h ▸ Ne.symm hne)
      simp only [h1, h2]
    · simp only [lookupG, List.lookup]
      by_cases hy : e' = hd.1
      · simp only [hy, beq_self_eq_true]
      · have hne' : (e' == hd.1) = false := beq_eq_false_iff_ne.mpr hy
        simp only [hne']
        exact ih

theorem lookupBuf_update_eq (bufs : Buffers) (e : Edge) (buf : Buffer) :
    lookupBuf (updateBuf bufs e buf) e = buf := by
  induction bufs with
  | nil =>
    simp only [updateBuf, lookupBuf, List.lookup, beq_self_eq_true, Option.getD]
  | cons hd tl ih =>
    simp only [updateBuf]
    split_ifs with h
    · simp only [lookupBuf, List.lookup, beq_self_eq_true, Option.getD]
    · simp only [lookupBuf, List.lookup]
      have hne : (e == hd.1) = false := beq_eq_false_iff_ne.mpr h
      simp only [hne, Option.getD]
      have ih' := ih
      simp only [lookupBuf, Option.getD] at ih'
      exact ih'

theorem lookupBuf_update_neq (bufs : Buffers) (e e' : Edge) (buf : Buffer) (hne : e ≠ e') :
    lookupBuf (updateBuf bufs e buf) e' = lookupBuf bufs e' := by
  induction bufs with
  | nil =>
    simp only [updateBuf, lookupBuf, List.lookup]
    have h : (e' == e) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
    simp only [h, Option.getD]
  | cons hd tl ih =>
    simp only [updateBuf]
    split_ifs with h
    · -- h : e = hd.1, so e' ≠ e implies e' ≠ hd.1
      simp only [lookupBuf, List.lookup]
      have h1 : (e' == e) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
      have h2 : (e' == hd.1) = false := beq_eq_false_iff_ne.mpr (h ▸ Ne.symm hne)
      simp only [h1, h2, Option.getD]
    · simp only [lookupBuf, List.lookup]
      by_cases hy : e' = hd.1
      · simp only [hy, beq_self_eq_true, Option.getD]
      · have hne' : (e' == hd.1) = false := beq_eq_false_iff_ne.mpr hy
        simp only [hne', Option.getD]
        have ih' := ih
        simp only [lookupBuf, Option.getD] at ih'
        exact ih'

theorem lookupD_update_eq (env : DEnv) (e : Edge) (ts : List ValType) :
    lookupD (updateD env e ts) e = ts := by
  induction env with
  | nil =>
    simp only [updateD, lookupD, List.lookup, beq_self_eq_true, Option.getD]
  | cons hd tl ih =>
    simp only [updateD]
    split_ifs with h
    · simp only [lookupD, List.lookup, beq_self_eq_true, Option.getD]
    · simp only [lookupD, List.lookup]
      have hne : (e == hd.1) = false := beq_eq_false_iff_ne.mpr h
      simp only [hne, Option.getD]
      have ih' := ih
      simp only [lookupD, Option.getD] at ih'
      exact ih'

theorem lookupD_update_neq (env : DEnv) (e e' : Edge) (ts : List ValType) (hne : e ≠ e') :
    lookupD (updateD env e ts) e' = lookupD env e' := by
  induction env with
  | nil =>
    simp only [updateD, lookupD, List.lookup]
    have h : (e' == e) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
    simp only [h, Option.getD]
  | cons hd tl ih =>
    simp only [updateD]
    split_ifs with h
    · -- h : e = hd.1, so e' ≠ e implies e' ≠ hd.1
      simp only [lookupD, List.lookup]
      have h1 : (e' == e) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
      have h2 : (e' == hd.1) = false := beq_eq_false_iff_ne.mpr (h ▸ Ne.symm hne)
      simp only [h1, h2, Option.getD]
    · simp only [lookupD, List.lookup]
      by_cases hy : e' = hd.1
      · simp only [hy, beq_self_eq_true, Option.getD]
      · have hne' : (e' == hd.1) = false := beq_eq_false_iff_ne.mpr hy
        simp only [hne', Option.getD]
        have ih' := ih
        simp only [lookupD, Option.getD] at ih'
        exact ih'

end
