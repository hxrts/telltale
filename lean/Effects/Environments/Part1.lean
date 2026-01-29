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

open Batteries

/-- SEnv maps variables to their value types (extensional). -/
abbrev SEnv := Var → Option ValType

/-- Lookup a type in SEnv. -/
def lookupSEnv (env : SEnv) (x : Var) : Option ValType :=
  env x

/-- Update or insert in SEnv. -/
def updateSEnv (env : SEnv) (x : Var) (T : ValType) : SEnv :=
  fun y => if y = x then some T else env y

instance : EmptyCollection SEnv := ⟨fun _ => none⟩

@[simp] theorem lookupSEnv_empty (x : Var) : lookupSEnv (∅ : SEnv) x = none := by
  rfl

/-- Union of SEnvs (left-biased on key collisions). -/
def SEnvUnion (S₁ S₂ : SEnv) : SEnv :=
  fun x =>
    match S₁ x with
    | some T => some T
    | none => S₂ x

instance : Append SEnv := ⟨SEnvUnion⟩

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

/-! ## DEnv: Directed Edge → Type Trace -/

/-- DEnv maps directed edges to their in-flight type traces (extensional). -/
abbrev DEnv := Edge → Option (List ValType)

/-- Lookup helper (dot notation). -/
def DEnv.find? (env : DEnv) (e : Edge) : Option (List ValType) :=
  env e

instance : EmptyCollection DEnv := ⟨fun _ => none⟩

/-- Union of DEnvs (left-biased on key collisions). -/
def DEnvUnion (D₁ D₂ : DEnv) : DEnv :=
  fun e =>
    match D₁ e with
    | some ts => some ts
    | none => D₂ e

instance : Append DEnv := ⟨DEnvUnion⟩

/-- Lookup a type trace for a directed edge. -/
def lookupD (env : DEnv) (e : Edge) : List ValType :=
  (env e).getD []

/-- Update or insert a type trace for a directed edge. -/
def updateD (env : DEnv) (e : Edge) (ts : List ValType) : DEnv :=
  fun e' => if e' = e then some ts else env e'

/-- Lookup after update on the same edge. -/
theorem lookupD_update_eq (env : DEnv) (e : Edge) (ts : List ValType) :
    lookupD (updateD env e ts) e = ts := by
  simp [lookupD, updateD]

/-- Lookup after update on a different edge. -/
theorem lookupD_update_neq (env : DEnv) (e e' : Edge) (ts : List ValType) (hne : e ≠ e') :
    lookupD (updateD env e ts) e' = lookupD env e' := by
  simp [lookupD, updateD, hne]

@[simp] theorem lookupD_empty (e : Edge) : lookupD (∅ : DEnv) e = [] := by
  rfl

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
  fun e => if e ∈ RoleSet.allEdges sid roles then some [] else none

/-- Empty DEnv lookup via `find?` always returns none. -/
@[simp] theorem DEnv_find?_empty (e : Edge) :
    (∅ : DEnv).find? e = none := by
  rfl

/-- Looking up an edge in initBuffers returns empty if edge is in allEdges. -/
theorem initBuffers_lookup_mem (sid : SessionId) (roles : RoleSet) (e : Edge)
    (hMem : e ∈ RoleSet.allEdges sid roles) :
    (initBuffers sid roles).lookup e = some [] := by
  simp only [initBuffers]
  generalize hEdges : RoleSet.allEdges sid roles = edges at hMem
  clear hEdges
  induction edges with
  | nil => simp only [List.mem_nil_iff] at hMem
  | cons hd tl ih =>
    simp only [List.map, List.lookup]
    simp only [List.mem_cons] at hMem
    cases hMem with
    | inl heq =>
      subst heq
      simp only [beq_self_eq_true]
    | inr hTl =>
      by_cases heq : e = hd
      · subst heq; simp only [beq_self_eq_true]
      · have hNeq : (e == hd) = false := beq_eq_false_iff_ne.mpr heq
        simp only [hNeq]
        exact ih hTl

/-- Looking up an edge in initDEnv returns empty if edge is in allEdges. -/
theorem initDEnv_lookup_mem (sid : SessionId) (roles : RoleSet) (e : Edge)
    (_hMem : e ∈ RoleSet.allEdges sid roles) :
    lookupD (initDEnv sid roles) e = [] := by
  simp [initDEnv, lookupD, _hMem]

/-- Looking up an edge with a different sid in initDEnv returns none. -/
theorem initDEnv_lookup_none (sid : SessionId) (roles : RoleSet) (e : Edge)
    (_hne : e.sid ≠ sid) :
    lookupD (initDEnv sid roles) e = [] := by
  have hNot : e ∉ RoleSet.allEdges sid roles := by
    intro hmem
    exact _hne (RoleSet.allEdges_sid sid roles e hmem)
  simp [initDEnv, lookupD, hNot]

/-- If initBuffers returns none, the edge is not in the role edges. -/
theorem initBuffers_not_mem_of_lookup_none (sid : SessionId) (roles : RoleSet) (e : Edge)
    (h : (initBuffers sid roles).lookup e = none) :
    e ∉ RoleSet.allEdges sid roles := by
  -- Any edge in allEdges would be found with an empty buffer.
  intro hMem
  have hSome := initBuffers_lookup_mem sid roles e hMem
  exact Option.noConfusion (hSome.symm.trans h)

/-- initBuffers returns none for edges not in allEdges. -/
theorem initBuffers_lookup_none_of_notin (sid : SessionId) (roles : RoleSet) (e : Edge)
    (hNot : e ∉ RoleSet.allEdges sid roles) :
    (initBuffers sid roles).lookup e = none := by
  simp only [initBuffers]
  generalize hEdges : RoleSet.allEdges sid roles = edges at hNot
  clear hEdges
  induction edges with
  | nil =>
      simp
  | cons hd tl ih =>
      simp only [List.mem_cons, not_or] at hNot
      simp only [List.map, List.lookup]
      have hne : (e == hd) = false := beq_eq_false_iff_ne.mpr hNot.1
      simp only [hne]
      exact ih hNot.2

/-- Looking up an edge with a different sid in initBuffers returns none. -/
theorem initBuffers_lookup_none (sid : SessionId) (roles : RoleSet) (e : Edge)
    (hne : e.sid ≠ sid) :
    (initBuffers sid roles).lookup e = none := by
  simp only [initBuffers]
  -- Every edge in allEdges has .sid = sid, so e cannot be in the list
  have hNotIn : e ∉ RoleSet.allEdges sid roles := by
    intro hmem
    exact hne (RoleSet.allEdges_sid sid roles e hmem)
  -- Use induction with the membership constraint carried through
  generalize hlist : RoleSet.allEdges sid roles = edges at hNotIn
  clear hlist
  induction edges with
  | nil => simp only [List.map, List.lookup]
  | cons hd tl ih =>
    simp only [List.mem_cons, not_or] at hNotIn
    simp only [List.map, List.lookup]
    have hNeEdge : e ≠ hd := hNotIn.1
    have hBeqFalse : (e == hd) = false := beq_eq_false_iff_ne.mpr hNeEdge
    simp only [hBeqFalse]
    exact ih hNotIn.2

/-- initDEnv has no entry for edges outside allEdges. -/
theorem initDEnv_find?_none_of_notin (sid : SessionId) (roles : RoleSet) (e : Edge)
    (hNot : e ∉ RoleSet.allEdges sid roles) :
    (initDEnv sid roles).find? e = none := by
  simp [initDEnv, hNot]

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
  simp [lookupSEnv, updateSEnv]

theorem lookupSEnv_update_neq (env : SEnv) (x y : Var) (T : ValType) (hne : x ≠ y) :
    lookupSEnv (updateSEnv env x T) y = lookupSEnv env y := by
  simp [lookupSEnv, updateSEnv, hne]

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

/-- If (e', S') ∈ updateG env e L, then either (e' = e and S' = L), or (e', S') was in env. -/
theorem updateG_mem_of (env : GEnv) (e : Endpoint) (L : LocalType) (e' : Endpoint) (S' : LocalType)
    (h : (e', S') ∈ updateG env e L) :
    (e' = e ∧ S' = L) ∨ (e', S') ∈ env := by
  induction env with
  | nil =>
    simp only [updateG, List.mem_singleton] at h
    exact Or.inl (Prod.mk.inj h)
  | cons hd tl ih =>
    simp only [updateG] at h
    split_ifs at h with heq
    · -- e = hd.1: replaced the head
      simp only [List.mem_cons] at h
      cases h with
      | inl hhead =>
        exact Or.inl (Prod.mk.inj hhead)
      | inr htl =>
        exact Or.inr (List.mem_cons_of_mem _ htl)
    · -- e ≠ hd.1: head preserved, recurse
      simp only [List.mem_cons] at h
      cases h with
      | inl hhead =>
        exact Or.inr (List.mem_cons.mpr (Or.inl hhead))
      | inr htl =>
        cases ih htl with
        | inl heq' => exact Or.inl heq'
        | inr hmem => exact Or.inr (List.mem_cons.mpr (Or.inr hmem))

/-- updateG preserves supply_fresh: if all endpoints in env have sid < supply,
    and e.sid < supply, then all endpoints in (updateG env e L) have sid < supply. -/
theorem updateG_preserves_supply_fresh (env : GEnv) (e : Endpoint) (L : LocalType)
    (supply : SessionId)
    (hFresh : ∀ e' S', (e', S') ∈ env → e'.sid < supply)
    (heFresh : e.sid < supply) :
    ∀ e' S', (e', S') ∈ updateG env e L → e'.sid < supply := by
  intro e' S' hMem
  cases updateG_mem_of env e L e' S' hMem with
  | inl heq =>
    rw [heq.1]
    exact heFresh
  | inr hmem =>
    exact hFresh e' S' hmem

/-- If lookupG returns some L, then (e, L) is in the list. -/
theorem lookupG_mem (env : GEnv) (e : Endpoint) (L : LocalType)
    (h : lookupG env e = some L) :
    (e, L) ∈ env := by
  simp only [lookupG] at h
  induction env with
  | nil =>
    simp only [List.lookup] at h
    exact Option.noConfusion h
  | cons hd tl ih =>
    simp only [List.lookup] at h
    split at h
    · simp only [Option.some.injEq] at h
      rename_i heq
      simp only [beq_iff_eq] at heq
      simp only [List.mem_cons]
      left
      exact Prod.ext heq h.symm
    · simp only [List.mem_cons]
      right
      exact ih h

/-- If lookupG returns some L, then e.sid < supply (using supply_fresh_G). -/
theorem lookupG_supply_fresh (env : GEnv) (e : Endpoint) (L : LocalType)
    (supply : SessionId)
    (hFresh : ∀ e' S', (e', S') ∈ env → e'.sid < supply)
    (h : lookupG env e = some L) :
    e.sid < supply := by
  have hMem := lookupG_mem env e L h
  exact hFresh e L hMem

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

-- lookupD lemmas are defined above near DEnv.


end
