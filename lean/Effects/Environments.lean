import Effects.LocalType
import Effects.Values
import Lean.Data.RBMap
import Batteries.Data.RBMap.Lemmas

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

open Lean

/-- SEnv maps variables to their value types (permutation-invariant). -/
abbrev SEnv := RBMap Var ValType compare

/-- Lookup a type in SEnv. -/
def lookupSEnv (env : SEnv) (x : Var) : Option ValType :=
  env.find? x

/-- Update or insert in SEnv. -/
def updateSEnv (env : SEnv) (x : Var) (T : ValType) : SEnv :=
  env.insert x T

/-- Union of SEnvs (left-biased on key collisions). -/
def SEnvUnion (S₁ S₂ : SEnv) : SEnv :=
  RBMap.mergeBy (fun _ v₁ _ => v₁) S₁ S₂

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

/-- DEnv maps directed edges to their in-flight type traces
    (permutation-invariant). -/
abbrev DEnv := RBMap Edge (List ValType) compare

/-- Union of DEnvs (left-biased on key collisions). -/
def DEnvUnion (D₁ D₂ : DEnv) : DEnv :=
  RBMap.mergeBy (fun _ v₁ _ => v₁) D₁ D₂

instance : Append DEnv := ⟨DEnvUnion⟩

/-- Lookup a type trace for a directed edge. -/
def lookupD (env : DEnv) (e : Edge) : List ValType :=
  env.findD e []

/-- Update or insert a type trace for a directed edge. -/
def updateD (env : DEnv) (e : Edge) (ts : List ValType) : DEnv :=
  env.insert e ts

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
  (RoleSet.allEdges sid roles).foldl (fun env e => env.insert e []) RBMap.empty

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
axiom initDEnv_lookup_mem (sid : SessionId) (roles : RoleSet) (e : Edge)
    (hMem : e ∈ RoleSet.allEdges sid roles) :
    lookupD (initDEnv sid roles) e = []

/-- Looking up an edge with a different sid in initDEnv returns none. -/
axiom initDEnv_lookup_none (sid : SessionId) (roles : RoleSet) (e : Edge)
    (hne : e.sid ≠ sid) :
    lookupD (initDEnv sid roles) e = []

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

axiom lookupSEnv_update_eq (env : SEnv) (x : Var) (T : ValType) :
    lookupSEnv (updateSEnv env x T) x = some T

axiom lookupSEnv_update_neq (env : SEnv) (x y : Var) (T : ValType) (hne : x ≠ y) :
    lookupSEnv (updateSEnv env x T) y = lookupSEnv env y

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

axiom lookupD_update_eq (env : DEnv) (e : Edge) (ts : List ValType) :
    lookupD (updateD env e ts) e = ts

axiom lookupD_update_neq (env : DEnv) (e e' : Edge) (ts : List ValType) (hne : e ≠ e') :
    lookupD (updateD env e ts) e' = lookupD env e'

@[simp] axiom lookupD_empty (e : Edge) : lookupD (RBMap.empty) e = []

/-! ## Session Renaming Infrastructure -/

/-- Session renaming: an injective function on session IDs. -/
structure SessionRenaming where
  f : SessionId → SessionId
  inj : ∀ s1 s2, f s1 = f s2 → s1 = s2

/-- Rename a value type by updating embedded session IDs. -/
def renameValType (ρ : SessionRenaming) : ValType → ValType
  | .unit => .unit
  | .bool => .bool
  | .nat => .nat
  | .string => .string
  | .prod T₁ T₂ => .prod (renameValType ρ T₁) (renameValType ρ T₂)
  | .chan sid role => .chan (ρ.f sid) role

/-- Rename an endpoint's session ID. -/
def renameEndpoint (ρ : SessionRenaming) (e : Endpoint) : Endpoint :=
  { sid := ρ.f e.sid, role := e.role }

/-- Rename an edge's session ID. -/
def renameEdge (ρ : SessionRenaming) (e : Edge) : Edge :=
  { sid := ρ.f e.sid, sender := e.sender, receiver := e.receiver }

mutual

/-- Rename a local type by renaming all value types it carries. -/
def renameLocalType (ρ : SessionRenaming) : LocalType → LocalType
  | .send r T L => .send r (renameValType ρ T) (renameLocalType ρ L)
  | .recv r T L => .recv r (renameValType ρ T) (renameLocalType ρ L)
  | .select r bs => .select r (renameBranches ρ bs)
  | .branch r bs => .branch r (renameBranches ρ bs)
  | .end_ => .end_
  | .var n => .var n
  | .mu L => .mu (renameLocalType ρ L)
termination_by L => sizeOf L

/-- Rename a list of labeled branches. -/
def renameBranches (ρ : SessionRenaming) : List (Label × LocalType) → List (Label × LocalType)
  | [] => []
  | (l, L) :: bs => (l, renameLocalType ρ L) :: renameBranches ρ bs
termination_by bs => sizeOf bs

end

/-- Rename a runtime value by updating any embedded endpoints. -/
def renameValue (ρ : SessionRenaming) : Value → Value
  | .unit => .unit
  | .bool b => .bool b
  | .nat n => .nat n
  | .string s => .string s
  | .prod v₁ v₂ => .prod (renameValue ρ v₁) (renameValue ρ v₂)
  | .chan e => .chan (renameEndpoint ρ e)

/-- Rename all endpoints in GEnv. -/
def renameGEnv (ρ : SessionRenaming) (G : GEnv) : GEnv :=
  G.map fun (e, L) => (renameEndpoint ρ e, renameLocalType ρ L)

/-- Rename all edges in DEnv. -/
def renameDEnv (ρ : SessionRenaming) (D : DEnv) : DEnv :=
  RBMap.fold
    (fun acc (e : Edge) (ts : List ValType) =>
      acc.insert (renameEdge ρ e) (ts.map (renameValType ρ)))
    RBMap.empty D

/-- Rename all edges in Buffers. -/
def renameBufs (ρ : SessionRenaming) (bufs : Buffers) : Buffers :=
  bufs.map fun (e, buf) => (renameEdge ρ e, buf.map (renameValue ρ))

/-! ## Renaming Injectivity Lemmas -/

/-- Renaming preserves value type equality (injective). -/
theorem renameValType_inj (ρ : SessionRenaming) {T1 T2 : ValType} :
    renameValType ρ T1 = renameValType ρ T2 → T1 = T2 := by
  intro h
  induction T1 generalizing T2 with
  | unit =>
      cases T2 with
      | unit =>
          cases h
          rfl
      | bool => cases h
      | nat => cases h
      | string => cases h
      | prod _ _ => cases h
      | chan _ _ => cases h
  | bool =>
      cases T2 with
      | unit => cases h
      | bool =>
          cases h
          rfl
      | nat => cases h
      | string => cases h
      | prod _ _ => cases h
      | chan _ _ => cases h
  | nat =>
      cases T2 with
      | unit => cases h
      | bool => cases h
      | nat =>
          cases h
          rfl
      | string => cases h
      | prod _ _ => cases h
      | chan _ _ => cases h
  | string =>
      cases T2 with
      | unit => cases h
      | bool => cases h
      | nat => cases h
      | string =>
          cases h
          rfl
      | prod _ _ => cases h
      | chan _ _ => cases h
  | prod T1a T1b ih1 ih2 =>
      cases T2 <;> simp [renameValType] at h
      case prod T2a T2b =>
        obtain ⟨h1, h2⟩ := h
        have h1' := ih1 h1
        have h2' := ih2 h2
        subst h1' h2'
        rfl
  | chan sid role =>
      cases T2 <;> simp [renameValType] at h
      case chan sid' role' =>
        obtain ⟨hSid, hRole⟩ := h
        have hSid' : sid = sid' := ρ.inj _ _ hSid
        subst hSid' hRole
        rfl

/-- Renaming preserves value type equality tests. -/
theorem renameValType_beq (ρ : SessionRenaming) (T1 T2 : ValType) :
    (renameValType ρ T1 == renameValType ρ T2) = (T1 == T2) := by
  by_cases h : T1 = T2
  · subst h
    simp
  · have hne : renameValType ρ T1 ≠ renameValType ρ T2 := by
      intro hEq
      exact h (renameValType_inj ρ hEq)
    have hbeq1 : (renameValType ρ T1 == renameValType ρ T2) = false :=
      beq_eq_false_iff_ne.mpr hne
    have hbeq2 : (T1 == T2) = false := beq_eq_false_iff_ne.mpr h
    simp [hbeq1, hbeq2]

/-- Renaming preserves endpoint equality (injective). -/
theorem renameEndpoint_inj (ρ : SessionRenaming) (e1 e2 : Endpoint) :
    renameEndpoint ρ e1 = renameEndpoint ρ e2 → e1 = e2 := by
  intro h
  have hsid : ρ.f e1.sid = ρ.f e2.sid := by
    have := congrArg Endpoint.sid h
    simp only [renameEndpoint] at this
    exact this
  have hrole : e1.role = e2.role := by
    have := congrArg Endpoint.role h
    simp only [renameEndpoint] at this
    exact this
  have hsid' : e1.sid = e2.sid := ρ.inj _ _ hsid
  cases e1; cases e2
  simp only at hsid' hrole
  subst hsid' hrole
  rfl

/-- Renaming preserves edge equality (injective). -/
theorem renameEdge_inj (ρ : SessionRenaming) (e1 e2 : Edge) :
    renameEdge ρ e1 = renameEdge ρ e2 → e1 = e2 := by
  intro h
  have hsid : ρ.f e1.sid = ρ.f e2.sid := by
    have := congrArg Edge.sid h
    simp only [renameEdge] at this
    exact this
  have hsender : e1.sender = e2.sender := by
    have := congrArg Edge.sender h
    simp only [renameEdge] at this
    exact this
  have hrecv : e1.receiver = e2.receiver := by
    have := congrArg Edge.receiver h
    simp only [renameEdge] at this
    exact this
  have hsid' : e1.sid = e2.sid := ρ.inj _ _ hsid
  cases e1; cases e2
  simp only at hsid' hsender hrecv
  subst hsid' hsender hrecv
  rfl

/-! ## Renaming Lookup Lemmas -/

/-- Looking up a renamed endpoint in a renamed GEnv. -/
theorem lookupG_rename (ρ : SessionRenaming) (G : GEnv) (e : Endpoint) :
    lookupG (renameGEnv ρ G) (renameEndpoint ρ e) =
      (lookupG G e).map (renameLocalType ρ) := by
  induction G with
  | nil => rfl
  | cons hd tl ih =>
    by_cases heq : e = hd.1
    case pos =>
      subst heq
      simp [renameGEnv, lookupG, List.lookup]
    case neg =>
      have hne : renameEndpoint ρ e ≠ renameEndpoint ρ hd.1 := fun h =>
        heq (renameEndpoint_inj ρ _ _ h)
      have hbeq1 : (e == hd.1) = false := beq_eq_false_iff_ne.mpr heq
      have hbeq2 : (renameEndpoint ρ e == renameEndpoint ρ hd.1) = false :=
        beq_eq_false_iff_ne.mpr hne
      simpa [renameGEnv, lookupG, List.lookup, hbeq1, hbeq2] using ih

/-- Looking up a renamed edge in a renamed DEnv. -/
axiom lookupD_rename (ρ : SessionRenaming) (D : DEnv) (e : Edge) :
    lookupD (renameDEnv ρ D) (renameEdge ρ e) =
      (lookupD D e).map (renameValType ρ)

/-- Looking up a renamed edge in renamed buffers. -/
theorem lookupBuf_rename (ρ : SessionRenaming) (bufs : Buffers) (e : Edge) :
    lookupBuf (renameBufs ρ bufs) (renameEdge ρ e) =
      (lookupBuf bufs e).map (renameValue ρ) := by
  induction bufs with
  | nil => simp only [renameBufs, lookupBuf, List.lookup, List.map, Option.getD]
  | cons hd tl ih =>
    simp only [renameBufs, List.map, lookupBuf, List.lookup, Option.getD]
    by_cases heq : e = hd.1
    case pos =>
      subst heq
      simp only [beq_self_eq_true]
    case neg =>
      have hne : renameEdge ρ e ≠ renameEdge ρ hd.1 := fun h =>
        heq (renameEdge_inj ρ _ _ h)
      have hbeq1 : (e == hd.1) = false := beq_eq_false_iff_ne.mpr heq
      have hbeq2 : (renameEdge ρ e == renameEdge ρ hd.1) = false :=
        beq_eq_false_iff_ne.mpr hne
      simp only [hbeq1, hbeq2]
      exact ih

/-! ## Inverse Lookup Lemmas -/

/-- If lookup succeeds in renamed GEnv, the preimage endpoint exists. -/
theorem lookupG_rename_inv (ρ : SessionRenaming) (G : GEnv) (e : Endpoint) (L : LocalType) :
    lookupG (renameGEnv ρ G) e = some L →
    ∃ e' L', e = renameEndpoint ρ e' ∧ L = renameLocalType ρ L' ∧ lookupG G e' = some L' := by
  intro h
  induction G with
  | nil =>
    simp only [renameGEnv, lookupG, List.lookup, List.map] at h
    exact Option.noConfusion h
  | cons hd tl ih =>
    simp only [renameGEnv, List.map, lookupG, List.lookup] at h
    by_cases heq : e = renameEndpoint ρ hd.1
    case pos =>
      simp only [heq, beq_self_eq_true, Option.some.injEq] at h
      refine ⟨hd.1, hd.2, heq, h.symm, ?_⟩
      simp only [lookupG, List.lookup, beq_self_eq_true]
    case neg =>
      have hbeq : (e == renameEndpoint ρ hd.1) = false := beq_eq_false_iff_ne.mpr heq
      simp only [hbeq] at h
      obtain ⟨e', L', he', hL', hLookup⟩ := ih h
      refine ⟨e', L', he', hL', ?_⟩
      simp only [lookupG, List.lookup]
      have hne : e' ≠ hd.1 := by
        intro heq'
        subst heq'
        exact heq he'
      simp only [beq_eq_false_iff_ne.mpr hne]
      exact hLookup

/-- If lookup succeeds (non-empty) in renamed DEnv, the preimage edge exists. -/
axiom lookupD_rename_inv (ρ : SessionRenaming) (D : DEnv) (e : Edge) :
    lookupD (renameDEnv ρ D) e ≠ [] →
    ∃ e', e = renameEdge ρ e' ∧
      lookupD (renameDEnv ρ D) e = (lookupD D e').map (renameValType ρ)

/-- If lookup succeeds (non-empty) in renamed buffers, the preimage edge exists. -/
theorem lookupBuf_rename_inv (ρ : SessionRenaming) (bufs : Buffers) (e : Edge) :
    lookupBuf (renameBufs ρ bufs) e ≠ [] →
    ∃ e', e = renameEdge ρ e' ∧
      lookupBuf (renameBufs ρ bufs) e = (lookupBuf bufs e').map (renameValue ρ) := by
  intro h
  induction bufs with
  | nil =>
    simp only [renameBufs, lookupBuf, List.lookup, List.map, Option.getD, ne_eq,
               not_true_eq_false] at h
  | cons hd tl ih =>
    simp only [renameBufs, List.map, lookupBuf, List.lookup, Option.getD] at h ⊢
    by_cases heq : e = renameEdge ρ hd.1
    case pos =>
      refine ⟨hd.1, heq, ?_⟩
      subst heq
      simp only [beq_self_eq_true]
    case neg =>
      have hbeq : (e == renameEdge ρ hd.1) = false := beq_eq_false_iff_ne.mpr heq
      simp only [hbeq] at h ⊢
      obtain ⟨e', he', hLookup⟩ := ih h
      have hne : e' ≠ hd.1 := by
        intro heq'
        subst heq'
        exact heq he'
      refine ⟨e', he', ?_⟩
      simp only [beq_eq_false_iff_ne.mpr hne]
      exact hLookup

end
