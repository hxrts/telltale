import Protocol.Typing.Judgments

/-! # MPST Process Typing: Compatibility

This module defines compatibility predicates for process typing. -/

/-
The Problem. Process typing requires compatibility checks between local types,
contexts, and actions. We need coinductive compatibility for recursive types
and split-context reasoning for parallel composition.

Solution Structure. We define:
1. Coinductive compatibility for local type pairs
2. Context splitting for parallel composition
3. Compatibility lemmas used by the typing judgment
-/

/-! ## Key Judgments

- `HasTypeProcN n S G D P`: Process P is well-typed under environments S, G, D
  with maximum session ID n
- `WTConfigN n S G D C`: Configuration C is well-typed

## Typing Rules

- **Skip**: `⊢ skip` (always well-typed)
- **Seq**: `⊢ P` and `⊢ Q` implies `⊢ seq P Q`
- **Par**: `⊢ P` and `⊢ Q` with split contexts implies `⊢ par P Q`
- **Send**: If `S[k] = chan (sid, r)` and `G[sid,r] = !q(T).L` and `S[x] = T`,
            then `⊢ send k x` and G[sid,r] ↦ L
- **Recv**: If `S[k] = chan (sid, r)` and `G[sid,r] = ?p(T).L`,
            then `⊢ recv k x` and G[sid,r] ↦ L, S[x] ↦ T
- **Select**: If `S[k] = chan (sid, r)` and `G[sid,r] = ⊕q{ℓᵢ: Lᵢ}`,
              then `⊢ select k ℓⱼ` and G[sid,r] ↦ Lⱼ
- **Branch**: If `S[k] = chan (sid, r)` and `G[sid,r] = &p{ℓᵢ: Lᵢ}`,
              then `⊢ branch k [(ℓᵢ, Pᵢ)]` if each Pᵢ is typed under Lᵢ
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical
open Batteries

section

/-! ## Global Compatibility (Coinductive) -/

/-- GStep: projection of TypedStep to G/D (for compatibility closure). -/
def GStep (G : GEnv) (D : DEnv) (G' : GEnv) (D' : DEnv) : Prop :=
  -- Existential projection of a TypedStep on G/D.
  ∃ Ssh Sown store bufs P Sown' store' bufs' P',
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'

/-! ## Compatibility (coinductive closure) -/

/-- Compatibility: readiness now + closure under GStep. -/
coinductive Compatible : GEnv → DEnv → Prop where
  | mk {G : GEnv} {D : DEnv} :
      -- Compatibility exposes immediate readiness and step closure.
      SendReady G D →
      SelectReady G D →
      (∀ {G' D'}, GStep G D G' D' → Compatible G' D') →
      Compatible G D

/-- Extract SendReady from Compatible. -/
theorem Compatible_to_SendReady {G : GEnv} {D : DEnv} :
    Compatible G D → SendReady G D := by
  -- Compatibility carries SendReady as a field.
  intro h
  cases h with
  | mk hSend _ _ => exact hSend

/-- Extract SelectReady from Compatible. -/
theorem Compatible_to_SelectReady {G : GEnv} {D : DEnv} :
    Compatible G D → SelectReady G D := by
  -- Compatibility carries SelectReady as a field.
  intro h
  cases h with
  | mk _ hSelect _ => exact hSelect

/-- Compatibility is preserved by any TypedStep. -/
theorem Compatible_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    Compatible G D →
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    Compatible G' D' := by
  -- Use the step-closure field with the projected GStep witness.
  intro hCompat hTS
  cases hCompat with
  | mk _ _ hClosed =>
      exact hClosed ⟨Ssh, Sown, store, bufs, P, Sown', store', bufs', P', hTS⟩

/-! ## LocalTypeR.WellFormed Predicate -/

/-- Well-formed process configuration.

    **Combines all invariants**: A process P with state (G, D, S, store, bufs)
    is well-formed if:
    1. Store is typed by S and G
    2. Buffers are typed by D
    3. G and D are coherent (including head/label refinements)
    4. G and D are globally compatible (coinductive readiness)
    5. Process P has pre-update style typing

    This predicate is preserved by TypedStep transitions. -/
def LocalTypeR.WellFormed (G : GEnv) (D : DEnv) (Ssh : SEnv) (Sown : OwnedEnv)
    (store : VarStore) (bufs : Buffers) (P : Process) : Prop :=
  StoreTypedStrong G (SEnvAll Ssh Sown) store ∧
  BuffersTyped G D bufs ∧
  Coherent G D ∧
  HeadCoherent G D ∧
  ValidLabels G D bufs ∧
  Compatible G D ∧
  DisjointS Ssh (OwnedEnv.all Sown) ∧
  OwnedDisjoint Sown ∧
  DConsistent G D ∧
  ∃ S' G' W Δ, HasTypeProcPreOut Ssh Sown G P S' G' W Δ ∧ DisjointS Sown.right S'.left

/-- Complete well-formedness: core invariants plus role-completeness of GEnv. -/
def WellFormedComplete (G : GEnv) (D : DEnv) (Ssh : SEnv) (Sown : OwnedEnv)
    (store : VarStore) (bufs : Buffers) (P : Process) : Prop :=
  LocalTypeR.WellFormed G D Ssh Sown store bufs P ∧ RoleComplete G

/-- WellFormedComplete implies LocalTypeR.WellFormed (projection). -/
theorem WellFormedComplete.toWellFormed
    {G : GEnv} {D : DEnv} {Ssh : SEnv} {Sown : OwnedEnv}
    {store : VarStore} {bufs : Buffers} {P : Process} :
    WellFormedComplete G D Ssh Sown store bufs P →
    LocalTypeR.WellFormed G D Ssh Sown store bufs P := by
  -- Drop the RoleComplete component.
  intro h
  exact h.1

/-! ## Support Lemmas for Preservation -/

/-- DisjointG: left lookup implies right is none. -/
theorem DisjointG_lookup_left {G₁ G₂ : GEnv} {e : Endpoint} {L : LocalType} :
    DisjointG G₁ G₂ →
    lookupG G₁ e = some L →
    lookupG G₂ e = none := by
  intro hDisj hLookup
  have hSid : e.sid ∈ SessionsOf G₁ := ⟨e, L, hLookup, rfl⟩
  have hNoSid : e.sid ∉ SessionsOf G₂ := by
    intro hSid2
    have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := by
      exact ⟨hSid, hSid2⟩
    have hEmpty := hDisj
    have : (SessionsOf G₁ ∩ SessionsOf G₂) = ∅ := hEmpty
    have hContra : e.sid ∈ (∅ : Set SessionId) := by
      simpa [this] using hInter
    exact hContra.elim
  by_contra hSome
  cases hLookup2 : lookupG G₂ e with
  | none => exact (hSome hLookup2)
  | some L2 =>
      have hSid2 : e.sid ∈ SessionsOf G₂ := ⟨e, L2, hLookup2, rfl⟩
      exact (hNoSid hSid2)

/-- If a session ID is not present in G, lookup at any endpoint with that ID is none. -/
theorem lookupG_none_of_not_session {G : GEnv} {e : Endpoint} :
    e.sid ∉ SessionsOf G →
    lookupG G e = none := by
  intro hNot
  cases hLookup : lookupG G e with
  | none => simp
  | some L =>
      have hSid : e.sid ∈ SessionsOf G := ⟨e, L, hLookup, rfl⟩
      exact (hNot hSid).elim

theorem DisjointD_lookup_left {D₁ D₂ : DEnv} {e : Edge} {ts : List ValType} :
    DisjointD D₁ D₂ →
    D₁.find? e = some ts →
    D₂.find? e = none := by
  intro hDisj hFind
  by_contra hSome
  cases hFind2 : D₂.find? e with
  | none => exact (hSome hFind2)
  | some ts2 =>
      have hSid1 : e.sid ∈ SessionsOfD D₁ := by
        exact ⟨e, ts, hFind, rfl⟩
      have hSid2 : e.sid ∈ SessionsOfD D₂ := by
        exact ⟨e, ts2, hFind2, rfl⟩
      have hInter : e.sid ∈ SessionsOfD D₁ ∩ SessionsOfD D₂ := by
        exact ⟨hSid1, hSid2⟩
      have hEmpty : SessionsOfD D₁ ∩ SessionsOfD D₂ = ∅ := hDisj
      have : e.sid ∈ (∅ : Set SessionId) := by
        simpa [hEmpty] using hInter
      exact this.elim

theorem DisjointD_lookup_right {D₁ D₂ : DEnv} {e : Edge} {ts : List ValType} :
    DisjointD D₁ D₂ →
    D₂.find? e = some ts →
    D₁.find? e = none := by
  intro hDisj hFind
  have hDisj' : DisjointD D₂ D₁ := by
    simpa [DisjointD, Set.inter_comm] using hDisj
  exact DisjointD_lookup_left (D₁:=D₂) (D₂:=D₁) hDisj' hFind

def insertPairD (acc : DEnv) (p : Edge × List ValType) : DEnv :=
  updateD acc p.1 p.2

theorem findD_update_eq (env : DEnv) (e : Edge) (ts : List ValType) :
    (updateD env e ts).find? e = some ts := by
  have hEq : compare e e = .eq := by
    simp
  simpa [updateD] using
    (RBMap.find?_insert_of_eq (t := env.map) (k := e) (v := ts) (k' := e) hEq)

theorem findD_update_neq (env : DEnv) (e e' : Edge) (ts : List ValType) (hne : e ≠ e') :
    (updateD env e ts).find? e' = env.find? e' := by
  have hne' : compare e' e ≠ .eq := by
    intro hEq
    exact hne (by symm; exact (Edge.compare_eq_iff_eq e' e).1 hEq)
  have h' : (env.map.insert e ts).find? e' = env.map.find? e' := by
    simpa using (RBMap.find?_insert_of_ne (t := env.map) (k := e) (v := ts) (k' := e') hne')
  have h'' : (updateD env e ts).find? e' = env.map.find? e' := by
    simpa [updateD] using h'
  simpa [DEnv.find?] using h''

theorem findD_foldl_insert_preserve
    (L : List (Edge × List ValType)) (env : DEnv) (e : Edge) (ts : List ValType)
    (hfind : env.find? e = some ts)
    (hSame : ∀ ts', (e, ts') ∈ L → ts' = ts) :
    (L.foldl insertPairD env).find? e = some ts := by
  induction L generalizing env with
  | nil =>
      simpa using hfind
  | cons p L ih =>
      cases p with
      | mk e' ts' =>
          have hSame' : ∀ ts'', (e, ts'') ∈ L → ts'' = ts := by
            intro ts'' hmem
            exact hSame ts'' (List.mem_cons_of_mem _ hmem)
          by_cases hEq : e' = e
          · cases hEq
            have hts' : ts' = ts := hSame ts' (by simp)
            cases hts'
            have hfind' : (updateD env e ts).find? e = some ts :=
              findD_update_eq env e ts
            simpa [List.foldl, insertPairD] using
              (ih (env := updateD env e ts) (hfind := hfind') (hSame := hSame'))
          · have hfind' : (updateD env e' ts').find? e = some ts := by
              have h' : (updateD env e' ts').find? e = env.find? e :=
                findD_update_neq env e' e ts' hEq
              simpa [hfind] using h'
            simpa [List.foldl, insertPairD] using
              (ih (env := updateD env e' ts') (hfind := hfind') (hSame := hSame'))

theorem findD_foldl_insert_of_mem
    (L : List (Edge × List ValType)) (env : DEnv) (e : Edge) (ts : List ValType)
    (hmem : (e, ts) ∈ L)
    (hSame : ∀ ts', (e, ts') ∈ L → ts' = ts) :
    (L.foldl insertPairD env).find? e = some ts := by
  induction L generalizing env with
  | nil =>
      cases hmem
  | cons p L ih =>
      cases p with
      | mk e' ts' =>
          have hSame' : ∀ ts'', (e, ts'') ∈ L → ts'' = ts := by
            intro ts'' hmem'
            exact hSame ts'' (List.mem_cons_of_mem _ hmem')
          cases hmem with
          | head _ =>
              have hfind' : (updateD env e ts).find? e = some ts :=
                findD_update_eq env e ts
              simpa [List.foldl, insertPairD] using
                (findD_foldl_insert_preserve (L:=L) (env:=updateD env e ts)
                  (e:=e) (ts:=ts) hfind' hSame')
          | tail _ htail =>
              simpa [List.foldl, insertPairD] using
                (ih (env := updateD env e' ts') (hmem := htail) (hSame := hSame'))

theorem findD_foldl_insert_notin
    (L : List (Edge × List ValType)) (env : DEnv) (e : Edge)
    (hNot : ∀ ts, (e, ts) ∈ L → False) :
    (L.foldl insertPairD env).find? e = env.find? e := by
  induction L generalizing env with
  | nil =>
      rfl
  | cons p L ih =>
      cases p with
      | mk e' ts' =>
          have hNot' : ∀ ts, (e, ts) ∈ L → False := by
            intro ts hmem
            exact hNot ts (List.mem_cons_of_mem _ hmem)
          have hneq : e' ≠ e := by
            intro hEq
            exact hNot ts' (by simpa [hEq])
          have hfind :
              (updateD env e' ts').find? e = env.find? e := by
            exact findD_update_neq env e' e ts' hneq
          simpa [List.foldl, insertPairD, hfind] using
            (ih (env := updateD env e' ts') (hNot := hNot'))

theorem lookupD_foldl_insert_preserve'
    (L : List (Edge × List ValType)) (env : DEnv) (e : Edge) (ts : List ValType)
    (hlookup : lookupD env e = ts)
    (hSame : ∀ ts', (e, ts') ∈ L → ts' = ts) :
    lookupD (L.foldl insertPairD env) e = ts := by
  induction L generalizing env with
  | nil =>
      simpa using hlookup
  | cons p L ih =>
      cases p with
      | mk e' ts' =>
          have hSame' : ∀ ts'', (e, ts'') ∈ L → ts'' = ts := by
            intro ts'' hmem
            exact hSame ts'' (List.mem_cons_of_mem _ hmem)
          by_cases hEq : e' = e
          · cases hEq
            have hts' : ts' = ts := hSame ts' (by simp)
            cases hts'
            have hlookup' : lookupD (updateD env e ts) e = ts := by
              simpa using (lookupD_update_eq (env:=env) (e:=e) (ts:=ts))
            simpa [List.foldl, insertPairD] using
              (ih (env := updateD env e ts) (hlookup := hlookup') (hSame := hSame'))
          · have hlookup' : lookupD (updateD env e' ts') e = ts := by
              have h := lookupD_update_neq (env:=env) (e:=e') (e':=e) (ts:=ts') hEq
              simpa [hlookup] using h
            simpa [List.foldl, insertPairD] using
              (ih (env := updateD env e' ts') (hlookup := hlookup') (hSame := hSame'))

theorem lookupD_foldl_insert_of_mem
    (L : List (Edge × List ValType)) (env : DEnv) (e : Edge) (ts : List ValType)
    (hmem : (e, ts) ∈ L)
    (hSame : ∀ ts', (e, ts') ∈ L → ts' = ts) :
    lookupD (L.foldl insertPairD env) e = ts := by
  induction L generalizing env with
  | nil =>
      cases hmem
  | cons p L ih =>
      cases p with
      | mk e' ts' =>
          have hSame' : ∀ ts'', (e, ts'') ∈ L → ts'' = ts := by
            intro ts'' hmem'
            exact hSame ts'' (List.mem_cons_of_mem _ hmem')
          cases hmem with
          | head _ =>
              have hlookup' : lookupD (updateD env e ts) e = ts := by
                simpa using (lookupD_update_eq (env:=env) (e:=e) (ts:=ts))
              simpa [List.foldl, insertPairD] using
                (lookupD_foldl_insert_preserve' (L:=L) (env:=updateD env e ts)
                  (e:=e) (ts:=ts) hlookup' hSame')
          | tail _ htail =>
              simpa [List.foldl, insertPairD] using
                (ih (env := updateD env e' ts') (hmem := htail) (hSame := hSame'))

theorem lookupD_foldl_insert_notin
    (L : List (Edge × List ValType)) (env : DEnv) (e : Edge) (ts : List ValType)
    (hlookup : lookupD env e = ts)
    (hNot : ∀ ts, (e, ts) ∈ L → False) :
    lookupD (L.foldl insertPairD env) e = ts := by
  apply lookupD_foldl_insert_preserve' (L:=L) (env:=env) (e:=e) (ts:=ts) hlookup
  intro ts' hmem
  exact (hNot ts' hmem).elim

end
