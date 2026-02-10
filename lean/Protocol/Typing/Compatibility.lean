import Protocol.Typing.Judgments

/-!
# MPST Process Typing: Compatibility

This module defines compatibility predicates for process typing.
-/

/-
The Problem. Process typing requires compatibility checks between local types,
contexts, and actions. We need coinductive compatibility for recursive types
and split-context reasoning for parallel composition.

Solution Structure. We define:
1. Coinductive compatibility for local type pairs
2. Context splitting for parallel composition
3. Compatibility lemmas used by the typing judgment
-/

/-!
## Key Judgments

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

/-! ### Global Compatibility (Coinductive) -/

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

/-! ### LocalTypeR.WellFormed Predicate -/

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

private def insertPairD (acc : DEnv) (p : Edge × List ValType) : DEnv :=
  updateD acc p.1 p.2

private def insertPairS (acc : SEnv) (p : Var × ValType) : SEnv :=
  updateSEnv acc p.1 p.2

private theorem findD_update_eq (env : DEnv) (e : Edge) (ts : List ValType) :
    (updateD env e ts).find? e = some ts := by
  have hEq : compare e e = .eq := by
    simp
  simpa [updateD] using
    (RBMap.find?_insert_of_eq (t := env.map) (k := e) (v := ts) (k' := e) hEq)

private theorem findD_update_neq (env : DEnv) (e e' : Edge) (ts : List ValType) (hne : e ≠ e') :
    (updateD env e ts).find? e' = env.find? e' := by
  have hne' : compare e' e ≠ .eq := by
    intro hEq
    exact hne (by symm; exact (Edge.compare_eq_iff_eq e' e).1 hEq)
  have h' : (env.map.insert e ts).find? e' = env.map.find? e' := by
    simpa using (RBMap.find?_insert_of_ne (t := env.map) (k := e) (v := ts) (k' := e') hne')
  have h'' : (updateD env e ts).find? e' = env.map.find? e' := by
    simpa [updateD] using h'
  simpa [DEnv.find?] using h''

private theorem findD_foldl_insert_preserve
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

private theorem findD_foldl_insert_of_mem
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

private theorem findD_foldl_insert_notin
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

private theorem lookupD_foldl_insert_preserve'
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

private theorem lookupD_foldl_insert_of_mem
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

private theorem lookupD_foldl_insert_notin
    (L : List (Edge × List ValType)) (env : DEnv) (e : Edge) (ts : List ValType)
    (hlookup : lookupD env e = ts)
    (hNot : ∀ ts, (e, ts) ∈ L → False) :
    lookupD (L.foldl insertPairD env) e = ts := by
  apply lookupD_foldl_insert_preserve' (L:=L) (env:=env) (e:=e) (ts:=ts) hlookup
  intro ts' hmem
  exact (hNot ts' hmem).elim

private theorem lookupSEnv_foldl_insert_preserve
    (L : List (Var × ValType)) (env : SEnv) (x : Var) (T : ValType)
    (hlookup : lookupSEnv env x = some T)
    (hSame : ∀ T', (x, T') ∈ L → T' = T) :
    lookupSEnv (L.foldl insertPairS env) x = some T := by
  induction L generalizing env with
  | nil =>
      simpa using hlookup
  | cons p L ih =>
      cases p with
      | mk x' T' =>
          have hSame' : ∀ T'', (x, T'') ∈ L → T'' = T := by
            intro T'' hmem
            exact hSame T'' (List.mem_cons_of_mem _ hmem)
          by_cases hEq : x' = x
          · cases hEq
            have hT' : T' = T := hSame T' (by simp)
            cases hT'
            have hlookup' : lookupSEnv (updateSEnv env x T) x = some T := by
              simpa using (lookupSEnv_update_eq (env:=env) (x:=x) (T:=T))
            simpa [List.foldl, insertPairS] using
              (ih (env := updateSEnv env x T) (hlookup := hlookup') (hSame := hSame'))
          · have hlookup' : lookupSEnv (updateSEnv env x' T') x = some T := by
              have h := lookupSEnv_update_neq (env:=env) (x:=x') (y:=x) (T:=T') hEq
              simpa [hlookup] using h
            simpa [List.foldl, insertPairS] using
              (ih (env := updateSEnv env x' T') (hlookup := hlookup') (hSame := hSame'))

private theorem lookupSEnv_foldl_insert_of_mem
    (L : List (Var × ValType)) (env : SEnv) (x : Var) (T : ValType)
    (hmem : (x, T) ∈ L)
    (hSame : ∀ T', (x, T') ∈ L → T' = T) :
    lookupSEnv (L.foldl insertPairS env) x = some T := by
  induction L generalizing env with
  | nil =>
      cases hmem
  | cons p L ih =>
      cases p with
      | mk x' T' =>
          have hSame' : ∀ T'', (x, T'') ∈ L → T'' = T := by
            intro T'' hmem'
            exact hSame T'' (List.mem_cons_of_mem _ hmem')
          cases hmem with
          | head _ =>
              have hlookup' : lookupSEnv (updateSEnv env x T) x = some T := by
                simpa using (lookupSEnv_update_eq (env:=env) (x:=x) (T:=T))
              simpa [List.foldl, insertPairS] using
                (lookupSEnv_foldl_insert_preserve (L:=L) (env:=updateSEnv env x T)
                  (x:=x) (T:=T) hlookup' hSame')
          | tail _ htail =>
              simpa [List.foldl, insertPairS] using
                (ih (env := updateSEnv env x' T') (hmem := htail) (hSame := hSame'))

private theorem lookupSEnv_foldl_insert_notin
    (L : List (Var × ValType)) (env : SEnv) (x : Var) (v : Option ValType)
    (hlookup : lookupSEnv env x = v)
    (hNot : ∀ T, (x, T) ∈ L → False) :
    lookupSEnv (L.foldl insertPairS env) x = v := by
  induction L generalizing env with
  | nil =>
      simpa using hlookup
  | cons p L ih =>
      cases p with
      | mk x' T' =>
          have hNot' : ∀ T, (x, T) ∈ L → False := by
            intro T hmem
            exact hNot T (List.mem_cons_of_mem _ hmem)
          have hneq : x' ≠ x := by
            intro hEq
            exact hNot T' (by simpa [hEq])
          have hlookup' : lookupSEnv (updateSEnv env x' T') x = v := by
            have h := lookupSEnv_update_neq (env:=env) (x:=x') (y:=x) (T:=T') hneq
            simpa [hlookup] using h
          simpa [List.foldl, insertPairS] using
            (ih (env := updateSEnv env x' T') (hlookup := hlookup') (hNot := hNot'))

private def insertIfMissing (acc : RBMap Edge Trace compare) (k : Edge) (v : Trace) :
    RBMap Edge Trace compare :=
  match acc.find? k with
  | some _ => acc
  | none => acc.insert k v

private theorem rbmap_foldl_preserve
    (L : List (Edge × Trace)) (acc : RBMap Edge Trace compare) (e : Edge) (ts : Trace)
    (hfind : acc.find? e = some ts) :
    (L.foldl (fun acc p => insertIfMissing acc p.1 p.2) acc).find? e = some ts := by
  induction L generalizing acc with
  | nil =>
      simpa [hfind]
  | cons hd tl ih =>
      cases hd with
      | mk k v =>
          cases hacc : acc.find? k with
          | some _ =>
              simpa [List.foldl, insertIfMissing, hacc] using (ih (acc := acc) hfind)
          | none =>
              have hkne : k ≠ e := by
                intro hEq
                subst hEq
                simpa [hfind] using hacc
              have hne : compare e k ≠ .eq := by
                intro hEq
                exact hkne (by symm; exact (Edge.compare_eq_iff_eq e k).1 hEq)
              have hacc' : (acc.insert k v).find? e = acc.find? e := by
                simpa using (RBMap.find?_insert_of_ne (t := acc) (k := k) (v := v) (k' := e) hne)
              have hfind' : (acc.insert k v).find? e = some ts := by
                simpa [hfind] using hacc'
              simpa [List.foldl, insertIfMissing, hacc] using
                (ih (acc := acc.insert k v) hfind')

private theorem rbmap_foldl_none
    (L : List (Edge × Trace)) (acc : RBMap Edge Trace compare) (e : Edge)
    (hfind : acc.find? e = none) :
    (L.foldl (fun acc p => insertIfMissing acc p.1 p.2) acc).find? e = L.lookup e := by
  induction L generalizing acc with
  | nil =>
      simpa [List.lookup, hfind]
  | cons hd tl ih =>
      cases hd with
      | mk k v =>
          by_cases hEq : e = k
          · subst hEq
            have hEq' : compare e e = .eq := by
              simp
            have hfind' : (acc.insert e v).find? e = some v := by
              simpa using (RBMap.find?_insert_of_eq (t := acc) (k := e) (v := v) (k' := e) hEq')
            have hpreserve :
                (tl.foldl (fun acc p => insertIfMissing acc p.1 p.2) (acc.insert e v)).find? e =
                  some v :=
              rbmap_foldl_preserve (L := tl) (acc := acc.insert e v) (e := e) (ts := v) hfind'
            simpa [List.lookup, beq_self_eq_true, insertIfMissing, hfind] using hpreserve
          · have hbeq : (e == k) = false := beq_eq_false_iff_ne.mpr hEq
            cases hacc : acc.find? k with
            | some _ =>
                have ih' := ih (acc := acc) hfind
                simpa [List.foldl, insertIfMissing, hacc, List.lookup, hbeq] using ih'
            | none =>
                have hne : compare e k ≠ .eq := by
                  intro hEq'
                  exact hEq ((Edge.compare_eq_iff_eq e k).1 hEq')
                have hacc' : (acc.insert k v).find? e = acc.find? e := by
                  simpa using (RBMap.find?_insert_of_ne (t := acc) (k := k) (v := v) (k' := e) hne)
                have hfind' : (acc.insert k v).find? e = none := by
                  simpa [hfind] using hacc'
                have ih' := ih (acc := acc.insert k v) hfind'
                simpa [List.foldl, insertIfMissing, hacc, List.lookup, hbeq] using ih'

theorem findD_append_left {D₁ D₂ : DEnv} {e : Edge} {ts : List ValType} :
    D₁.find? e = some ts →
    (D₁ ++ D₂).find? e = some ts := by
  intro hfind
  have hfind_map : D₁.map.find? e = some ts := by
    simpa [DEnv.find?] using hfind
  have hfold_list :
      (D₂.map.toList.foldl (fun acc p => insertIfMissing acc p.1 p.2) D₁.map).find? e = some ts :=
    rbmap_foldl_preserve (L := D₂.map.toList) (acc := D₁.map) (e := e) (ts := ts) hfind_map
  have hfold :
      (RBMap.foldl (fun acc k v => insertIfMissing acc k v) D₁.map D₂.map).find? e = some ts := by
    simpa [RBMap.foldl_eq_foldl_toList] using hfold_list
  change (DEnvUnion D₁ D₂).find? e = some ts
  simpa [DEnvUnion, insertIfMissing] using hfold

theorem findD_append_right {D₁ D₂ : DEnv} {e : Edge} :
    D₁.find? e = none →
    (D₁ ++ D₂).find? e = D₂.find? e := by
  intro hfind
  have hfind_map : D₁.map.find? e = none := by
    simpa [DEnv.find?] using hfind
  have hfold_list :
      (D₂.map.toList.foldl (fun acc p => insertIfMissing acc p.1 p.2) D₁.map).find? e =
        D₂.map.toList.lookup e :=
    rbmap_foldl_none (L := D₂.map.toList) (acc := D₁.map) (e := e) hfind_map
  have hfold :
      (RBMap.foldl (fun acc k v => insertIfMissing acc k v) D₁.map D₂.map).find? e =
        D₂.map.toList.lookup e := by
    simpa [RBMap.foldl_eq_foldl_toList] using hfold_list
  have hlookup : D₂.map.toList.lookup e = D₂.map.find? e :=
    lookup_toList_eq_find? (m := D₂.map) (e := e)
  have hfold' :
      (RBMap.foldl (fun acc k v => insertIfMissing acc k v) D₁.map D₂.map).find? e =
        D₂.map.find? e := by
    simpa [hlookup] using hfold
  change (DEnvUnion D₁ D₂).find? e = D₂.map.find? e
  simpa [DEnvUnion, insertIfMissing] using hfold'

theorem SessionsOfD_append_left {D₁ D₂ : DEnv} :
    SessionsOfD D₁ ⊆ SessionsOfD (D₁ ++ D₂) := by
  intro s hs
  rcases hs with ⟨e, ts, hFind, hSid⟩
  exact ⟨e, ts, findD_append_left (D₁:=D₁) (D₂:=D₂) (e:=e) (ts:=ts) hFind, hSid⟩

theorem SessionsOfD_append_right {D₁ D₂ : DEnv} :
    SessionsOfD D₂ ⊆ SessionsOfD (D₁ ++ D₂) := by
  intro s hs
  rcases hs with ⟨e, ts, hFind, hSid⟩
  cases hLeft : D₁.find? e with
  | some ts₁ =>
      exact ⟨e, ts₁, findD_append_left (D₁:=D₁) (D₂:=D₂) (e:=e) (ts:=ts₁) hLeft, hSid⟩
  | none =>
      have hFind' := findD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) hLeft
      exact ⟨e, ts, by simpa [hFind'] using hFind, hSid⟩

theorem SessionsOfD_append_subset {D₁ D₂ : DEnv} :
    SessionsOfD (D₁ ++ D₂) ⊆ SessionsOfD D₁ ∪ SessionsOfD D₂ := by
  intro s hs
  rcases hs with ⟨e, ts, hFind, hSid⟩
  cases hLeft : D₁.find? e with
  | some ts₁ =>
      have hIn : s ∈ SessionsOfD D₁ := ⟨e, ts₁, hLeft, hSid⟩
      exact Or.inl hIn
  | none =>
      have hRight := findD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) hLeft
      have hFind' : D₂.find? e = some ts := by
        simpa [hRight] using hFind
      have hIn : s ∈ SessionsOfD D₂ := ⟨e, ts, hFind', hSid⟩
      exact Or.inr hIn

theorem SessionsOfD_updateD_subset {D : DEnv} {e : Edge} {ts : List ValType} :
    SessionsOfD (updateD D e ts) ⊆ SessionsOfD D ∪ {e.sid} := by
  intro s hs
  rcases hs with ⟨e', ts', hFind, hSid⟩
  by_cases hEq : e' = e
  · subst hEq
    right
    simpa [hSid]
  · left
    have hFind' : D.find? e' = some ts' := by
      have h' : (updateD D e ts).find? e' = D.find? e' :=
        findD_update_neq D e e' ts (Ne.symm hEq)
      simpa [h'] using hFind
    exact ⟨e', ts', hFind', hSid⟩

theorem lookupD_entry_of_nonempty {D : DEnv} {e : Edge} :
    lookupD D e ≠ [] →
    ∃ ts, D.find? e = some ts := by
  intro hne
  cases hFind : D.find? e with
  | none =>
      have hlookup : lookupD D e = [] := by
        simp [lookupD, hFind]
      exact (hne hlookup).elim
  | some ts =>
      exact ⟨ts, by simpa [hFind]⟩

/-- Lookup in appended GEnv prefers the left. -/
theorem lookupG_append_left {G₁ G₂ : GEnv} {e : Endpoint} {L : LocalType} :
    lookupG G₁ e = some L →
    lookupG (G₁ ++ G₂) e = some L := by
  intro hLookup
  induction G₁ with
  | nil =>
      simp [lookupG] at hLookup
  | cons hd tl ih =>
      cases hEq : (e == hd.1) with
      | true =>
          have hL : hd.2 = L := by
            simpa [lookupG, List.lookup, hEq] using hLookup
          simp [lookupG, List.lookup, hEq, hL]
      | false =>
          have hLookup' : lookupG tl e = some L := by
            simpa [lookupG, List.lookup, hEq] using hLookup
          have ih' := ih hLookup'
          simpa [lookupG, List.lookup, hEq] using ih'

/-- Lookup in appended GEnv falls back to the right when left is missing. -/
theorem lookupG_append_right {G₁ G₂ : GEnv} {e : Endpoint} :
    lookupG G₁ e = none →
    lookupG (G₁ ++ G₂) e = lookupG G₂ e := by
  intro hLookup
  induction G₁ with
  | nil =>
      simp [lookupG] at hLookup ⊢
  | cons hd tl ih =>
      cases hEq : (e == hd.1) with
      | true =>
          have : False := by
            simpa [lookupG, List.lookup, hEq] using hLookup
          exact this.elim
      | false =>
          have hLookup' : lookupG tl e = none := by
            simpa [lookupG, List.lookup, hEq] using hLookup
          have ih' := ih hLookup'
          simpa [lookupG, List.lookup, hEq] using ih'

/-- Invert lookup in an appended GEnv. -/
theorem lookupG_append_inv {G₁ G₂ : GEnv} {e : Endpoint} {L : LocalType} :
    lookupG (G₁ ++ G₂) e = some L →
    lookupG G₁ e = some L ∨ (lookupG G₁ e = none ∧ lookupG G₂ e = some L) := by
  intro hLookup
  cases hLeft : lookupG G₁ e with
  | some L₁ =>
      left
      have hLeft' := lookupG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L₁) hLeft
      have hEq : L₁ = L := by
        have : some L₁ = some L := by simpa [hLeft'] using hLookup
        cases this
        rfl
      simpa [hEq] using hLeft
  | none =>
      right
      have hRight := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hLeft
      have hLookup' : lookupG G₂ e = some L := by
        simpa [hRight] using hLookup
      exact ⟨by simpa [hLeft], hLookup'⟩

theorem SessionsOf_append_right_subset {G₁ G₂ : GEnv} :
    SessionsOf G₂ ⊆ SessionsOf (G₁ ++ G₂) := by
  intro s hs
  rcases hs with ⟨e, L, hLookup, hSid⟩
  cases hLeft : lookupG G₁ e with
  | some L₁ =>
      exact ⟨e, L₁, lookupG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L₁) hLeft, hSid⟩
  | none =>
      have hRight := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hLeft
      exact ⟨e, L, by simpa [hRight] using hLookup, hSid⟩

/-- Sessions in an appended GEnv are contained in the union of sessions. -/
theorem SessionsOf_append_subset {G₁ G₂ : GEnv} :
    SessionsOf (G₁ ++ G₂) ⊆ SessionsOf G₁ ∪ SessionsOf G₂ := by
  intro s hs
  rcases hs with ⟨e, L, hLookup, hSid⟩
  cases hLeft : lookupG G₁ e with
  | some L₁ =>
      exact Or.inl ⟨e, L₁, hLeft, hSid⟩
  | none =>
      have hRight := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hLeft
      have hLookup' : lookupG G₂ e = some L := by
        simpa [hRight] using hLookup
      exact Or.inr ⟨e, L, hLookup', hSid⟩

/-- Left sessions embed into appended GEnv sessions. -/
theorem SessionsOf_append_left {G₁ G₂ : GEnv} :
    SessionsOf G₁ ⊆ SessionsOf (G₁ ++ G₂) := by
  intro s hs
  rcases hs with ⟨e, L, hLookup, hSid⟩
  exact ⟨e, L, lookupG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hLookup, hSid⟩

/-- Right sessions embed into appended GEnv sessions. -/
theorem SessionsOf_append_right {G₁ G₂ : GEnv} :
    SessionsOf G₂ ⊆ SessionsOf (G₁ ++ G₂) := by
  intro s hs
  exact SessionsOf_append_right_subset (G₁:=G₁) (G₂:=G₂) hs

/-- Disjointness is preserved when the left sessions shrink. -/
theorem DisjointG_of_subset_left {G₁ G₁' G₂ : GEnv} :
    SessionsOf G₁' ⊆ SessionsOf G₁ →
    DisjointG G₁ G₂ →
    DisjointG G₁' G₂ := by
  intro hSub hDisj
  have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = ∅ := by
    simpa [DisjointG, GEnvDisjoint] using hDisj
  apply Set.eq_empty_iff_forall_notMem.2
  intro s hs
  have hs' : s ∈ SessionsOf G₁ ∩ SessionsOf G₂ := by
    exact ⟨hSub hs.1, hs.2⟩
  have : s ∈ (∅ : Set SessionId) := by
    simpa [hEmpty] using hs'
  exact this.elim

/-- DisjointG is symmetric. -/
theorem DisjointG_symm {G₁ G₂ : GEnv} :
    DisjointG G₁ G₂ →
    DisjointG G₂ G₁ := by
  intro hDisj
  simpa [DisjointG, GEnvDisjoint, Set.inter_comm] using hDisj

theorem DisjointG_append_left {G₁ G₁' G₂ : GEnv} :
    DisjointG G₁ G₂ →
    DisjointG G₁' G₂ →
    DisjointG (G₁ ++ G₁') G₂ := by
  intro hDisj hDisj'
  apply Set.eq_empty_iff_forall_notMem.2
  intro s hs
  have hSub := SessionsOf_append_subset (G₁:=G₁) (G₂:=G₁') hs.1
  cases hSub with
  | inl hIn1 =>
      have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = ∅ := by
        simpa [DisjointG, GEnvDisjoint] using hDisj
      have hInter : s ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hIn1, hs.2⟩
      have : s ∈ (∅ : Set SessionId) := by simpa [hEmpty] using hInter
      exact this.elim
  | inr hIn2 =>
      have hEmpty : SessionsOf G₁' ∩ SessionsOf G₂ = ∅ := by
        simpa [DisjointG, GEnvDisjoint] using hDisj'
      have hInter : s ∈ SessionsOf G₁' ∩ SessionsOf G₂ := ⟨hIn2, hs.2⟩
      have : s ∈ (∅ : Set SessionId) := by simpa [hEmpty] using hInter
      exact this.elim

theorem lookupD_append_left {D₁ D₂ : DEnv} {e : Edge} :
    lookupD D₁ e ≠ [] →
    lookupD (D₁ ++ D₂) e = lookupD D₁ e := by
  intro hne
  cases hfind : D₁.find? e with
  | none =>
      have hlookup : lookupD D₁ e = [] := by
        simp [lookupD, hfind]
      exact (hne hlookup).elim
  | some ts =>
      have hleft :=
        findD_append_left (D₁:=D₁) (D₂:=D₂) (e:=e) (ts:=ts) hfind
      have hlookup : lookupD D₁ e = ts := by
        simp [lookupD, hfind]
      have hlookup' : lookupD (D₁ ++ D₂) e = ts := by
        simp [lookupD, hleft]
      simpa [hlookup] using hlookup'

theorem lookupD_append_right {D₁ D₂ : DEnv} {e : Edge} :
    D₁.find? e = none →
    lookupD (D₁ ++ D₂) e = lookupD D₂ e := by
  intro hfind
  have h := findD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) hfind
  simp [lookupD, h]

theorem lookupD_append_left_of_right_none {D₁ D₂ : DEnv} {e : Edge} :
    D₂.find? e = none →
    lookupD (D₁ ++ D₂) e = lookupD D₁ e := by
  intro hRight
  cases hfind : D₁.find? e with
  | none =>
      have h := findD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) hfind
      have hlookup : lookupD D₁ e = [] := by
        simp [lookupD, hfind]
      have hlookup' : lookupD (D₁ ++ D₂) e = [] := by
        simp [lookupD, h, hRight]
      simpa [hlookup] using hlookup'
  | some ts =>
      have hleft :=
        findD_append_left (D₁:=D₁) (D₂:=D₂) (e:=e) (ts:=ts) hfind
      have hlookup : lookupD D₁ e = ts := by
        simp [lookupD, hfind]
      have hlookup' : lookupD (D₁ ++ D₂) e = ts := by
        simp [lookupD, hleft]
      simpa [hlookup] using hlookup'

theorem lookupSEnv_append_left {S₁ S₂ : SEnv} {x : Var} {T : ValType} :
    lookupSEnv S₁ x = some T →
    lookupSEnv (S₁ ++ S₂) x = some T := by
  intro hlookup
  induction S₁ with
  | nil =>
      cases hlookup
  | cons hd tl ih =>
      by_cases hEq : x == hd.1
      · have hT : T = hd.2 := by
          have : some hd.2 = some T := by
            simpa [lookupSEnv, List.lookup, hEq] using hlookup
          exact Option.some.inj this.symm
        subst hT
        simp [lookupSEnv, List.lookup, hEq]
      · have hTail : lookupSEnv tl x = some T := by
          simpa [lookupSEnv, List.lookup, hEq] using hlookup
        have hTail' := ih hTail
        simpa [lookupSEnv, List.lookup, hEq] using hTail'

theorem lookupSEnv_append_right {S₁ S₂ : SEnv} {x : Var} :
    lookupSEnv S₁ x = none →
    lookupSEnv (S₁ ++ S₂) x = lookupSEnv S₂ x := by
  intro hlookup
  induction S₁ with
  | nil =>
      simp [lookupSEnv]
  | cons hd tl ih =>
      by_cases hEq : x == hd.1
      · have : lookupSEnv (hd :: tl) x = some hd.2 := by
          simp [lookupSEnv, List.lookup, hEq]
        have hContra : (none : Option ValType) = some hd.2 := by
          simpa [hlookup] using this
        cases hContra
      · have hTail : lookupSEnv tl x = none := by
          simpa [lookupSEnv, List.lookup, hEq] using hlookup
        have hTail' := ih hTail
        simpa [lookupSEnv, List.lookup, hEq] using hTail'

theorem SEnvDomSubset_append_left {S₁ S₂ : SEnv} :
    SEnvDomSubset S₁ (S₁ ++ S₂) := by
  intro x T hLookup
  exact ⟨T, lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂) hLookup⟩

theorem SEnvDomSubset_append_right {S₁ S₂ : SEnv} :
    SEnvDomSubset S₂ (S₁ ++ S₂) := by
  intro x T hLookup
  cases hLeft : lookupSEnv S₁ x with
  | some T₁ =>
      exact ⟨T₁, lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂) hLeft⟩
  | none =>
      have hEq := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hLeft
      exact ⟨T, by simpa [hEq] using hLookup⟩

theorem lookupSEnv_all_frame_left {Ssh S₁ S₂ : SEnv} {x : Var} {T : ValType} :
    DisjointS S₁ S₂ →
    lookupSEnv (Ssh ++ S₂) x = some T →
    lookupSEnv (Ssh ++ (S₁ ++ S₂)) x = some T := by
  intro hDisj hLookup
  cases hSsh : lookupSEnv Ssh x with
  | some Tsh =>
      have hLeft := lookupSEnv_append_left (S₁:=Ssh) (S₂:=S₂) hSsh
      have hEq : Tsh = T := by
        have : some Tsh = some T := by simpa [hLeft] using hLookup
        cases this
        rfl
      have hLeft' := lookupSEnv_append_left (S₁:=Ssh) (S₂:=S₁ ++ S₂) hSsh
      simpa [hEq] using hLeft'
  | none =>
      have hEq := lookupSEnv_append_right (S₁:=Ssh) (S₂:=S₂) (x:=x) hSsh
      have hS2 : lookupSEnv S₂ x = some T := by
        simpa [hEq] using hLookup
      have hS1 : lookupSEnv S₁ x = none := by
        by_cases hS1 : lookupSEnv S₁ x = none
        · exact hS1
        · cases hS1' : lookupSEnv S₁ x with
          | none => exact (hS1 hS1').elim
          | some T₁ =>
              have hContra := hDisj x T₁ T hS1' hS2
              exact hContra.elim
      have hEq' := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hS1
      have hIn : lookupSEnv (S₁ ++ S₂) x = some T := by
        simpa [hEq'] using hS2
      have hEq'' := lookupSEnv_append_right (S₁:=Ssh) (S₂:=S₁ ++ S₂) (x:=x) hSsh
      simpa [hEq''] using hIn

theorem HasTypeProcPreOut_domsubset {Ssh Sown G P Sown' G' W Δ} :
    HasTypeProcPreOut Ssh Sown G P Sown' G' W Δ →
    SEnvDomSubset Sown.left Sown'.left := by
  intro h
  induction h with
  | skip =>
      exact SEnvDomSubset_refl
  | send =>
      exact SEnvDomSubset_refl
  | recv_new =>
      exact SEnvDomSubset_update_left
  | recv_old =>
      exact SEnvDomSubset_update_left
  | select =>
      exact SEnvDomSubset_refl
  | branch _ _ _ _ _ _ _ hDom _ =>
      exact hDom
  | seq hP hQ ihP ihQ =>
      exact SEnvDomSubset_trans ihP ihQ
  | par split hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
      hDisjW hDisjΔ hP hQ ihP ihQ =>
      -- Show dom subset for the left portion of the owned env.
      rename_i S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂ nS nG
      intro x T hLookup
      have hLookupS : lookupSEnv (split.S1 ++ split.S2) x = some T := by
        simpa [split.hS] using hLookup
      by_cases hLeftNone : lookupSEnv split.S1 x = none
      · have hRight : lookupSEnv split.S2 x = some T := by
          have hEq := lookupSEnv_append_right (S₁:=split.S1) (S₂:=split.S2) (x:=x) hLeftNone
          simpa [hEq] using hLookupS
        obtain ⟨T', hRight'⟩ := ihQ hRight
        have hLeftNone' : lookupSEnv S₁' x = none := by
          by_cases hSome : lookupSEnv S₁' x = none
          · exact hSome
          · cases hSome' : lookupSEnv S₁' x with
            | none => exact (hSome hSome').elim
            | some T₁ =>
                exact (hDisjS' x T₁ T' hSome' hRight').elim
        have hEq := lookupSEnv_append_right (S₁:=S₁') (S₂:=S₂') (x:=x) hLeftNone'
        have hAppend : lookupSEnv (S₁' ++ S₂') x = some T' := by
          simpa [hEq] using hRight'
        exact ⟨T', by simpa [hSfin] using hAppend⟩
      · cases hLeftSome : lookupSEnv split.S1 x with
        | none => exact (hLeftNone hLeftSome).elim
        | some T₁ =>
            have hLeftAppend :
                lookupSEnv (split.S1 ++ split.S2) x = some T₁ :=
              lookupSEnv_append_left (S₁:=split.S1) (S₂:=split.S2) hLeftSome
            have hEqT : T₁ = T := by
              have : some T₁ = some T := by
                simpa [hLeftAppend] using hLookupS
              exact Option.some.inj this
            have hLeftSome' : lookupSEnv split.S1 x = some T := by
              simpa [hEqT] using hLeftSome
            obtain ⟨T', hLeft'⟩ := ihP hLeftSome'
            have hAppend := lookupSEnv_append_left (S₁:=S₁') (S₂:=S₂') hLeft'
            exact ⟨T', by simpa [hSfin] using hAppend⟩
  | assign_new =>
      exact SEnvDomSubset_update_left
  | assign_old =>
      exact SEnvDomSubset_update_left

/-- StoreTyped splits to the left portion of SEnv. -/
theorem StoreTyped_split_left {G : GEnv} {S₁ S₂ : SEnv} {store : VarStore} :
    StoreTyped G (S₁ ++ S₂) store →
    StoreTyped G S₁ store := by
  intro hST x v T hStore hS
  have hS' : lookupSEnv (S₁ ++ S₂) x = some T :=
    lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂) hS
  exact hST x v T hStore hS'

/-- StoreTyped splits to the right portion of SEnv (requires disjointness). -/
theorem StoreTyped_split_right {G : GEnv} {S₁ S₂ : SEnv} {store : VarStore}
    (hDisj : DisjointS S₁ S₂) :
    StoreTyped G (S₁ ++ S₂) store →
    StoreTyped G S₂ store := by
  intro hST x v T hStore hS
  have hNone : lookupSEnv S₁ x = none := by
    by_cases hS1 : lookupSEnv S₁ x = none
    · exact hS1
    · cases hS1' : lookupSEnv S₁ x with
      | none => exact (hS1 hS1').elim
      | some T₁ =>
          exact (hDisj x T₁ T hS1' hS).elim
  have hS' : lookupSEnv (S₁ ++ S₂) x = some T := by
    have h := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hNone
    simpa [hS] using h
  exact hST x v T hStore hS'

/-- Coherence splits to the left portion of G/D. -/
theorem Coherent_split_left {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} :
    Coherent (G₁ ++ G₂) (D₁ ++ D₂) →
    DisjointG G₁ G₂ →
    Coherent G₁ D₁ := by
  intro hCoh hDisj e hActive Lrecv hGrecv
  let senderEp : Endpoint := { sid := e.sid, role := e.sender }
  let recvEp : Endpoint := { sid := e.sid, role := e.receiver }
  have hGrecv' : lookupG (G₁ ++ G₂) recvEp = some Lrecv := lookupG_append_left hGrecv
  have hActive' : ActiveEdge (G₁ ++ G₂) e := by
    simp only [ActiveEdge]
    constructor
    · -- Sender isSome in G₁ ++ G₂
      have hS := hActive.1
      simp only [Option.isSome_iff_exists] at hS ⊢
      obtain ⟨Ls, hLs⟩ := hS
      exact ⟨Ls, lookupG_append_left hLs⟩
    · -- Receiver isSome in G₁ ++ G₂
      rw [hGrecv']; trivial
  have hCoh' := hCoh e hActive' Lrecv hGrecv'
  rcases hCoh' with ⟨Lsender, hGsenderMerged, hConsume⟩
  -- sender must live in G₁ because sessions are disjoint and receiver is in G₁
  have hSid : e.sid ∈ SessionsOf G₁ := ⟨recvEp, Lrecv, hGrecv, rfl⟩
  have hNot : e.sid ∉ SessionsOf G₂ := by
    intro hIn2
    have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hSid, hIn2⟩
    have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = (∅ : Set SessionId) := hDisj
    have : e.sid ∈ (∅ : Set SessionId) := by
      simpa [hEmpty] using hInter
    exact this.elim
  have hG2none_sender : lookupG G₂ senderEp = none := lookupG_none_of_not_session hNot
  have hGsender : lookupG G₁ senderEp = some Lsender := by
    cases lookupG_append_inv (G₁:=G₁) (G₂:=G₂) (e:=senderEp) hGsenderMerged with
    | inl hLeft => exact hLeft
    | inr hRight =>
        have hRight' : lookupG G₂ senderEp = some Lsender := hRight.2
        have : False := by simpa [hG2none_sender] using hRight'
        exact this.elim
  by_cases hTrace : lookupD D₁ e = []
  · refine ⟨Lsender, hGsender, ?_⟩
    simp [hTrace, Consume]
  · have hTrace' : lookupD (D₁ ++ D₂) e = lookupD D₁ e :=
      lookupD_append_left (e := e) hTrace
    refine ⟨Lsender, hGsender, ?_⟩
    simpa [hTrace'] using hConsume
