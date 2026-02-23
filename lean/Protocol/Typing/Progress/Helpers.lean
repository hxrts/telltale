import Protocol.Typing.Preservation

/-! # MPST Process Typing: Progress

This module proves progress for the process typing judgment.
-/

/-
The Problem. We need progress: well-typed processes either terminate (skip)
or can take a step. Combined with preservation, this yields type safety.

Solution Structure. We prove progress by:
1. Case analysis on the process (skip is done, others can step)
2. Using buffer contents to show sends/recvs can proceed
3. Handling parallel composition via context splitting
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

section

-- Progress Helpers

theorem find_label_eq {α : Type} {lbl lbl' : Label} {xs : List (Label × α)} {v : α}
    (h : xs.find? (fun b => b.1 == lbl) = some (lbl', v)) : lbl' = lbl := by
  have hPred : (lbl' == lbl) := (List.find?_eq_some_iff_append (xs := xs)
    (p := fun b => b.1 == lbl) (b := (lbl', v))).1 h |>.1
  have hPred' : (lbl' == lbl) = true := by
    simpa using hPred
  exact (beq_iff_eq).1 hPred'

-- Blocked-Process Predicate

def BlockedProc (store : VarStore) (bufs : Buffers) : Process → Prop
  | .recv k _ =>
      ∃ e source,
        lookupStr store k = some (.chan e) ∧
        lookupBuf bufs { sid := e.sid, sender := source, receiver := e.role } = []
  | .branch k _ =>
      ∃ e source,
        lookupStr store k = some (.chan e) ∧
        lookupBuf bufs { sid := e.sid, sender := source, receiver := e.role } = []
  | .seq P _ =>
      BlockedProc store bufs P
  | .par _ _ P Q =>
      (P = .skip ∨ BlockedProc store bufs P) ∧ (Q = .skip ∨ BlockedProc store bufs Q)
  | _ => False

-- SEnv Domain-Subset Helpers

lemma disjoint_s_right_empty (S : SEnv) : DisjointS S (∅ : SEnv) := by
  intro x T₁ T₂ hL1 hL2
  have : lookupSEnv (∅ : SEnv) x = none := lookup_s_env_empty x
  cases hL2

lemma s_env_dom_subset_erase
    {S : SEnv} {x : Var} :
    SEnvDomSubset (eraseSEnv S x) S := by
  intro y Ty hErase
  by_cases hxy : y = x
  · subst hxy
    have hNone : lookupSEnv (eraseSEnv S y) y = none := lookup_s_env_erase_eq (S:=S) (x:=y)
    have : (some Ty : Option ValType) = none := by simpa [hNone] using hErase
    cases this
  · have hEq : lookupSEnv (eraseSEnv S x) y = lookupSEnv S y :=
      lookup_s_env_erase_ne (S:=S) (x:=x) (y:=y) hxy
    exact ⟨Ty, by simpa [hEq] using hErase⟩

lemma s_env_dom_subset_update_left_right
    {Sown : OwnedEnv} {x : Var} {T : ValType} :
    SEnvDomSubset (OwnedEnv.updateLeft Sown x T).right Sown.right := by
  simpa [OwnedEnv.updateLeft] using (s_env_dom_subset_erase (S:=Sown.right) (x:=x))

-- Pre-Out Right-Environment Domain Inclusion

theorem has_type_proc_pre_out_right_domsubset
    {Ssh Sown G P Sfin Gfin W Δ} :
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
/- ## Structured Block 1 -/
    SEnvDomSubset Sfin.right Sown.right := by
  intro h
  induction h with
  | skip =>
      exact s_env_dom_subset_refl
  | send =>
      exact s_env_dom_subset_refl
  | recv_new _ _ _ _ =>
      simpa using (s_env_dom_subset_update_left_right (Sown:=_) (x:=_) (T:=_))
  | recv_old _ _ _ _ =>
      simpa using (s_env_dom_subset_update_left_right (Sown:=_) (x:=_) (T:=_))
  | select =>
      exact s_env_dom_subset_refl
  | branch _ _ _ _ _ _ _ _ hRight =>
      intro x T hLookup
      exact ⟨T, by simpa [hRight] using hLookup⟩
  | seq hP hQ ihP ihQ =>
      exact s_env_dom_subset_trans ihQ ihP
  | par split hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
      hDisjW hDisjΔ hP hQ ihP ihQ =>
      intro x T hLookup
      exact ⟨T, by simpa [hSfin] using hLookup⟩
  | assign_new _ _ _ =>
      simpa using (s_env_dom_subset_update_left_right (Sown:=_) (x:=_) (T:=_))
  | assign_old _ _ _ =>
      simpa using (s_env_dom_subset_update_left_right (Sown:=_) (x:=_) (T:=_))

-- Typed-Step Preservation of Right-Owned Environment

lemma typed_step_preserves_right
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' Sfin Gfin W Δ} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    SEnvDomSubset Sown.right Sfin.right →
    Sown'.right = Sown.right := by
  intro hStep hPre hSubRight
  induction hStep generalizing Sfin Gfin W Δ with
  | recv =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
        hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut
      cases hPre with
      | recv_new hk' hG' hNoSh hNoOwnL =>
          have hNoOwnR : lookupSEnv Sown.right x = none := by
            by_cases hNone : lookupSEnv Sown.right x = none
            · exact hNone
            · cases hOwn : lookupSEnv Sown.right x with
              | none =>
                  exact (hNone hOwn).elim
              | some Tx =>
                  obtain ⟨Tfin, hInFin⟩ := hSubRight hOwn
                  have hNoneErase : lookupSEnv (eraseSEnv Sown.right x) x = none :=
                    lookup_s_env_erase_eq (S:=Sown.right) (x:=x)
                  have : (some Tfin : Option ValType) = none := by
/- ## Structured Block 2 -/
                    simpa [OwnedEnv.updateLeft, hNoneErase] using hInFin
                  cases this
          have hErase : eraseSEnv Sown.right x = Sown.right :=
            erase_s_env_of_lookup_none hNoOwnR
          have hRightEq : (OwnedEnv.updateLeft Sown x T).right = Sown.right := by
            simpa [OwnedEnv.updateLeft, hErase]
          simpa [hSout] using hRightEq
      | recv_old hk' hG' hNoSh hOwn =>
          have hNoOwnR : lookupSEnv Sown.right x = none := by
            by_cases hNone : lookupSEnv Sown.right x = none
            · exact hNone
            · cases hOwnR : lookupSEnv Sown.right x with
              | none =>
                  exact (hNone hOwnR).elim
              | some Tx =>
                  obtain ⟨Tfin, hInFin⟩ := hSubRight hOwnR
                  have hNoneErase : lookupSEnv (eraseSEnv Sown.right x) x = none :=
                    lookup_s_env_erase_eq (S:=Sown.right) (x:=x)
                  have : (some Tfin : Option ValType) = none := by
                    simpa [OwnedEnv.updateLeft, hNoneErase] using hInFin
                  cases this
          have hErase : eraseSEnv Sown.right x = Sown.right :=
            erase_s_env_of_lookup_none hNoOwnR
          have hRightEq : (OwnedEnv.updateLeft Sown x T).right = Sown.right := by
            simpa [OwnedEnv.updateLeft, hErase]
          simpa [hSout] using hRightEq
  -- Typed-Step Preservation: Assign Cases
  | assign =>
      rename_i G D Ssh Sown store bufs x v T S' store' hv hSout hStoreOut
      cases hPre with
      | assign_new hNoSh hNoOwnL hv' =>
          have hNoOwnR : lookupSEnv Sown.right x = none := by
            by_cases hNone : lookupSEnv Sown.right x = none
            · exact hNone
            · cases hOwnR : lookupSEnv Sown.right x with
              | none =>
                  exact (hNone hOwnR).elim
              | some Tx =>
                  obtain ⟨Tfin, hInFin⟩ := hSubRight hOwnR
                  have hNoneErase : lookupSEnv (eraseSEnv Sown.right x) x = none :=
                    lookup_s_env_erase_eq (S:=Sown.right) (x:=x)
                  have : (some Tfin : Option ValType) = none := by
                    simpa [OwnedEnv.updateLeft, hNoneErase] using hInFin
                  cases this
          have hErase : eraseSEnv Sown.right x = Sown.right :=
            erase_s_env_of_lookup_none hNoOwnR
          have hRightEq : (OwnedEnv.updateLeft Sown x T).right = Sown.right := by
            simpa [OwnedEnv.updateLeft, hErase]
          simpa [hSout] using hRightEq
      | assign_old hNoSh hOwn hv' =>
          have hNoOwnR : lookupSEnv Sown.right x = none := by
/- ## Structured Block 3 -/
            by_cases hNone : lookupSEnv Sown.right x = none
            · exact hNone
            · cases hOwnR : lookupSEnv Sown.right x with
              | none =>
                  exact (hNone hOwnR).elim
              | some Tx =>
                  obtain ⟨Tfin, hInFin⟩ := hSubRight hOwnR
                  have hNoneErase : lookupSEnv (eraseSEnv Sown.right x) x = none :=
                    lookup_s_env_erase_eq (S:=Sown.right) (x:=x)
                  have : (some Tfin : Option ValType) = none := by
                    simpa [OwnedEnv.updateLeft, hNoneErase] using hInFin
                  cases this
          have hErase : eraseSEnv Sown.right x = Sown.right :=
            erase_s_env_of_lookup_none hNoOwnR
          have hRightEq : (OwnedEnv.updateLeft Sown x T).right = Sown.right := by
            simpa [OwnedEnv.updateLeft, hErase]
          simpa [hSout] using hRightEq
  -- Typed-Step Preservation: Structural Cases
  | seq_step _ ih =>
      cases hPre with
      | seq hP hQ =>
          have hSubQ := has_type_proc_pre_out_right_domsubset hQ
          have hSubP := s_env_dom_subset_trans hSubRight hSubQ
          exact ih hP hSubP
  | _ =>
      rfl

-- Endpoint Equality from Full Store Lookup

lemma channel_endpoint_eq_of_store
    {G : GEnv} {Ssh : SEnv} {Sown : OwnedEnv} {store : VarStore}
    {k : Var} {e e' : Endpoint} :
    (hStore : StoreTypedStrong G (SEnvAll Ssh Sown) store) →
    lookupSEnv (SEnvAll Ssh Sown) k = some (ValType.chan e.sid e.role) →
    lookupStr store k = some (Value.chan e') →
    e' = e := by
  intro hStore hk hkStr
  obtain ⟨vk, hkStr', hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
  have hkChan : vk = Value.chan e := has_type_val_chan_inv hkTyped
  have hkStr'' : lookupStr store k = some (Value.chan e) := by
    simpa [hkChan] using hkStr'
  have hEqOpt : some (Value.chan e') = some (Value.chan e) := by
    simpa [hkStr] using hkStr''
  have hEq : (Value.chan e') = (Value.chan e) := Option.some.inj hEqOpt
  cases hEq
  rfl

-- Empty-Environment and Disjointness Utilities

lemma disjoint_g_left_empty (G : GEnv) : DisjointG [] G := by
  simp [DisjointG, GEnvDisjoint, sessions_of_empty]

lemma d_env_find_empty (e : Edge) : (∅ : DEnv).find? e = none := by
  rfl

lemma disjoint_d_right_empty (D : DEnv) : DisjointD D (∅ : DEnv) := by
  simp [DisjointD, sessions_of_d_empty]

lemma disjoint_d_left_empty (D : DEnv) : DisjointD (∅ : DEnv) D := by
  simp [DisjointD, sessions_of_d_empty]

/- ## Structured Block 4 -/
theorem d_env_append_empty_right (D : DEnv) : D ++ (∅ : DEnv) = D :=
  d_env_union_empty_right D

theorem d_env_append_empty_left (D : DEnv) : (∅ : DEnv) ++ D = D :=
  d_env_union_empty_left D

lemma s_env_append_empty_left (S : SEnv) : (∅ : SEnv) ++ S = S := by
  simpa using (List.nil_append S)

-- Store Typing Rearrangements (Local Helpers)


end
