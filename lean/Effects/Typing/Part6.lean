import Effects.Typing.Part5

/-!
# MPST Process Typing

This module defines the typing rules for MPST processes.

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

noncomputable section

/-! ## Preservation Theorems -/

/-- TypedStep preserves coherence.

    **Proof strategy**: Case analysis on TypedStep constructor:
    - `send`: Use `Coherent_send_preserved` with hRecvReady derived from coherence
    - `recv`: Use `Coherent_recv_preserved`
    - `assign`: G and D unchanged
    - `seq_step`, `seq_skip`: IH or G/D unchanged
    - `par_*`: Disjoint resources remain coherent -/
theorem typed_step_preserves_coherence {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    Coherent G D →
    Coherent G' D'
  | @TypedStep.send G D Ssh Sown store bufs k x e target T L v sendEdge Gout Dout bufsOut hk hx hG hS hv hRecvReady hEdge hGout hDout hBufsOut, hCoh => by
    -- Use Coherent_send_preserved with explicit arguments
    -- After rewriting with the equalities, Gout = updateG G e L and Dout = appendD D sendEdge T
    rw [hGout, hDout, hEdge]
    unfold appendD
    exact @Coherent_send_preserved G D e target T L hCoh hG hRecvReady
  | @TypedStep.recv G D Ssh Sown store bufs k x e source T L v vs recvEdge Gout Dout SownOut storeOut bufsOut hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut, hCoh => by
    -- Use Coherent_recv_preserved with explicit arguments
    rw [hGout, hDout]
    have hTrace' : (lookupD D { sid := e.sid, sender := source, receiver := e.role }).head? = some T := by
      rw [← hEdge]; exact hTrace
    rw [hEdge]
    exact @Coherent_recv_preserved G D e source T L hCoh hG hTrace'
  | @TypedStep.select G D Ssh Sown store bufs k ℓ e target bs L selectEdge Gout Dout bufsOut hk hG hFind hTargetReady hEdge hGout hDout hBufsOut, hCoh => by
    -- Use Coherent_select_preserved with explicit arguments
    rw [hGout, hDout, hEdge]
    unfold appendD
    exact @Coherent_select_preserved G D e target bs ℓ L hCoh hG hFind hTargetReady
  | @TypedStep.branch G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge Gout Dout bufsOut hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut, hCoh => by
    -- Use Coherent_branch_preserved with explicit arguments
    have hTrace' : (lookupD D { sid := e.sid, sender := source, receiver := e.role }).head? = some .string := by
      rw [← hEdge]; exact hTrace
    rw [hGout, hDout, hEdge]
    exact @Coherent_branch_preserved G D e source bs ℓ L hCoh hG hFindT hTrace'
  | .assign _ _ _, hCoh => by
    -- G and D unchanged
    exact hCoh
  | .seq_step hTS, hCoh =>
    -- Inductive hypothesis on sub-transition
    typed_step_preserves_coherence hTS hCoh
  | .seq_skip, hCoh =>
    -- No change
    hCoh
  | @TypedStep.par_left Ssh store bufs store' bufs' P P' Q S G D₁ D₂ G₁' D₁' S₁' split
      hTS hDisjG hDisjD hDisjS hConsL hConsR, hCoh => by
    -- Left transition preserves its part, right unchanged.
    have hCohMerged : Coherent (split.G1 ++ split.G2) (D₁ ++ D₂) := by
      simpa [split.hG] using hCoh
    have hCohL : Coherent split.G1 D₁ := Coherent_split_left hCohMerged hDisjG
    have hCohL' : Coherent G₁' D₁' := typed_step_preserves_coherence hTS hCohL
    have hCohR : Coherent split.G2 D₂ := Coherent_split_right hCohMerged hDisjG hConsL
    have hSubG : SessionsOf G₁' ⊆ SessionsOf split.G1 := SessionsOf_subset_of_TypedStep hTS
    have hDisjG' : DisjointG G₁' split.G2 := DisjointG_of_subset_left hSubG hDisjG
    have hSubD : SessionsOfD D₁' ⊆ SessionsOf split.G1 := by
      intro s hs
      have hs' : s ∈ SessionsOfD D₁ ∪ SessionsOf split.G1 := SessionsOfD_subset_of_TypedStep hTS hs
      cases hs' with
      | inl hD1 => exact hConsL hD1
      | inr hG1 => exact hG1
    intro e Lrecv hGrecv
    set senderEp : Endpoint := { sid := e.sid, role := e.sender }
    set recvEp : Endpoint := { sid := e.sid, role := e.receiver }
    have hInvRecv := lookupG_append_inv (G₁:=G₁') (G₂:=split.G2) (e:=recvEp) hGrecv
    cases hInvRecv with
    | inl hRecvLeft =>
        have hSidLeft : e.sid ∈ SessionsOf G₁' := ⟨recvEp, Lrecv, hRecvLeft, rfl⟩
        have hD2none : D₂.find? e = none := lookupD_none_of_disjointG hDisjG' hConsR hSidLeft
        have hTraceEq : lookupD (D₁' ++ D₂) e = lookupD D₁' e :=
          lookupD_append_left_of_right_none (D₁:=D₁') (D₂:=D₂) (e:=e) hD2none
        have hCohEdge := hCohL' e Lrecv hRecvLeft
        rcases hCohEdge with ⟨Lsender, hGsenderLeft, hConsume⟩
        have hGsenderMerged : lookupG (G₁' ++ split.G2) senderEp = some Lsender :=
          lookupG_append_left (G₁:=G₁') (G₂:=split.G2) hGsenderLeft
        refine ⟨Lsender, hGsenderMerged, ?_⟩
        simpa [hTraceEq] using hConsume
    | inr hRecvRight =>
        have hSidRight : e.sid ∈ SessionsOf split.G2 := ⟨recvEp, Lrecv, hRecvRight.2, rfl⟩
        have hDisjGsym : DisjointG split.G2 G₁' := DisjointG_symm hDisjG'
        have hD1none : D₁'.find? e = none :=
          lookupD_none_of_disjointG (G₁:=split.G2) (G₂:=G₁') (D₂:=D₁') hDisjGsym hSubD hSidRight
        have hTraceEq : lookupD (D₁' ++ D₂) e = lookupD D₂ e :=
          lookupD_append_right (D₁:=D₁') (D₂:=D₂) (e:=e) hD1none
        have hCohEdge := hCohR e Lrecv hRecvRight.2
        rcases hCohEdge with ⟨Lsender, hGsenderRight, hConsume⟩
        have hNot : e.sid ∉ SessionsOf G₁' := by
          intro hIn
          have hInter : e.sid ∈ SessionsOf G₁' ∩ SessionsOf split.G2 := ⟨hIn, hSidRight⟩
          have hEmpty : SessionsOf G₁' ∩ SessionsOf split.G2 = (∅ : Set SessionId) := hDisjG'
          have : e.sid ∈ (∅ : Set SessionId) := by
            simpa [hEmpty] using hInter
          exact this.elim
        have hG1none : lookupG G₁' senderEp = none := lookupG_none_of_not_session hNot
        have hSenderEq := lookupG_append_right (G₁:=G₁') (G₂:=split.G2) (e:=senderEp) hG1none
        have hGsenderMerged : lookupG (G₁' ++ split.G2) senderEp = some Lsender := by
          simpa [hSenderEq] using hGsenderRight
        refine ⟨Lsender, hGsenderMerged, ?_⟩
        simpa [hTraceEq] using hConsume
  | @TypedStep.par_right Ssh store bufs store' bufs' P Q Q' S G D₁ D₂ G₂' D₂' S₂' split
      hTS hDisjG hDisjD hDisjS hConsL hConsR, hCoh => by
    -- Right transition preserves its part, left unchanged.
    have hCohMerged : Coherent (split.G1 ++ split.G2) (D₁ ++ D₂) := by
      simpa [split.hG] using hCoh
    have hCohL : Coherent split.G1 D₁ := Coherent_split_left hCohMerged hDisjG
    have hCohR : Coherent split.G2 D₂ := Coherent_split_right hCohMerged hDisjG hConsL
    have hCohR' : Coherent G₂' D₂' := typed_step_preserves_coherence hTS hCohR
    have hSubG : SessionsOf G₂' ⊆ SessionsOf split.G2 := SessionsOf_subset_of_TypedStep hTS
    have hDisjG' : DisjointG split.G1 G₂' := by
      -- reuse subset on the right
      have hDisjGsym : DisjointG split.G2 split.G1 := DisjointG_symm hDisjG
      have hDisjG'' : DisjointG G₂' split.G1 := DisjointG_of_subset_left hSubG hDisjGsym
      exact DisjointG_symm hDisjG''
    have hSubD : SessionsOfD D₂' ⊆ SessionsOf split.G2 := by
      intro s hs
      have hs' : s ∈ SessionsOfD D₂ ∪ SessionsOf split.G2 := SessionsOfD_subset_of_TypedStep hTS hs
      cases hs' with
      | inl hD2 => exact hConsR hD2
      | inr hG2 => exact hG2
    intro e Lrecv hGrecv
    set senderEp : Endpoint := { sid := e.sid, role := e.sender }
    set recvEp : Endpoint := { sid := e.sid, role := e.receiver }
    have hInvRecv := lookupG_append_inv (G₁:=split.G1) (G₂:=G₂') (e:=recvEp) hGrecv
    cases hInvRecv with
    | inl hRecvLeft =>
        have hSidLeft : e.sid ∈ SessionsOf split.G1 := ⟨recvEp, Lrecv, hRecvLeft, rfl⟩
        have hD2none : D₂'.find? e = none :=
          lookupD_none_of_disjointG (G₁:=split.G1) (G₂:=split.G2) (D₂:=D₂') hDisjG hSubD hSidLeft
        have hTraceEq : lookupD (D₁ ++ D₂') e = lookupD D₁ e :=
          lookupD_append_left_of_right_none (D₁:=D₁) (D₂:=D₂') (e:=e) hD2none
        have hCohEdge := hCohL e Lrecv hRecvLeft
        rcases hCohEdge with ⟨Lsender, hGsenderLeft, hConsume⟩
        have hGsenderMerged : lookupG (split.G1 ++ G₂') senderEp = some Lsender :=
          lookupG_append_left (G₁:=split.G1) (G₂:=G₂') hGsenderLeft
        refine ⟨Lsender, hGsenderMerged, ?_⟩
        simpa [hTraceEq] using hConsume
    | inr hRecvRight =>
        have hSidRight : e.sid ∈ SessionsOf G₂' := ⟨recvEp, Lrecv, hRecvRight.2, rfl⟩
        have hDisjGsym : DisjointG G₂' split.G1 := DisjointG_symm hDisjG'
        have hD1none : D₁.find? e = none :=
          lookupD_none_of_disjointG (G₁:=G₂') (G₂:=split.G1) (D₂:=D₁) hDisjGsym hConsL hSidRight
        have hTraceEq : lookupD (D₁ ++ D₂') e = lookupD D₂' e :=
          lookupD_append_right (D₁:=D₁) (D₂:=D₂') (e:=e) hD1none
        have hCohEdge := hCohR' e Lrecv hRecvRight.2
        rcases hCohEdge with ⟨Lsender, hGsenderRight, hConsume⟩
        have hNot : e.sid ∉ SessionsOf split.G1 := by
          intro hIn
          have hInter : e.sid ∈ SessionsOf split.G1 ∩ SessionsOf G₂' := ⟨hIn, hSidRight⟩
          have hEmpty : SessionsOf split.G1 ∩ SessionsOf G₂' = (∅ : Set SessionId) := hDisjG'
          have : e.sid ∈ (∅ : Set SessionId) := by
            simpa [hEmpty] using hInter
          exact this.elim
        have hG1none : lookupG split.G1 senderEp = none := lookupG_none_of_not_session hNot
        have hSenderEq := lookupG_append_right (G₁:=split.G1) (G₂:=G₂') (e:=senderEp) hG1none
        have hGsenderMerged : lookupG (split.G1 ++ G₂') senderEp = some Lsender := by
          simpa [hSenderEq] using hGsenderRight
        refine ⟨Lsender, hGsenderMerged, ?_⟩
        simpa [hTraceEq] using hConsume
  | .par_skip_left, hCoh =>
    hCoh
  | .par_skip_right, hCoh =>
    hCoh

/-! ## StoreTypedStrong Preservation -/

/-- Updating the left SEnv inside an append when the key is absent on the right. -/
private theorem updateSEnv_append_left_hit {S₁ S₂ : SEnv} {x : Var} {T : ValType}
    (hNone : lookupSEnv S₂ x = none) :
    updateSEnv (S₁ ++ S₂) x T = updateSEnv S₁ x T ++ S₂ := by
  -- Compare lookups pointwise using extensionality.
  apply SEnv_ext
  intro y
  by_cases hEq : y = x
  · subst hEq
    -- Updated key wins on both sides.
    simp [lookupSEnv_update_eq, lookupSEnv_append_left]
  · -- Non-updated key: updates are transparent.
    have hUpd :
        lookupSEnv (updateSEnv (S₁ ++ S₂) x T) y = lookupSEnv (S₁ ++ S₂) y := by
      simpa using (lookupSEnv_update_neq (env:=S₁ ++ S₂) (x:=x) (y:=y) (T:=T) hEq)
    cases hS₁ : lookupSEnv S₁ y <;>
      simp [hUpd, hS₁, lookupSEnv_update_neq, hEq, lookupSEnv_append_left, lookupSEnv_append_right, hNone]

/-- Updating an appended SEnv always updates the left side. -/
private theorem updateSEnv_append_left_any {S₁ S₂ : SEnv} {x : Var} {T : ValType} :
    updateSEnv (S₁ ++ S₂) x T = updateSEnv S₁ x T ++ S₂ := by
  -- Compare lookups pointwise for all variables.
  apply SEnv_ext
  intro y
  by_cases hEq : y = x
  · -- Updated key wins on both sides.
    subst hEq
    simp [lookupSEnv_update_eq, lookupSEnv_append_left]
  · -- Non-updated keys are unchanged by update.
    have hUpd :
        lookupSEnv (updateSEnv (S₁ ++ S₂) x T) y = lookupSEnv (S₁ ++ S₂) y := by
      simpa using (lookupSEnv_update_neq (env:=S₁ ++ S₂) (x:=x) (y:=y) (T:=T) hEq)
    have hUpd₁ :
        lookupSEnv (updateSEnv S₁ x T) y = lookupSEnv S₁ y := by
      simpa using (lookupSEnv_update_neq (env:=S₁) (x:=x) (y:=y) (T:=T) hEq)
    cases hS₁ : lookupSEnv S₁ y <;>
      simp [hUpd, hUpd₁, hS₁, lookupSEnv_append_left, lookupSEnv_append_right]

/-- If a disjoint update environment contains x, the right side cannot. -/
private theorem lookupSEnv_none_of_disjoint_update
    {S₁ S₂ : SEnv} {x : Var} {T : ValType}
    (hDisj : DisjointS (updateSEnv S₁ x T) S₂) :
    lookupSEnv S₂ x = none := by
  -- Otherwise disjointness is violated at x.
  by_contra hSome
  cases hS2 : lookupSEnv S₂ x with
  | none => exact (hSome hS2).elim
  | some T₂ =>
      have hS1 : lookupSEnv (updateSEnv S₁ x T) x = some T := by
        simpa using (lookupSEnv_update_eq (env:=S₁) (x:=x) (T:=T))
      exact (hDisj x T T₂ hS1 hS2).elim

/-- Same-domain is preserved by a matching SEnv/store update. -/
private theorem StoreTypedStrong_sameDomain_update
    {S : SEnv} {store : Store} {x : Var} {T : ValType} {v : Value}
    (hDom : ∀ y, (lookupSEnv S y).isSome ↔ (lookupStr store y).isSome) :
    ∀ y, (lookupSEnv (updateSEnv S x T) y).isSome ↔
      (lookupStr (updateStr store x v) y).isSome := by
  -- Update is pointwise: only x changes.
  intro y
  by_cases hEq : y = x
  · subst hEq
    simp [lookupSEnv_update_eq, lookupStr_update_eq]
  · have hS : lookupSEnv (updateSEnv S x T) y = lookupSEnv S y := by
      simpa using (lookupSEnv_update_neq (env:=S) (x:=x) (y:=y) (T:=T) hEq)
    have hStr : lookupStr (updateStr store x v) y = lookupStr store y := by
      simpa using (lookupStr_update_neq store x y v hEq)
    simpa [hS, hStr] using hDom y

/-- StoreTypedStrong is stable under updating G at a single endpoint. -/
private theorem StoreTypedStrong_updateG
    {G : GEnv} {S : SEnv} {store : Store} {e : Endpoint} {L : LocalType}
    (hStore : StoreTypedStrong G S store) :
    StoreTypedStrong (updateG G e L) S store := by
  -- Same-domain is unchanged; typing weakens along updateG.
  refine ⟨?_, ?_⟩
  · intro x
    simpa using hStore.sameDomain x
  ·
    have hST : StoreTyped (updateG G e L) S store :=
      StoreTyped_send_preserved (G:=G) (S:=S) (store:=store) (e:=e) (L:=L) hStore.typeCorr
    exact hST

/-- Assignment preserves StoreTypedStrong on shared+owned SEnv. -/
private theorem StoreTypedStrong_assign_update
    {G : GEnv} {Ssh Sown : SEnv} {store : Store} {x : Var} {v : Value} {T : ValType}
    (hStore : StoreTypedStrong G (SEnvAll Ssh Sown) store)
    (hNone : lookupSEnv Ssh x = none)
    (hv : HasTypeVal G v T) :
    StoreTypedStrong G (SEnvAll Ssh (updateSEnv Sown x T)) (updateStr store x v) := by
  -- Same-domain updates pointwise; typing uses StoreTyped_assign_preserved.
  refine ⟨?_, ?_⟩
  ·
    have hDom := StoreTypedStrong_sameDomain_update (S:=SEnvAll Ssh Sown) (store:=store) hStore.sameDomain
    simpa [SEnvAll, updateSEnv_append_left hNone] using hDom
  ·
    have hST : StoreTyped G (updateSEnv (SEnvAll Ssh Sown) x T) (updateStr store x v) :=
      StoreTyped_assign_preserved (G:=G) (S:=SEnvAll Ssh Sown) (store:=store) (x:=x) (v:=v) (T:=T)
        hStore.typeCorr hv
    simpa [SEnvAll, updateSEnv_append_left hNone] using hST

/-- Receive preserves StoreTypedStrong on shared+owned SEnv. -/
private theorem StoreTypedStrong_recv_update
    {G : GEnv} {Ssh Sown : SEnv} {store : Store} {e : Endpoint} {L : LocalType}
    {x : Var} {v : Value} {T : ValType}
    (hStore : StoreTypedStrong G (SEnvAll Ssh Sown) store)
    (hNone : lookupSEnv Ssh x = none)
    (hv : HasTypeVal G v T) :
    StoreTypedStrong (updateG G e L) (SEnvAll Ssh (updateSEnv Sown x T)) (updateStr store x v) := by
  -- Same-domain updates pointwise; typing uses StoreTyped_recv_preserved.
  refine ⟨?_, ?_⟩
  ·
    have hDom := StoreTypedStrong_sameDomain_update (S:=SEnvAll Ssh Sown) (store:=store) hStore.sameDomain
    simpa [SEnvAll, updateSEnv_append_left hNone] using hDom
  ·
    have hST : StoreTyped (updateG G e L) (updateSEnv (SEnvAll Ssh Sown) x T) (updateStr store x v) :=
      StoreTyped_recv_preserved (G:=G) (S:=SEnvAll Ssh Sown) (store:=store) (e:=e) (L:=L)
        (x:=x) (v:=v) (T:=T) hStore.typeCorr hv
    simpa [SEnvAll, updateSEnv_append_left hNone] using hST

/-- Frame: send updates G on the left under a right context. -/
private theorem StoreTypedStrong_frame_send
    {G G₂ : GEnv} {Ssh Sown S₂ : SEnv} {store : Store}
    {e : Endpoint} {target : Role} {T : ValType} {L : LocalType}
    (hStore : StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store)
    (hG : lookupG G e = some (.send target T L)) :
    StoreTypedStrong (updateG G e L ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store := by
  -- Update G on the left; SEnv/store unchanged.
  have hStore' :
      StoreTypedStrong (updateG (G ++ G₂) e L) (SEnvAll Ssh (Sown ++ S₂)) store :=
    StoreTypedStrong_updateG (G:=G ++ G₂) (S:=SEnvAll Ssh (Sown ++ S₂))
      (store:=store) (e:=e) (L:=L) hStore
  have hGrew :
      updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
    updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.send target T L) (L':=L) hG
  simpa [hGrew] using hStore'

/-- Frame: select updates G on the left under a right context. -/
private theorem StoreTypedStrong_frame_select
    {G G₂ : GEnv} {Ssh Sown S₂ : SEnv} {store : Store}
    {e : Endpoint} {target : Role} {bs : List (Label × LocalType)} {L : LocalType}
    (hStore : StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store)
    (hG : lookupG G e = some (.select target bs)) :
    StoreTypedStrong (updateG G e L ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store := by
  -- Update G on the left; SEnv/store unchanged.
  have hStore' :
      StoreTypedStrong (updateG (G ++ G₂) e L) (SEnvAll Ssh (Sown ++ S₂)) store :=
    StoreTypedStrong_updateG (G:=G ++ G₂) (S:=SEnvAll Ssh (Sown ++ S₂))
      (store:=store) (e:=e) (L:=L) hStore
  have hGrew :
      updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
    updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.select target bs) (L':=L) hG
  simpa [hGrew] using hStore'

/-- Frame: branch updates G on the left under a right context. -/
private theorem StoreTypedStrong_frame_branch
    {G G₂ : GEnv} {Ssh Sown S₂ : SEnv} {store : Store}
    {e : Endpoint} {source : Role} {bs : List (Label × LocalType)} {L : LocalType}
    (hStore : StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store)
    (hG : lookupG G e = some (.branch source bs)) :
    StoreTypedStrong (updateG G e L ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store := by
  -- Update G on the left; SEnv/store unchanged.
  have hStore' :
      StoreTypedStrong (updateG (G ++ G₂) e L) (SEnvAll Ssh (Sown ++ S₂)) store :=
    StoreTypedStrong_updateG (G:=G ++ G₂) (S:=SEnvAll Ssh (Sown ++ S₂))
      (store:=store) (e:=e) (L:=L) hStore
  have hGrew :
      updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
    updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.branch source bs) (L':=L) hG
  simpa [hGrew] using hStore'

/-- Frame: assignment updates S on the left under a right context. -/
private theorem StoreTypedStrong_frame_assign
    {G G₂ : GEnv} {Ssh Sown S₂ : SEnv} {store : Store}
    {x : Var} {v : Value} {T : ValType}
    (hStore : StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store)
    (hNone : lookupSEnv Ssh x = none)
    (hv : HasTypeVal G v T) :
    StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (updateSEnv Sown x T ++ S₂)) (updateStr store x v) := by
  -- Lift hv to the framed G, then update SEnv/store.
  have hv' : HasTypeVal (G ++ G₂) v T :=
    HasTypeVal_mono G (G ++ G₂) v T hv (by
      intro ep L hLookup
      exact lookupG_append_left hLookup)
  have hStore' :
      StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (updateSEnv (Sown ++ S₂) x T))
        (updateStr store x v) :=
    StoreTypedStrong_assign_update (G:=G ++ G₂) (Ssh:=Ssh) (Sown:=Sown ++ S₂)
      (store:=store) (x:=x) (v:=v) (T:=T) hStore hNone hv'
  simpa [SEnvAll, updateSEnv_append_left_any] using hStore'

/-- Frame: receive updates S and G on the left under a right context. -/
private theorem StoreTypedStrong_frame_recv
    {G G₂ : GEnv} {Ssh Sown S₂ : SEnv} {store : Store}
    {e : Endpoint} {source : Role} {L : LocalType} {x : Var} {v : Value} {T : ValType} :
    StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store →
    lookupSEnv Ssh x = none →
    HasTypeVal G v T →
    lookupG G e = some (.recv source T L) →
    StoreTypedStrong (updateG G e L ++ G₂)
      (SEnvAll Ssh (updateSEnv Sown x T ++ S₂)) (updateStr store x v) := by
  -- Lift hv to the framed G, then update SEnv/store and rewrite updateG.
  intro hStore hNone hv hG
  have hv' : HasTypeVal (G ++ G₂) v T :=
    HasTypeVal_mono G (G ++ G₂) v T hv (by
      intro ep L' hLookup
      exact lookupG_append_left hLookup)
  have hStore' :
      StoreTypedStrong (updateG (G ++ G₂) e L)
        (SEnvAll Ssh (updateSEnv (Sown ++ S₂) x T)) (updateStr store x v) :=
    StoreTypedStrong_recv_update (G:=G ++ G₂) (Ssh:=Ssh) (Sown:=Sown ++ S₂)
      (store:=store) (e:=e) (L:=L) (x:=x) (v:=v) (T:=T) hStore hNone hv'
  have hGrew :
      updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
    updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.recv source T L) (L':=L) hG
  simpa [SEnvAll, updateSEnv_append_left_any, hGrew] using hStore'

/-- Frame helper: recv case discharges via pre-out. -/
private theorem StoreTypedStrong_preserved_frame_recv_case
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'}
    {G₂ : GEnv} {S₂ : SEnv} {Sfin Gfin W Δ}
    {e : Endpoint} {source : Role} {x : Var} {T : ValType} {L : LocalType} {v : Value} {vs : List Value} :
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store →
    HasTypeVal G v T →
    lookupG G e = some (.recv source T L) →
    G' = updateG G e L →
    Sown' = updateSEnv Sown x T →
    store' = updateStr store x v →
    StoreTypedStrong (G' ++ G₂) (SEnvAll Ssh (Sown' ++ S₂)) store' := by
  -- Use the recv frame lemma with pre-out's freshness.
  intro hPre hStore hv hG hGout hSout hStoreOut
  cases hPre with
  | recv_new _ _ hNone _ =>
      simpa [hGout, hSout, hStoreOut] using
        StoreTypedStrong_frame_recv (G₂:=G₂) (S₂:=S₂) hStore hNone hv hG
  | recv_old _ _ hNone _ =>
      simpa [hGout, hSout, hStoreOut] using
        StoreTypedStrong_frame_recv (G₂:=G₂) (S₂:=S₂) hStore hNone hv hG

/-- Frame helper: assign case discharges via pre-out. -/
private theorem StoreTypedStrong_preserved_frame_assign_case
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'}
    {G₂ : GEnv} {S₂ : SEnv} {Sfin Gfin W Δ}
    {x : Var} {v : Value} {T : ValType} :
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store →
    HasTypeVal G v T →
    Sown' = updateSEnv Sown x T →
    store' = updateStr store x v →
    StoreTypedStrong (G' ++ G₂) (SEnvAll Ssh (Sown' ++ S₂)) store' := by
  -- Use the assign frame lemma with pre-out's freshness.
  intro hPre hStore hv hSout hStoreOut
  cases hPre with
  | assign_new hNone _ _ =>
      simpa [hSout, hStoreOut] using
        StoreTypedStrong_frame_assign (G₂:=G₂) (S₂:=S₂) hStore hNone hv
  | assign_old hNone _ _ =>
      simpa [hSout, hStoreOut] using
        StoreTypedStrong_frame_assign (G₂:=G₂) (S₂:=S₂) hStore hNone hv

/-- Frame helper: seq case passes the pre-out to the IH. -/
private theorem StoreTypedStrong_preserved_frame_seq_case
    {G D Ssh Sown store bufs P Q G' D' Sown' store' bufs' P'}
    {G₂ : GEnv} {S₂ : SEnv} {Sfin Gfin W Δ}
    (ih :
      StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store →
      HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
      StoreTypedStrong (G' ++ G₂) (SEnvAll Ssh (Sown' ++ S₂)) store')
    (hPre : HasTypeProcPreOut Ssh Sown G (.seq P Q) Sfin Gfin W Δ)
    (hStore : StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store) :
    StoreTypedStrong (G' ++ G₂) (SEnvAll Ssh (Sown' ++ S₂)) store' := by
  -- Extract the pre-out for P and apply the IH.
  cases hPre with
  | seq hPreP _ =>
      exact ih hStore hPreP

/-- Frame helper: par-left case passes the left pre-out to the IH. -/
private theorem StoreTypedStrong_preserved_frame_par_left_case
    {G D Ssh Sown store bufs P Q G' D' Sown' store' bufs' P'}
    {G₂ : GEnv} {S₂ : SEnv} {Sfin Gfin W Δ}
    (ih :
      StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store →
      HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
      StoreTypedStrong (G' ++ G₂) (SEnvAll Ssh (Sown' ++ S₂)) store')
    (hPre : HasTypeProcPreOut Ssh Sown G (.par P Q) Sfin Gfin W Δ)
    (hStore : StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store) :
    StoreTypedStrong (G' ++ G₂) (SEnvAll Ssh (Sown' ++ S₂)) store' := by
  -- Extract the left pre-out and apply the IH.
  cases hPre with
  | par _ _ _ _ _ _ _ _ _ _ _ _ _ hPreL _ =>
      exact ih hStore hPreL

/-- Frame helper: par-right case passes the right pre-out to the IH. -/
private theorem StoreTypedStrong_preserved_frame_par_right_case
    {G D Ssh Sown store bufs P Q G' D' Sown' store' bufs' P'}
    {G₂ : GEnv} {S₂ : SEnv} {Sfin Gfin W Δ}
    (ih :
      StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store →
      HasTypeProcPreOut Ssh Sown G Q Sfin Gfin W Δ →
      StoreTypedStrong (G' ++ G₂) (SEnvAll Ssh (Sown' ++ S₂)) store')
    (hPre : HasTypeProcPreOut Ssh Sown G (.par P Q) Sfin Gfin W Δ)
    (hStore : StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store) :
    StoreTypedStrong (G' ++ G₂) (SEnvAll Ssh (Sown' ++ S₂)) store' := by
  -- Extract the right pre-out and apply the IH.
  cases hPre with
  | par _ _ _ _ _ _ _ _ _ _ _ _ _ _ hPreR =>
      exact ih hStore hPreR

/-- Store typing is preserved by a framed TypedStep. -/
private theorem StoreTypedStrong_preserved_frame_left
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'}
    {G₂ : GEnv} {S₂ : SEnv} {Sfin Gfin W Δ} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    StoreTypedStrong (G' ++ G₂) (SEnvAll Ssh (Sown' ++ S₂)) store' := by
  -- Use induction to reuse the frame lemma for structural steps.
  intro hTS hStore hPre; induction hTS generalizing Sfin Gfin W Δ with
  | send _ _ hG _ _ _ _ hGout _ _ =>
      simpa [hGout] using StoreTypedStrong_frame_send (G₂:=G₂) (S₂:=S₂) hStore hG
  | recv _ hG _ _ hv _ hGout _ hSout hStoreOut _ =>
      exact StoreTypedStrong_preserved_frame_recv_case (G₂:=G₂) (S₂:=S₂) hPre hStore hv hG hGout hSout hStoreOut
  | select _ hG _ _ _ hGout _ _ =>
      simpa [hGout] using StoreTypedStrong_frame_select (G₂:=G₂) (S₂:=S₂) hStore hG
  | branch _ hG _ _ _ _ _ hGout _ _ =>
      simpa [hGout] using StoreTypedStrong_frame_branch (G₂:=G₂) (S₂:=S₂) hStore hG
  | assign hv _ hSout hStoreOut =>
      exact StoreTypedStrong_preserved_frame_assign_case (G₂:=G₂) (S₂:=S₂) hPre hStore hv hSout hStoreOut
  | seq_step hTS ih =>
      exact StoreTypedStrong_preserved_frame_seq_case (G₂:=G₂) (S₂:=S₂) ih hPre hStore
  | seq_skip | par_skip_left | par_skip_right =>
      simpa using hStore
  | par_left _ _ _ _ _ _ _ ih =>
      exact StoreTypedStrong_preserved_frame_par_left_case (G₂:=G₂) (S₂:=S₂) ih hPre hStore
  | par_right _ _ _ _ _ _ _ ih =>
      exact StoreTypedStrong_preserved_frame_par_right_case (G₂:=G₂) (S₂:=S₂) ih hPre hStore
  -- skip cases handled above

/-- Store typing is preserved by TypedStep. -/
theorem StoreTypedStrong_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'}
    {Sfin Gfin W Δ} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    StoreTypedStrong G (SEnvAll Ssh Sown) store →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    StoreTypedStrong G' (SEnvAll Ssh Sown') store' := by
  -- Use the frame lemma with empty right context.
  intro hTS hStore hPre
  simpa using
    (StoreTypedStrong_preserved_frame_left (G₂:=∅) (S₂:=∅) hTS hStore hPre)

private theorem BuffersTyped_weakenG
    {G G' : GEnv} {D : DEnv} {bufs : Buffers}
    (hBT : BuffersTyped G D bufs)
    (hMono : ∀ ep L, lookupG G ep = some L → lookupG G' ep = some L) :
    BuffersTyped G' D bufs := by
  -- Lift buffer typing along a monotone GEnv map.
  intro e
  rcases hBT e with ⟨hLen, hTyping⟩
  refine ⟨hLen, ?_⟩
  intro i hi
  exact HasTypeVal_mono G G' _ _ (hTyping i hi) hMono

private theorem BuffersTyped_rewriteD
    {G : GEnv} {D D' : DEnv} {bufs : Buffers}
    (hEq : ∀ e, lookupD D' e = lookupD D e)
    (hBT : BuffersTyped G D bufs) :
    BuffersTyped G D' bufs := by
  -- Rewrite the trace lookup edge-wise.
  intro e
  rcases hBT e with ⟨hLen, hTyping⟩
  refine ⟨?_, ?_⟩
  · simpa [hEq e] using hLen
  · intro i hi
    simpa [hEq e] using hTyping i hi

private theorem sid_not_in_right_of_left {G₁ G₂ : GEnv} (hDisj : DisjointG G₁ G₂)
    {s : SessionId} (hIn : s ∈ SessionsOf G₁) : s ∉ SessionsOf G₂ := by
  -- Disjoint session sets cannot share a member.
  intro hIn2
  have hInter : s ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hIn, hIn2⟩
  have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = ∅ := by
    simpa [DisjointG, GEnvDisjoint] using hDisj
  have : s ∈ (∅ : Set SessionId) := by simpa [hEmpty] using hInter
  exact this.elim

private theorem DEnv_find_none_of_notin_sessions {G : GEnv} {D : DEnv}
    (hCons : DConsistent G D) {e : Edge} (hNot : e.sid ∉ SessionsOf G) :
    D.find? e = none := by
  -- An edge entry would witness a forbidden session id.
  by_cases hNone : D.find? e = none
  · exact hNone
  · cases hSome : D.find? e with
    | none => exact (hNone hSome).elim
    | some ts =>
        have hSid : e.sid ∈ SessionsOfD D := ⟨e, ts, hSome, rfl⟩
        have hSidG : e.sid ∈ SessionsOf G := hCons hSid
        exact (hNot hSidG).elim

private theorem lookupD_of_find {D : DEnv} {e : Edge} {ts : List ValType}
    (hFind : D.find? e = some ts) :
    lookupD D e = ts := by
  -- Unfold lookupD and rewrite with find?.
  simp [lookupD, hFind]

private theorem lookupD_append_left_of_find {D₁ D₂ : DEnv} {e : Edge} {ts : List ValType}
    (hFind : D₁.find? e = some ts) :
    lookupD (D₁ ++ D₂) e = ts := by
  -- Append prefers the left entry when present.
  have hFind' := findD_append_left (D₁:=D₁) (D₂:=D₂) (e:=e) (ts:=ts) hFind
  simpa [lookupD, hFind'] using (lookupD_of_find (D:=D₁) (e:=e) hFind)

private theorem findD_update_neq {D : DEnv} {e ep : Edge} {ts : List ValType}
    (hEq : ep ≠ e) :
    (updateD D e ts).find? ep = D.find? ep := by
  -- Update at e leaves other edges unchanged.
  simp [updateD, DEnv.find?, hEq]

private theorem lookupD_update_append_left
    {D₁ D₂ : DEnv} {e ep : Edge} {ts : List ValType}
    (hNone : D₂.find? e = none) :
    lookupD (updateD (D₁ ++ D₂) e ts) ep =
      lookupD ((updateD D₁ e ts) ++ D₂) ep := by
  -- Split on whether we query the updated edge.
  by_cases hEq : ep = e
  · subst hEq
    have hLeft : lookupD (updateD (D₁ ++ D₂) e ts) e = ts := lookupD_update_eq _ _ _
    have hFind : (updateD D₁ e ts).find? e = some ts := by
      simp [updateD, DEnv.find?]
    have hRight : lookupD ((updateD D₁ e ts) ++ D₂) e = ts :=
      lookupD_append_left_of_find (D₁:=updateD D₁ e ts) (D₂:=D₂) hFind
    simpa [hLeft, hRight]
  · have hUpdL :
        lookupD (updateD (D₁ ++ D₂) e ts) ep = lookupD (D₁ ++ D₂) ep :=
      lookupD_update_neq (env:=D₁ ++ D₂) (e:=e) (e':=ep) (ts:=ts) hEq
    have hUpdR :
        lookupD (updateD D₁ e ts) ep = lookupD D₁ ep :=
      lookupD_update_neq (env:=D₁) (e:=e) (e':=ep) (ts:=ts) hEq
    cases hFind : D₁.find? ep with
    | some ts' =>
        have hFind' : (updateD D₁ e ts).find? ep = some ts' :=
          by simpa [findD_update_neq (e:=e) (ep:=ep) (ts:=ts) hEq] using hFind
        have hLeft : lookupD (D₁ ++ D₂) ep = ts' :=
          lookupD_append_left_of_find (D₁:=D₁) (D₂:=D₂) hFind
        have hRight : lookupD ((updateD D₁ e ts) ++ D₂) ep = ts' :=
          lookupD_append_left_of_find (D₁:=updateD D₁ e ts) (D₂:=D₂) hFind'
        simpa [hUpdL, hUpdR, hLeft, hRight]
    | none =>
        have hFind' : (updateD D₁ e ts).find? ep = none :=
          by simpa [findD_update_neq (e:=e) (ep:=ep) (ts:=ts) hEq] using hFind
        have hLeft : lookupD (D₁ ++ D₂) ep = lookupD D₂ ep :=
          lookupD_append_right (D₁:=D₁) (D₂:=D₂) (e:=ep) hFind
        have hRight : lookupD ((updateD D₁ e ts) ++ D₂) ep = lookupD D₂ ep :=
          lookupD_append_right (D₁:=updateD D₁ e ts) (D₂:=D₂) (e:=ep) hFind'
        simpa [hUpdL, hUpdR, hLeft, hRight]

private theorem lookupD_update_append_right
    {D₁ D₂ : DEnv} {e ep : Edge} {ts : List ValType}
    (hNone : D₁.find? e = none) :
    lookupD (updateD (D₁ ++ D₂) e ts) ep =
      lookupD (D₁ ++ updateD D₂ e ts) ep := by
  -- Split on whether we query the updated edge.
  by_cases hEq : ep = e
  · subst hEq
    have hLeft : lookupD (updateD (D₁ ++ D₂) e ts) e = ts := lookupD_update_eq _ _ _
    have hRight : lookupD (D₁ ++ updateD D₂ e ts) e = ts := by
      have hFind : (updateD D₂ e ts).find? e = some ts := by
        simp [updateD, DEnv.find?]
      have hFind' : (D₁ ++ updateD D₂ e ts).find? e = some ts := by
        simpa [findD_append_right (D₁:=D₁) (D₂:=updateD D₂ e ts) (e:=e) hNone] using hFind
      simp [lookupD, hFind']
    simpa [hLeft, hRight]
  · have hUpdL :
        lookupD (updateD (D₁ ++ D₂) e ts) ep = lookupD (D₁ ++ D₂) ep :=
      lookupD_update_neq (env:=D₁ ++ D₂) (e:=e) (e':=ep) (ts:=ts) hEq
    cases hFind : D₁.find? ep with
    | some ts' =>
        have hLeft : lookupD (D₁ ++ D₂) ep = ts' :=
          lookupD_append_left_of_find (D₁:=D₁) (D₂:=D₂) hFind
        have hRight : lookupD (D₁ ++ updateD D₂ e ts) ep = ts' :=
          lookupD_append_left_of_find (D₁:=D₁) (D₂:=updateD D₂ e ts) hFind
        simpa [hUpdL, hLeft, hRight]
    | none =>
        have hFind' : (updateD D₂ e ts).find? ep = D₂.find? ep :=
          findD_update_neq (e:=e) (ep:=ep) (ts:=ts) hEq
        have hLeft : lookupD (D₁ ++ D₂) ep = lookupD D₂ ep :=
          lookupD_append_right (D₁:=D₁) (D₂:=D₂) (e:=ep) hFind
        have hRight : lookupD (D₁ ++ updateD D₂ e ts) ep = lookupD D₂ ep := by
          have hRight' : (D₁ ++ updateD D₂ e ts).find? ep = (updateD D₂ e ts).find? ep := by
            simpa using (findD_append_right (D₁:=D₁) (D₂:=updateD D₂ e ts) (e:=ep) hFind)
          simp [lookupD, hRight', hFind'] 
        simpa [hUpdL, hLeft, hRight]

private theorem lookupG_update_append_left
    {G₁ G₂ : GEnv} {e ep : Endpoint} {L Lold : LocalType}
    (hG : lookupG G₁ e = some Lold) :
    lookupG (updateG (G₁ ++ G₂) e L) ep =
      lookupG ((updateG G₁ e L) ++ G₂) ep := by
  -- Split on whether we query the updated endpoint.
  by_cases hEq : ep = e
  · subst hEq
    have hLeft : lookupG (updateG G₁ e L) e = some L := lookupG_update_eq _ _ _
    have hRight : lookupG (updateG (G₁ ++ G₂) e L) e = some L := lookupG_update_eq _ _ _
    have hApp : lookupG ((updateG G₁ e L) ++ G₂) e = some L :=
      lookupG_append_left (G₁:=updateG G₁ e L) (G₂:=G₂) (e:=e) (L:=L) hLeft
    simpa [hRight, hApp]
  · have hUpd : lookupG (updateG (G₁ ++ G₂) e L) ep = lookupG (G₁ ++ G₂) ep :=
      lookupG_update_neq (env:=G₁ ++ G₂) (e:=e) (e':=ep) (L:=L) hEq
    have hUpd1 : lookupG (updateG G₁ e L) ep = lookupG G₁ ep :=
      lookupG_update_neq (env:=G₁) (e:=e) (e':=ep) (L:=L) hEq
    cases hLookup : lookupG G₁ ep with
    | none =>
        have hLeftNone : lookupG (updateG G₁ e L) ep = none := by simpa [hUpd1, hLookup]
        have hAppL :
            lookupG ((updateG G₁ e L) ++ G₂) ep = lookupG G₂ ep :=
          lookupG_append_right (G₁:=updateG G₁ e L) (G₂:=G₂) (e:=ep) hLeftNone
        have hAppR : lookupG (G₁ ++ G₂) ep = lookupG G₂ ep :=
          lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=ep) hLookup
        simpa [hUpd, hAppL, hAppR]
    | some L₁ =>
        have hLeftSome : lookupG (updateG G₁ e L) ep = some L₁ := by
          simpa [hUpd1] using hLookup
        have hAppL :
            lookupG ((updateG G₁ e L) ++ G₂) ep = some L₁ :=
          lookupG_append_left (G₁:=updateG G₁ e L) (G₂:=G₂) (e:=ep) (L:=L₁) hLeftSome
        have hAppR : lookupG (G₁ ++ G₂) ep = some L₁ :=
          lookupG_append_left (G₁:=G₁) (G₂:=G₂) (e:=ep) (L:=L₁) hLookup
        simpa [hUpd, hAppL, hAppR]

private theorem lookupG_update_append_right
    {G₁ G₂ : GEnv} {e ep : Endpoint} {L : LocalType}
    (hNone : lookupG G₁ e = none) :
    lookupG (updateG (G₁ ++ G₂) e L) ep =
      lookupG (G₁ ++ updateG G₂ e L) ep := by
  -- Split on whether we query the updated endpoint.
  by_cases hEq : ep = e
  · subst hEq
    have hRight : lookupG (updateG (G₁ ++ G₂) e L) e = some L := lookupG_update_eq _ _ _
    have hLeft : lookupG (updateG G₂ e L) e = some L := lookupG_update_eq _ _ _
    have hApp : lookupG (G₁ ++ updateG G₂ e L) e = some L :=
      lookupG_append_right (G₁:=G₁) (G₂:=updateG G₂ e L) (e:=e) (by simpa [hNone])
    simpa [hRight, hApp]
  · have hUpd : lookupG (updateG (G₁ ++ G₂) e L) ep = lookupG (G₁ ++ G₂) ep :=
      lookupG_update_neq (env:=G₁ ++ G₂) (e:=e) (e':=ep) (L:=L) hEq
    cases hLookup : lookupG G₁ ep with
    | some L₁ =>
        have hAppR : lookupG (G₁ ++ G₂) ep = some L₁ :=
          lookupG_append_left (G₁:=G₁) (G₂:=G₂) (e:=ep) (L:=L₁) hLookup
        have hAppL : lookupG (G₁ ++ updateG G₂ e L) ep = some L₁ :=
          lookupG_append_left (G₁:=G₁) (G₂:=updateG G₂ e L) (e:=ep) (L:=L₁) hLookup
        simpa [hUpd, hAppL, hAppR]
    | none =>
        have hAppR : lookupG (G₁ ++ G₂) ep = lookupG G₂ ep :=
          lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=ep) hLookup
        have hAppL : lookupG (G₁ ++ updateG G₂ e L) ep = lookupG (updateG G₂ e L) ep :=
          lookupG_append_right (G₁:=G₁) (G₂:=updateG G₂ e L) (e:=ep) hLookup
        have hUpd2 : lookupG (updateG G₂ e L) ep = lookupG G₂ ep :=
          lookupG_update_neq (env:=G₂) (e:=e) (e':=ep) (L:=L) hEq
        simpa [hUpd, hAppL, hAppR, hUpd2]

private theorem BuffersTyped_send_frame_left
    {G : GEnv} {D : DEnv} {G₂ : GEnv} {D₂ : DEnv} {bufs bufs' : Buffers}
    {e : Endpoint} {target : Role} {T : ValType} {L : LocalType} {v : Value}
    {sendEdge : Edge} :
    lookupG G e = some (.send target T L) →
    HasTypeVal G v T →
    sendEdge = { sid := e.sid, sender := e.role, receiver := target } →
    DisjointG G G₂ →
    DConsistent G₂ D₂ →
    BuffersTyped (G ++ G₂) (D ++ D₂) bufs →
    BuffersTyped (updateG G e L ++ G₂)
      (appendD D sendEdge T ++ D₂)
      (enqueueBuf bufs sendEdge v) := by
  -- Frame the send preservation over an appended environment.
  intro hG hv hEdge hDisj hCons hBT
  have hG' : lookupG (G ++ G₂) e = some (.send target T L) :=
    lookupG_append_left (G₁:=G) (G₂:=G₂) hG
  have hv' : HasTypeVal (G ++ G₂) v T :=
    HasTypeVal_mono G (G ++ G₂) v T hv (by
      intro ep L hLookup; exact lookupG_append_left (G₁:=G) (G₂:=G₂) hLookup)
  have hBT' := BuffersTyped_send_preserved (G:=G ++ G₂) (D:=D ++ D₂) (bufs:=bufs)
    (senderEp:=e) (receiverRole:=target) (T:=T) (L:=L) (v:=v) hBT hv' hG'
  have hSid : sendEdge.sid ∈ SessionsOf G := by simpa [hEdge] using ⟨e, .send target T L, hG, rfl⟩
  have hNot : sendEdge.sid ∉ SessionsOf G₂ := sid_not_in_right_of_left hDisj hSid
  have hNone : D₂.find? sendEdge = none := DEnv_find_none_of_notin_sessions hCons hNot
  have hTraceEq : lookupD (D ++ D₂) sendEdge = lookupD D sendEdge :=
    lookupD_append_left_of_right_none (D₁:=D) (D₂:=D₂) (e:=sendEdge) hNone
  have hBT'' : BuffersTyped (updateG (G ++ G₂) e L)
      (updateD (D ++ D₂) sendEdge (lookupD D sendEdge ++ [T])) (enqueueBuf bufs sendEdge v) := by
    simpa [hTraceEq] using hBT'
  have hDrew : ∀ e', lookupD (updateD (D ++ D₂) sendEdge (lookupD D sendEdge ++ [T])) e' =
      lookupD ((updateD D sendEdge (lookupD D sendEdge ++ [T])) ++ D₂) e' := by
    intro e'
    exact lookupD_update_append_left (D₁:=D) (D₂:=D₂) (e:=sendEdge) (ep:=e') (ts:=lookupD D sendEdge ++ [T]) hNone
  have hBT''' := BuffersTyped_rewriteD hDrew hBT''
  have hGrew : ∀ ep L', lookupG (updateG (G ++ G₂) e L) ep = some L' →
      lookupG ((updateG G e L) ++ G₂) ep = some L' := by
    intro ep L' hLookup
    have hEq := lookupG_update_append_left (G₁:=G) (G₂:=G₂) (e:=e) (ep:=ep) (L:=L) (Lold:=.send target T L) hG
    simpa [hEq] using hLookup
  exact BuffersTyped_weakenG hBT''' hGrew

private theorem BuffersTyped_recv_frame_left
    {G : GEnv} {D : DEnv} {G₂ : GEnv} {D₂ : DEnv} {bufs bufs' : Buffers}
    {e : Endpoint} {source : Role} {T : ValType} {L : LocalType} {v : Value} {vs : List Value}
    {recvEdge : Edge} :
    lookupG G e = some (.recv source T L) →
    lookupBuf bufs recvEdge = v :: vs →
    HasTypeVal G v T →
    recvEdge = { sid := e.sid, sender := source, receiver := e.role } →
    DisjointG G G₂ →
    DConsistent G₂ D₂ →
    BuffersTyped (G ++ G₂) (D ++ D₂) bufs →
    BuffersTyped (updateG G e L ++ G₂)
      (updateD D recvEdge (lookupD D recvEdge).tail ++ D₂)
      (updateBuf bufs recvEdge vs) := by
  -- Frame the recv preservation over an appended environment.
  intro hG hBuf hv hEdge hDisj hCons hBT
  have hG' : lookupG (G ++ G₂) e = some (.recv source T L) :=
    lookupG_append_left (G₁:=G) (G₂:=G₂) hG
  have hv' : HasTypeVal (G ++ G₂) v T :=
    HasTypeVal_mono G (G ++ G₂) v T hv (by
      intro ep L hLookup; exact lookupG_append_left (G₁:=G) (G₂:=G₂) hLookup)
  have hBT' := BuffersTyped_recv_preserved (G:=G ++ G₂) (D:=D ++ D₂) (bufs:=bufs)
    (receiverEp:=e) (senderRole:=source) (T:=T) (L:=L) (v:=v) (vs:=vs) hBT hBuf hv' hG'
  have hSid : recvEdge.sid ∈ SessionsOf G := by simpa [hEdge] using ⟨e, .recv source T L, hG, rfl⟩
  have hNot : recvEdge.sid ∉ SessionsOf G₂ := sid_not_in_right_of_left hDisj hSid
  have hNone : D₂.find? recvEdge = none := DEnv_find_none_of_notin_sessions hCons hNot
  have hTraceEq : lookupD (D ++ D₂) recvEdge = lookupD D recvEdge :=
    lookupD_append_left_of_right_none (D₁:=D) (D₂:=D₂) (e:=recvEdge) hNone
  have hBT'' : BuffersTyped (updateG (G ++ G₂) e L)
      (updateD (D ++ D₂) recvEdge (lookupD D recvEdge).tail) (updateBuf bufs recvEdge vs) := by
    simpa [hTraceEq] using hBT'
  have hDrew : ∀ e', lookupD (updateD (D ++ D₂) recvEdge (lookupD D recvEdge).tail) e' =
      lookupD ((updateD D recvEdge (lookupD D recvEdge).tail) ++ D₂) e' := by
    intro e'
    exact lookupD_update_append_left (D₁:=D) (D₂:=D₂) (e:=recvEdge) (ep:=e') (ts:=(lookupD D recvEdge).tail) hNone
  have hBT''' := BuffersTyped_rewriteD hDrew hBT''
  have hGrew : ∀ ep L', lookupG (updateG (G ++ G₂) e L) ep = some L' →
      lookupG ((updateG G e L) ++ G₂) ep = some L' := by
    intro ep L' hLookup
    have hEq := lookupG_update_append_left (G₁:=G) (G₂:=G₂) (e:=e) (ep:=ep) (L:=L) (Lold:=.recv source T L) hG
    simpa [hEq] using hLookup
  exact BuffersTyped_weakenG hBT''' hGrew

private theorem BuffersTyped_select_frame_left
    {G : GEnv} {D : DEnv} {G₂ : GEnv} {D₂ : DEnv} {bufs bufs' : Buffers}
    {e : Endpoint} {target : Role} {bs : List (String × LocalType)}
    {ℓ : String} {L : LocalType} {selectEdge : Edge} :
    lookupG G e = some (.select target bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    selectEdge = { sid := e.sid, sender := e.role, receiver := target } →
    DisjointG G G₂ →
    DConsistent G₂ D₂ →
    BuffersTyped (G ++ G₂) (D ++ D₂) bufs →
    BuffersTyped (updateG G e L ++ G₂)
      (updateD D selectEdge (lookupD D selectEdge ++ [.string]) ++ D₂)
      (enqueueBuf bufs selectEdge (.string ℓ)) := by
  -- Frame the select preservation over an appended environment.
  intro hG hFind hEdge hDisj hCons hBT
  have hG' : lookupG (G ++ G₂) e = some (.select target bs) :=
    lookupG_append_left (G₁:=G) (G₂:=G₂) hG
  have hBT' := BuffersTyped_select_preserved (G:=G ++ G₂) (D:=D ++ D₂) (bufs:=bufs)
    (selectorEp:=e) (targetRole:=target) (bs:=bs) (ℓ:=ℓ) (L:=L) hBT hG' hFind
  have hSid : selectEdge.sid ∈ SessionsOf G := by simpa [hEdge] using ⟨e, .select target bs, hG, rfl⟩
  have hNot : selectEdge.sid ∉ SessionsOf G₂ := sid_not_in_right_of_left hDisj hSid
  have hNone : D₂.find? selectEdge = none := DEnv_find_none_of_notin_sessions hCons hNot
  have hTraceEq : lookupD (D ++ D₂) selectEdge = lookupD D selectEdge :=
    lookupD_append_left_of_right_none (D₁:=D) (D₂:=D₂) (e:=selectEdge) hNone
  have hBT'' : BuffersTyped (updateG (G ++ G₂) e L)
      (updateD (D ++ D₂) selectEdge (lookupD D selectEdge ++ [.string])) (enqueueBuf bufs selectEdge (.string ℓ)) := by
    simpa [hTraceEq] using hBT'
  have hDrew : ∀ e', lookupD (updateD (D ++ D₂) selectEdge (lookupD D selectEdge ++ [.string])) e' =
      lookupD ((updateD D selectEdge (lookupD D selectEdge ++ [.string])) ++ D₂) e' := by
    intro e'
    exact lookupD_update_append_left (D₁:=D) (D₂:=D₂) (e:=selectEdge) (ep:=e') (ts:=lookupD D selectEdge ++ [.string]) hNone
  have hBT''' := BuffersTyped_rewriteD hDrew hBT''
  have hGrew : ∀ ep L', lookupG (updateG (G ++ G₂) e L) ep = some L' →
      lookupG ((updateG G e L) ++ G₂) ep = some L' := by
    intro ep L' hLookup
    have hEq := lookupG_update_append_left (G₁:=G) (G₂:=G₂) (e:=e) (ep:=ep) (L:=L) (Lold:=.select target bs) hG
    simpa [hEq] using hLookup
  exact BuffersTyped_weakenG hBT''' hGrew

private theorem BuffersTyped_branch_frame_left
    {G : GEnv} {D : DEnv} {G₂ : GEnv} {D₂ : DEnv} {bufs bufs' : Buffers}
    {e : Endpoint} {source : Role} {bs : List (String × LocalType)}
    {ℓ : String} {L : LocalType} {vs : List Value} {branchEdge : Edge} :
    lookupG G e = some (.branch source bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    lookupBuf bufs branchEdge = .string ℓ :: vs →
    branchEdge = { sid := e.sid, sender := source, receiver := e.role } →
    DisjointG G G₂ →
    DConsistent G₂ D₂ →
    BuffersTyped (G ++ G₂) (D ++ D₂) bufs →
    BuffersTyped (updateG G e L ++ G₂)
      (updateD D branchEdge (lookupD D branchEdge).tail ++ D₂)
      (updateBuf bufs branchEdge vs) := by
  -- Frame the branch preservation over an appended environment.
  intro hG hFind hBuf hEdge hDisj hCons hBT
  have hG' : lookupG (G ++ G₂) e = some (.branch source bs) :=
    lookupG_append_left (G₁:=G) (G₂:=G₂) hG
  have hBT' := BuffersTyped_branch_preserved (G:=G ++ G₂) (D:=D ++ D₂) (bufs:=bufs)
    (brancherEp:=e) (senderRole:=source) (bs:=bs) (ℓ:=ℓ) (L:=L) (vs:=vs) hBT hBuf hG' hFind
  have hSid : branchEdge.sid ∈ SessionsOf G := by simpa [hEdge] using ⟨e, .branch source bs, hG, rfl⟩
  have hNot : branchEdge.sid ∉ SessionsOf G₂ := sid_not_in_right_of_left hDisj hSid
  have hNone : D₂.find? branchEdge = none := DEnv_find_none_of_notin_sessions hCons hNot
  have hTraceEq : lookupD (D ++ D₂) branchEdge = lookupD D branchEdge :=
    lookupD_append_left_of_right_none (D₁:=D) (D₂:=D₂) (e:=branchEdge) hNone
  have hBT'' : BuffersTyped (updateG (G ++ G₂) e L)
      (updateD (D ++ D₂) branchEdge (lookupD D branchEdge).tail) (updateBuf bufs branchEdge vs) := by
    simpa [hTraceEq] using hBT'
  have hDrew : ∀ e', lookupD (updateD (D ++ D₂) branchEdge (lookupD D branchEdge).tail) e' =
      lookupD ((updateD D branchEdge (lookupD D branchEdge).tail) ++ D₂) e' := by
    intro e'
    exact lookupD_update_append_left (D₁:=D) (D₂:=D₂) (e:=branchEdge) (ep:=e') (ts:=(lookupD D branchEdge).tail) hNone
  have hBT''' := BuffersTyped_rewriteD hDrew hBT''
  have hGrew : ∀ ep L', lookupG (updateG (G ++ G₂) e L) ep = some L' →
      lookupG ((updateG G e L) ++ G₂) ep = some L' := by
    intro ep L' hLookup
    have hEq := lookupG_update_append_left (G₁:=G) (G₂:=G₂) (e:=e) (ep:=ep) (L:=L) (Lold:=.branch source bs) hG
    simpa [hEq] using hLookup
  exact BuffersTyped_weakenG hBT''' hGrew

private theorem BuffersTyped_send_frame_right
    {G : GEnv} {D : DEnv} {G₁ : GEnv} {D₁ : DEnv} {bufs bufs' : Buffers}
    {e : Endpoint} {target : Role} {T : ValType} {L : LocalType} {v : Value}
    {sendEdge : Edge} :
    lookupG G e = some (.send target T L) →
    HasTypeVal G v T →
    sendEdge = { sid := e.sid, sender := e.role, receiver := target } →
    DisjointG G₁ G →
    DConsistent G₁ D₁ →
    BuffersTyped (G₁ ++ G) (D₁ ++ D) bufs →
    BuffersTyped (G₁ ++ updateG G e L)
      (D₁ ++ appendD D sendEdge T)
      (enqueueBuf bufs sendEdge v) := by
  -- Frame the send preservation on the right side.
  intro hG hv hEdge hDisj hCons hBT
  have hNone : lookupG G₁ e = none := DisjointG_lookup_left (G₁:=G₁) (G₂:=G) hDisj hG
  have hG' : lookupG (G₁ ++ G) e = some (.send target T L) := by
    simpa [lookupG_append_right (G₁:=G₁) (G₂:=G) (e:=e) hNone] using hG
  have hv' : HasTypeVal (G₁ ++ G) v T :=
    HasTypeVal_mono G (G₁ ++ G) v T hv (by
      intro ep L hLookup
      have hNone' : lookupG G₁ ep = none :=
        DisjointG_lookup_left (G₁:=G₁) (G₂:=G) hDisj hLookup
      simpa [lookupG_append_right (G₁:=G₁) (G₂:=G) (e:=ep) hNone'] using hLookup)
  have hBT' := BuffersTyped_send_preserved (G:=G₁ ++ G) (D:=D₁ ++ D) (bufs:=bufs)
    (senderEp:=e) (receiverRole:=target) (T:=T) (L:=L) (v:=v) hBT hv' hG'
  have hSid : sendEdge.sid ∈ SessionsOf G := by simpa [hEdge] using ⟨e, .send target T L, hG, rfl⟩
  have hNot : sendEdge.sid ∉ SessionsOf G₁ := by
    have hDisj' := DisjointG_symm hDisj
    exact sid_not_in_right_of_left hDisj' hSid
  have hNoneD : D₁.find? sendEdge = none := DEnv_find_none_of_notin_sessions hCons hNot
  have hBT'' : BuffersTyped (updateG (G₁ ++ G) e L)
      (updateD (D₁ ++ D) sendEdge (lookupD D sendEdge ++ [T])) (enqueueBuf bufs sendEdge v) := by
    have hTraceEq : lookupD (D₁ ++ D) sendEdge = lookupD D sendEdge :=
      lookupD_append_right (D₁:=D₁) (D₂:=D) (e:=sendEdge) hNoneD
    simpa [hTraceEq] using hBT'
  have hDrew : ∀ e', lookupD (updateD (D₁ ++ D) sendEdge (lookupD D sendEdge ++ [T])) e' =
      lookupD (D₁ ++ updateD D sendEdge (lookupD D sendEdge ++ [T])) e' := by
    intro e'
    exact lookupD_update_append_right (D₁:=D₁) (D₂:=D) (e:=sendEdge) (ep:=e') (ts:=lookupD D sendEdge ++ [T]) hNoneD
  have hBT''' := BuffersTyped_rewriteD hDrew hBT''
  have hGrew : ∀ ep L', lookupG (updateG (G₁ ++ G) e L) ep = some L' →
      lookupG (G₁ ++ updateG G e L) ep = some L' := by
    intro ep L' hLookup
    have hEq := lookupG_update_append_right (G₁:=G₁) (G₂:=G) (e:=e) (ep:=ep) (L:=L) hNone
    simpa [hEq] using hLookup
  exact BuffersTyped_weakenG hBT''' hGrew

private theorem BuffersTyped_recv_frame_right
    {G : GEnv} {D : DEnv} {G₁ : GEnv} {D₁ : DEnv} {bufs bufs' : Buffers}
    {e : Endpoint} {source : Role} {T : ValType} {L : LocalType} {v : Value} {vs : List Value}
    {recvEdge : Edge} :
    lookupG G e = some (.recv source T L) →
    lookupBuf bufs recvEdge = v :: vs →
    HasTypeVal G v T →
    recvEdge = { sid := e.sid, sender := source, receiver := e.role } →
    DisjointG G₁ G →
    DConsistent G₁ D₁ →
    BuffersTyped (G₁ ++ G) (D₁ ++ D) bufs →
    BuffersTyped (G₁ ++ updateG G e L)
      (D₁ ++ updateD D recvEdge (lookupD D recvEdge).tail)
      (updateBuf bufs recvEdge vs) := by
  -- Frame the recv preservation on the right side.
  intro hG hBuf hv hEdge hDisj hCons hBT
  have hNone : lookupG G₁ e = none := DisjointG_lookup_left (G₁:=G₁) (G₂:=G) hDisj hG
  have hG' : lookupG (G₁ ++ G) e = some (.recv source T L) := by
    simpa [lookupG_append_right (G₁:=G₁) (G₂:=G) (e:=e) hNone] using hG
  have hv' : HasTypeVal (G₁ ++ G) v T :=
    HasTypeVal_mono G (G₁ ++ G) v T hv (by
      intro ep L hLookup
      have hNone' : lookupG G₁ ep = none :=
        DisjointG_lookup_left (G₁:=G₁) (G₂:=G) hDisj hLookup
      simpa [lookupG_append_right (G₁:=G₁) (G₂:=G) (e:=ep) hNone'] using hLookup)
  have hBT' := BuffersTyped_recv_preserved (G:=G₁ ++ G) (D:=D₁ ++ D) (bufs:=bufs)
    (receiverEp:=e) (senderRole:=source) (T:=T) (L:=L) (v:=v) (vs:=vs) hBT hBuf hv' hG'
  have hSid : recvEdge.sid ∈ SessionsOf G := by simpa [hEdge] using ⟨e, .recv source T L, hG, rfl⟩
  have hNot : recvEdge.sid ∉ SessionsOf G₁ := by
    have hDisj' := DisjointG_symm hDisj
    exact sid_not_in_right_of_left hDisj' hSid
  have hNoneD : D₁.find? recvEdge = none := DEnv_find_none_of_notin_sessions hCons hNot
  have hBT'' : BuffersTyped (updateG (G₁ ++ G) e L)
      (updateD (D₁ ++ D) recvEdge (lookupD D recvEdge).tail) (updateBuf bufs recvEdge vs) := by
    have hTraceEq : lookupD (D₁ ++ D) recvEdge = lookupD D recvEdge :=
      lookupD_append_right (D₁:=D₁) (D₂:=D) (e:=recvEdge) hNoneD
    simpa [hTraceEq] using hBT'
  have hDrew : ∀ e', lookupD (updateD (D₁ ++ D) recvEdge (lookupD D recvEdge).tail) e' =
      lookupD (D₁ ++ updateD D recvEdge (lookupD D recvEdge).tail) e' := by
    intro e'
    exact lookupD_update_append_right (D₁:=D₁) (D₂:=D) (e:=recvEdge) (ep:=e') (ts:=(lookupD D recvEdge).tail) hNoneD
  have hBT''' := BuffersTyped_rewriteD hDrew hBT''
  have hGrew : ∀ ep L', lookupG (updateG (G₁ ++ G) e L) ep = some L' →
      lookupG (G₁ ++ updateG G e L) ep = some L' := by
    intro ep L' hLookup
    have hEq := lookupG_update_append_right (G₁:=G₁) (G₂:=G) (e:=e) (ep:=ep) (L:=L) hNone
    simpa [hEq] using hLookup
  exact BuffersTyped_weakenG hBT''' hGrew

private theorem BuffersTyped_select_frame_right
    {G : GEnv} {D : DEnv} {G₁ : GEnv} {D₁ : DEnv} {bufs bufs' : Buffers}
    {e : Endpoint} {target : Role} {bs : List (String × LocalType)}
    {ℓ : String} {L : LocalType} {selectEdge : Edge} :
    lookupG G e = some (.select target bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    selectEdge = { sid := e.sid, sender := e.role, receiver := target } →
    DisjointG G₁ G →
    DConsistent G₁ D₁ →
    BuffersTyped (G₁ ++ G) (D₁ ++ D) bufs →
    BuffersTyped (G₁ ++ updateG G e L)
      (D₁ ++ updateD D selectEdge (lookupD D selectEdge ++ [.string]))
      (enqueueBuf bufs selectEdge (.string ℓ)) := by
  -- Frame the select preservation on the right side.
  intro hG hFind hEdge hDisj hCons hBT
  have hNone : lookupG G₁ e = none := DisjointG_lookup_left (G₁:=G₁) (G₂:=G) hDisj hG
  have hG' : lookupG (G₁ ++ G) e = some (.select target bs) := by
    simpa [lookupG_append_right (G₁:=G₁) (G₂:=G) (e:=e) hNone] using hG
  have hBT' := BuffersTyped_select_preserved (G:=G₁ ++ G) (D:=D₁ ++ D) (bufs:=bufs)
    (selectorEp:=e) (targetRole:=target) (bs:=bs) (ℓ:=ℓ) (L:=L) hBT hG' hFind
  have hSid : selectEdge.sid ∈ SessionsOf G := by simpa [hEdge] using ⟨e, .select target bs, hG, rfl⟩
  have hNot : selectEdge.sid ∉ SessionsOf G₁ := by
    have hDisj' := DisjointG_symm hDisj
    exact sid_not_in_right_of_left hDisj' hSid
  have hNoneD : D₁.find? selectEdge = none := DEnv_find_none_of_notin_sessions hCons hNot
  have hBT'' : BuffersTyped (updateG (G₁ ++ G) e L)
      (updateD (D₁ ++ D) selectEdge (lookupD D selectEdge ++ [.string])) (enqueueBuf bufs selectEdge (.string ℓ)) := by
    have hTraceEq : lookupD (D₁ ++ D) selectEdge = lookupD D selectEdge :=
      lookupD_append_right (D₁:=D₁) (D₂:=D) (e:=selectEdge) hNoneD
    simpa [hTraceEq] using hBT'
  have hDrew : ∀ e', lookupD (updateD (D₁ ++ D) selectEdge (lookupD D selectEdge ++ [.string])) e' =
      lookupD (D₁ ++ updateD D selectEdge (lookupD D selectEdge ++ [.string])) e' := by
    intro e'
    exact lookupD_update_append_right (D₁:=D₁) (D₂:=D) (e:=selectEdge) (ep:=e') (ts:=lookupD D selectEdge ++ [.string]) hNoneD
  have hBT''' := BuffersTyped_rewriteD hDrew hBT''
  have hGrew : ∀ ep L', lookupG (updateG (G₁ ++ G) e L) ep = some L' →
      lookupG (G₁ ++ updateG G e L) ep = some L' := by
    intro ep L' hLookup
    have hEq := lookupG_update_append_right (G₁:=G₁) (G₂:=G) (e:=e) (ep:=ep) (L:=L) hNone
    simpa [hEq] using hLookup
  exact BuffersTyped_weakenG hBT''' hGrew

private theorem BuffersTyped_branch_frame_right
    {G : GEnv} {D : DEnv} {G₁ : GEnv} {D₁ : DEnv} {bufs bufs' : Buffers}
    {e : Endpoint} {source : Role} {bs : List (String × LocalType)}
    {ℓ : String} {L : LocalType} {vs : List Value} {branchEdge : Edge} :
    lookupG G e = some (.branch source bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    lookupBuf bufs branchEdge = .string ℓ :: vs →
    branchEdge = { sid := e.sid, sender := source, receiver := e.role } →
    DisjointG G₁ G →
    DConsistent G₁ D₁ →
    BuffersTyped (G₁ ++ G) (D₁ ++ D) bufs →
    BuffersTyped (G₁ ++ updateG G e L)
      (D₁ ++ updateD D branchEdge (lookupD D branchEdge).tail)
      (updateBuf bufs branchEdge vs) := by
  -- Frame the branch preservation on the right side.
  intro hG hFind hBuf hEdge hDisj hCons hBT
  have hNone : lookupG G₁ e = none := DisjointG_lookup_left (G₁:=G₁) (G₂:=G) hDisj hG
  have hG' : lookupG (G₁ ++ G) e = some (.branch source bs) := by
    simpa [lookupG_append_right (G₁:=G₁) (G₂:=G) (e:=e) hNone] using hG
  have hBT' := BuffersTyped_branch_preserved (G:=G₁ ++ G) (D:=D₁ ++ D) (bufs:=bufs)
    (brancherEp:=e) (senderRole:=source) (bs:=bs) (ℓ:=ℓ) (L:=L) (vs:=vs) hBT hBuf hG' hFind
  have hSid : branchEdge.sid ∈ SessionsOf G := by simpa [hEdge] using ⟨e, .branch source bs, hG, rfl⟩
  have hNot : branchEdge.sid ∉ SessionsOf G₁ := by
    have hDisj' := DisjointG_symm hDisj
    exact sid_not_in_right_of_left hDisj' hSid
  have hNoneD : D₁.find? branchEdge = none := DEnv_find_none_of_notin_sessions hCons hNot
  have hBT'' : BuffersTyped (updateG (G₁ ++ G) e L)
      (updateD (D₁ ++ D) branchEdge (lookupD D branchEdge).tail) (updateBuf bufs branchEdge vs) := by
    have hTraceEq : lookupD (D₁ ++ D) branchEdge = lookupD D branchEdge :=
      lookupD_append_right (D₁:=D₁) (D₂:=D) (e:=branchEdge) hNoneD
    simpa [hTraceEq] using hBT'
  have hDrew : ∀ e', lookupD (updateD (D₁ ++ D) branchEdge (lookupD D branchEdge).tail) e' =
      lookupD (D₁ ++ updateD D branchEdge (lookupD D branchEdge).tail) e' := by
    intro e'
    exact lookupD_update_append_right (D₁:=D₁) (D₂:=D) (e:=branchEdge) (ep:=e') (ts:=(lookupD D branchEdge).tail) hNoneD
  have hBT''' := BuffersTyped_rewriteD hDrew hBT''
  have hGrew : ∀ ep L', lookupG (updateG (G₁ ++ G) e L) ep = some L' →
      lookupG (G₁ ++ updateG G e L) ep = some L' := by
    intro ep L' hLookup
    have hEq := lookupG_update_append_right (G₁:=G₁) (G₂:=G) (e:=e) (ep:=ep) (L:=L) hNone
    simpa [hEq] using hLookup
  exact BuffersTyped_weakenG hBT''' hGrew

private theorem BuffersTyped_preserved_frame_left
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    ∀ {G₂ D₂}, DisjointG G G₂ → DConsistent G₂ D₂ →
      BuffersTyped (G ++ G₂) (D ++ D₂) bufs →
      BuffersTyped (G' ++ G₂) (D' ++ D₂) bufs' := by
  -- Case split on the step; only send/recv/select/branch change buffers.
  intro hTS
  induction hTS generalizing G₂ D₂ with
  | send _ _ hG _ hv _ hEdge hGout hDout hBufsOut =>
      intro G₂ D₂ hDisj hCons hBT
      simpa [hGout, hDout, hBufsOut, hEdge, appendD] using
        BuffersTyped_send_frame_left (G:=G) (D:=D) (G₂:=G₂) (D₂:=D₂) (bufs:=bufs)
          (e:=_) (target:=_) (T:=_) (L:=_) (v:=_) (sendEdge:=_) hG hv hEdge hDisj hCons hBT
  | recv _ hG hEdge hBuf hv _ hGout hDout _ _ hBufsOut =>
      intro G₂ D₂ hDisj hCons hBT
      simpa [hGout, hDout, hBufsOut, hEdge] using
        BuffersTyped_recv_frame_left (G:=G) (D:=D) (G₂:=G₂) (D₂:=D₂) (bufs:=bufs)
          (e:=_) (source:=_) (T:=_) (L:=_) (v:=_) (vs:=_) (recvEdge:=_) hG hBuf hv hEdge hDisj hCons hBT
  | select _ hG hFind _ hEdge hGout hDout hBufsOut =>
      intro G₂ D₂ hDisj hCons hBT
      simpa [hGout, hDout, hBufsOut, hEdge] using
        BuffersTyped_select_frame_left (G:=G) (D:=D) (G₂:=G₂) (D₂:=D₂) (bufs:=bufs)
          (e:=_) (target:=_) (bs:=_) (ℓ:=_) (L:=_) (selectEdge:=_) hG hFind hEdge hDisj hCons hBT
  | branch _ hG hEdge hBuf _ hFind _ hGout hDout hBufsOut =>
      intro G₂ D₂ hDisj hCons hBT
      simpa [hGout, hDout, hBufsOut, hEdge] using
        BuffersTyped_branch_frame_left (G:=G) (D:=D) (G₂:=G₂) (D₂:=D₂) (bufs:=bufs)
          (e:=_) (source:=_) (bs:=_) (ℓ:=_) (L:=_) (vs:=_) (branchEdge:=_) hG hFind hBuf hEdge hDisj hCons hBT
  | assign =>
      intro _ _ _ _ hBT
      simpa using hBT
  | seq_step _ ih =>
      intro G₂ D₂ hDisj hCons hBT
      exact ih hDisj hCons hBT
  | seq_skip =>
      intro _ _ _ _ hBT
      simpa using hBT
  | par_left _ _ _ _ _ _ ih =>
      intro _ _ hDisj hCons hBT
      exact ih hDisj hCons hBT
  | par_right _ _ _ _ _ _ ih =>
      intro _ _ hDisj hCons hBT
      exact ih hDisj hCons hBT
  | par_skip_left =>
      intro _ _ _ _ hBT
      simpa using hBT
  | par_skip_right =>
      intro _ _ _ _ hBT
      simpa using hBT

private theorem BuffersTyped_preserved_frame_right
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    ∀ {G₁ D₁}, DisjointG G₁ G → DConsistent G₁ D₁ →
      BuffersTyped (G₁ ++ G) (D₁ ++ D) bufs →
      BuffersTyped (G₁ ++ G') (D₁ ++ D') bufs' := by
  -- Symmetric framing when the step sits on the right of append.
  intro hTS
  induction hTS generalizing G₁ D₁ with
  | send _ _ hG _ hv _ hEdge hGout hDout hBufsOut =>
      intro G₁ D₁ hDisj hCons hBT
      simpa [hGout, hDout, hBufsOut, hEdge, appendD] using
        BuffersTyped_send_frame_right (G:=G) (D:=D) (G₁:=G₁) (D₁:=D₁) (bufs:=bufs)
          (e:=_) (target:=_) (T:=_) (L:=_) (v:=_) (sendEdge:=_) hG hv hEdge hDisj hCons hBT
  | recv _ hG hEdge hBuf hv _ hGout hDout _ _ hBufsOut =>
      intro G₁ D₁ hDisj hCons hBT
      simpa [hGout, hDout, hBufsOut, hEdge] using
        BuffersTyped_recv_frame_right (G:=G) (D:=D) (G₁:=G₁) (D₁:=D₁) (bufs:=bufs)
          (e:=_) (source:=_) (T:=_) (L:=_) (v:=_) (vs:=_) (recvEdge:=_) hG hBuf hv hEdge hDisj hCons hBT
  | select _ hG hFind _ hEdge hGout hDout hBufsOut =>
      intro G₁ D₁ hDisj hCons hBT
      simpa [hGout, hDout, hBufsOut, hEdge] using
        BuffersTyped_select_frame_right (G:=G) (D:=D) (G₁:=G₁) (D₁:=D₁) (bufs:=bufs)
          (e:=_) (target:=_) (bs:=_) (ℓ:=_) (L:=_) (selectEdge:=_) hG hFind hEdge hDisj hCons hBT
  | branch _ hG hEdge hBuf _ hFind _ hGout hDout hBufsOut =>
      intro G₁ D₁ hDisj hCons hBT
      simpa [hGout, hDout, hBufsOut, hEdge] using
        BuffersTyped_branch_frame_right (G:=G) (D:=D) (G₁:=G₁) (D₁:=D₁) (bufs:=bufs)
          (e:=_) (source:=_) (bs:=_) (ℓ:=_) (L:=_) (vs:=_) (branchEdge:=_) hG hFind hBuf hEdge hDisj hCons hBT
  | assign =>
      intro _ _ _ _ hBT
      simpa using hBT
  | seq_step _ ih =>
      intro G₁ D₁ hDisj hCons hBT
      exact ih hDisj hCons hBT
  | seq_skip =>
      intro _ _ _ _ hBT
      simpa using hBT
  | par_left _ _ _ _ _ _ ih =>
      intro _ _ hDisj hCons hBT
      exact ih hDisj hCons hBT
  | par_right _ _ _ _ _ _ ih =>
      intro _ _ hDisj hCons hBT
      exact ih hDisj hCons hBT
  | par_skip_left =>
      intro _ _ _ _ hBT
      simpa using hBT
  | par_skip_right =>
      intro _ _ _ _ hBT
      simpa using hBT

/-- Buffer typing is preserved by TypedStep. -/
theorem BuffersTyped_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    BuffersTyped G D bufs →
    BuffersTyped G' D' bufs' := by
  -- Induct on the step; par cases use framed preservation.
  intro hTS hBT
  induction hTS with
  | send _ _ hG _ hv _ hEdge hGout hDout hBufsOut =>
      simpa [hGout, hDout, hBufsOut, hEdge, appendD] using
        BuffersTyped_send_preserved (G:=G) (D:=D) (bufs:=bufs)
          (senderEp:=_) (receiverRole:=_) (T:=_) (L:=_) (v:=_) hBT hv hG
  | recv _ hG hEdge hBuf hv _ hGout hDout _ _ hBufsOut =>
      simpa [hGout, hDout, hBufsOut, hEdge] using
        BuffersTyped_recv_preserved (G:=G) (D:=D) (bufs:=bufs)
          (receiverEp:=_) (senderRole:=_) (T:=_) (L:=_) (v:=_) (vs:=_) hBT hBuf hv hG
  | select _ hG hFind _ hEdge hGout hDout hBufsOut =>
      simpa [hGout, hDout, hBufsOut, hEdge] using
        BuffersTyped_select_preserved (G:=G) (D:=D) (bufs:=bufs)
          (selectorEp:=_) (targetRole:=_) (bs:=_) (ℓ:=_) (L:=_) hBT hG hFind
  | branch _ hG hEdge hBuf _ hFind _ hGout hDout hBufsOut =>
      simpa [hGout, hDout, hBufsOut, hEdge] using
        BuffersTyped_branch_preserved (G:=G) (D:=D) (bufs:=bufs)
          (brancherEp:=_) (senderRole:=_) (bs:=_) (ℓ:=_) (L:=_) (vs:=_) hBT hBuf hG hFind
  | assign =>
      simpa using hBT
  | seq_step _ ih =>
      exact ih hBT
  | seq_skip =>
      simpa using hBT
  | par_left _ hTS hDisjG _ _ _ hConsR _ =>
      exact BuffersTyped_preserved_frame_left hTS hDisjG hConsR hBT
  | par_right _ hTS hDisjG _ _ hConsL _ _ =>
      exact BuffersTyped_preserved_frame_right hTS hDisjG hConsL hBT
  | par_skip_left =>
      simpa using hBT
  | par_skip_right =>
      simpa using hBT

private theorem HeadCoherent_split_left {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} :
    HeadCoherent (G₁ ++ G₂) (D₁ ++ D₂) →
    DisjointG G₁ G₂ →
    SessionsOfD D₂ ⊆ SessionsOf G₂ →
    HeadCoherent G₁ D₁ := by
  -- Push receiver lookups into the left side and drop D₂ using disjoint sessions.
  intro hHead hDisj hSubD e
  set recvEp : Endpoint := ⟨e.sid, e.receiver⟩
  cases hLookup : lookupG G₁ recvEp with
  | none =>
      simp [HeadCoherent, hLookup]
  | some L =>
      have hLookup' : lookupG (G₁ ++ G₂) recvEp = some L :=
        lookupG_append_left (G₁:=G₁) (G₂:=G₂) hLookup
      have hSid : e.sid ∈ SessionsOf G₁ := ⟨recvEp, L, hLookup, rfl⟩
      have hNot : e.sid ∉ SessionsOf G₂ := sid_not_in_right_of_left hDisj hSid
      have hNone : D₂.find? e = none := DEnv_find_none_of_notin_sessions hSubD hNot
      have hTrace : lookupD (D₁ ++ D₂) e = lookupD D₁ e :=
        lookupD_append_left_of_right_none (D₁:=D₁) (D₂:=D₂) (e:=e) hNone
      simpa [HeadCoherent, hLookup, hLookup', hTrace] using hHead e

private theorem HeadCoherent_split_right {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} :
    HeadCoherent (G₁ ++ G₂) (D₁ ++ D₂) →
    DisjointG G₁ G₂ →
    SessionsOfD D₁ ⊆ SessionsOf G₁ →
    HeadCoherent G₂ D₂ := by
  -- Symmetric split: route receiver lookups into the right side.
  intro hHead hDisj hSubD e
  set recvEp : Endpoint := ⟨e.sid, e.receiver⟩
  cases hLookup : lookupG G₂ recvEp with
  | none =>
      simp [HeadCoherent, hLookup]
  | some L =>
      have hSid : e.sid ∈ SessionsOf G₂ := ⟨recvEp, L, hLookup, rfl⟩
      have hNot : e.sid ∉ SessionsOf G₁ :=
        sid_not_in_right_of_left (DisjointG_symm hDisj) hSid
      have hNone : D₁.find? e = none := DEnv_find_none_of_notin_sessions hSubD hNot
      have hLookup' : lookupG (G₁ ++ G₂) recvEp = some L := by
        have hNoneG : lookupG G₁ recvEp = none :=
          lookupG_none_of_not_session (G:=G₁) (e:=recvEp) hNot
        simpa [lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=recvEp) hNoneG] using hLookup
      have hTrace : lookupD (D₁ ++ D₂) e = lookupD D₂ e :=
        lookupD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) hNone
      simpa [HeadCoherent, hLookup, hLookup', hTrace] using hHead e

private theorem HeadCoherent_append {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} :
    HeadCoherent G₁ D₁ →
    HeadCoherent G₂ D₂ →
    DisjointG G₁ G₂ →
    SessionsOfD D₁ ⊆ SessionsOf G₁ →
    SessionsOfD D₂ ⊆ SessionsOf G₂ →
    HeadCoherent (G₁ ++ G₂) (D₁ ++ D₂) := by
  -- Split on whether the receiver endpoint comes from the left or right.
  intro hHead1 hHead2 hDisj hSub1 hSub2 e
  set recvEp : Endpoint := ⟨e.sid, e.receiver⟩
  cases hLookup : lookupG (G₁ ++ G₂) recvEp with
  | none =>
      simp [HeadCoherent, hLookup]
  | some L =>
      have hInv := lookupG_append_inv (G₁:=G₁) (G₂:=G₂) (e:=recvEp) hLookup
      cases hInv with
      | inl hLeft =>
          have hSid : e.sid ∈ SessionsOf G₁ := ⟨recvEp, L, hLeft, rfl⟩
          have hNot : e.sid ∉ SessionsOf G₂ := sid_not_in_right_of_left hDisj hSid
          have hNone : D₂.find? e = none := DEnv_find_none_of_notin_sessions hSub2 hNot
          have hTrace : lookupD (D₁ ++ D₂) e = lookupD D₁ e :=
            lookupD_append_left_of_right_none (D₁:=D₁) (D₂:=D₂) (e:=e) hNone
          simpa [HeadCoherent, hLookup, hLeft, hTrace] using hHead1 e
      | inr hRight =>
          have hSid : e.sid ∈ SessionsOf G₂ := ⟨recvEp, L, hRight.2, rfl⟩
          have hNot : e.sid ∉ SessionsOf G₁ :=
            sid_not_in_right_of_left (DisjointG_symm hDisj) hSid
          have hNone : D₁.find? e = none := DEnv_find_none_of_notin_sessions hSub1 hNot
          have hTrace : lookupD (D₁ ++ D₂) e = lookupD D₂ e :=
            lookupD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) hNone
          simpa [HeadCoherent, hLookup, hRight.2, hTrace] using hHead2 e

private theorem HeadCoherent_preserved_send
    {G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'} :
    lookupG G e = some (.send target T L) →
    (∀ Lrecv, lookupG G { sid := e.sid, role := target } = some Lrecv →
      ∃ L', Consume e.role Lrecv (lookupD D { sid := e.sid, sender := e.role, receiver := target }) = some L' ∧
            (Consume e.role L' [T]).isSome) →
    sendEdge = { sid := e.sid, sender := e.role, receiver := target } →
    G' = updateG G e L →
    D' = appendD D sendEdge T →
    Coherent G D →
    HeadCoherent G D →
    HeadCoherent G' D' := by
  -- Dispatch to the send preservation lemma and rewrite updates.
  intro hG hRecvReady hEdge hGout hDout hCoh hHead
  simpa [hGout, hDout, hEdge, appendD] using
    HeadCoherent_send_preserved (G:=G) (D:=D) (senderEp:=e)
      (receiverRole:=target) (T:=T) (L:=L) hHead hCoh hG hRecvReady

private theorem HeadCoherent_preserved_recv
    {G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'} :
    lookupG G e = some (.recv source T L) →
    recvEdge = { sid := e.sid, sender := source, receiver := e.role } →
    (lookupD D recvEdge).head? = some T →
    G' = updateG G e L →
    D' = updateD D recvEdge (lookupD D recvEdge).tail →
    Coherent G D →
    HeadCoherent G D →
    HeadCoherent G' D' := by
  -- Use recv preservation with RoleComplete derived from sender existence.
  intro hG hEdge hTrace hGout hDout hCoh hHead
  have hTrace' :
      (lookupD D { sid := e.sid, sender := source, receiver := e.role }).head? = some T := by
    rw [← hEdge]; exact hTrace
  simpa [hGout, hDout, hEdge] using
    HeadCoherent_recv_preserved (G:=G) (D:=D) (receiverEp:=e) (senderRole:=source)
      (Trecv:=T) (L:=L) hHead hCoh hG hTrace'

private theorem HeadCoherent_preserved_select
    {G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'} :
    lookupG G e = some (.select target bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    (∀ Ltarget, lookupG G { sid := e.sid, role := target } = some Ltarget →
      ∃ L', Consume e.role Ltarget (lookupD D { sid := e.sid, sender := e.role, receiver := target }) = some L' ∧
            (Consume e.role L' [.string]).isSome) →
    selectEdge = { sid := e.sid, sender := e.role, receiver := target } →
    G' = updateG G e L →
    D' = appendD D selectEdge .string →
    Coherent G D →
    HeadCoherent G D →
    HeadCoherent G' D' := by
  -- Dispatch to the select preservation lemma and rewrite updates.
  intro hG hFind hTargetReady hEdge hGout hDout hCoh hHead
  simpa [hGout, hDout, hEdge, appendD] using
    HeadCoherent_select_preserved (G:=G) (D:=D) (selectorEp:=e) (targetRole:=target)
      (bs:=bs) (ℓ:=ℓ) (L:=L) hHead hCoh hG hFind hTargetReady

private theorem HeadCoherent_preserved_branch
    {G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'} :
    lookupG G e = some (.branch source bs) →
    branchEdge = { sid := e.sid, sender := source, receiver := e.role } →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    (lookupD D branchEdge).head? = some .string →
    G' = updateG G e L →
    D' = updateD D branchEdge (lookupD D branchEdge).tail →
    Coherent G D →
    HeadCoherent G D →
    HeadCoherent G' D' := by
  -- Branch is the recv-style case on labels.
  intro hG hEdge hFind hTrace hGout hDout hCoh hHead
  have hTrace' :
      (lookupD D { sid := e.sid, sender := source, receiver := e.role }).head? = some .string := by
    rw [← hEdge]; exact hTrace
  simpa [hGout, hDout, hEdge] using
    HeadCoherent_branch_preserved (G:=G) (D:=D) (brancherEp:=e) (senderRole:=source)
      (bs:=bs) (ℓ:=ℓ) (L:=L) hHead hCoh hG hFind hTrace'

private theorem HeadCoherent_preserved_par_left
    {Ssh store bufs store' bufs' P P' Q S G D₁ D₂ G₁' D₁' S₁'} (split : ParSplit S G) :
    TypedStep split.G1 D₁ Ssh split.S1 store bufs P G₁' D₁' S₁' store' bufs' P' →
    DisjointG split.G1 split.G2 →
    DConsistent split.G1 D₁ →
    DConsistent split.G2 D₂ →
    Coherent (split.G1 ++ split.G2) (D₁ ++ D₂) →
    HeadCoherent (split.G1 ++ split.G2) (D₁ ++ D₂) →
    (Coherent split.G1 D₁ → HeadCoherent split.G1 D₁ → HeadCoherent G₁' D₁') →
    HeadCoherent (G₁' ++ split.G2) (D₁' ++ D₂) := by
  -- Split head coherence, apply IH on the left, then re-append.
  intro hTS hDisjG hConsL hConsR hCoh hHead ih
  have hHeadL : HeadCoherent split.G1 D₁ := HeadCoherent_split_left hHead hDisjG hConsR
  have hHeadR : HeadCoherent split.G2 D₂ := HeadCoherent_split_right hHead hDisjG hConsL
  have hCohL : Coherent split.G1 D₁ := Coherent_split_left hCoh hDisjG
  have hHeadL' : HeadCoherent G₁' D₁' := ih hCohL hHeadL
  have hSubG : SessionsOf G₁' ⊆ SessionsOf split.G1 := SessionsOf_subset_of_TypedStep hTS
  have hDisjG' : DisjointG G₁' split.G2 := DisjointG_of_subset_left hSubG hDisjG
  have hSubD : SessionsOfD D₁' ⊆ SessionsOf split.G1 := by
    intro s hs
    have hs' : s ∈ SessionsOfD D₁ ∪ SessionsOf split.G1 :=
      SessionsOfD_subset_of_TypedStep hTS hs
    cases hs' with
    | inl hD1 => exact hConsL hD1
    | inr hG1 => exact hG1
  exact HeadCoherent_append hHeadL' hHeadR hDisjG' hSubD hConsR

private theorem HeadCoherent_preserved_par_right
    {Ssh store bufs store' bufs' P Q Q' S G D₁ D₂ G₂' D₂' S₂'} (split : ParSplit S G) :
    TypedStep split.G2 D₂ Ssh split.S2 store bufs Q G₂' D₂' S₂' store' bufs' Q' →
    DisjointG split.G1 split.G2 →
    DConsistent split.G1 D₁ →
    DConsistent split.G2 D₂ →
    Coherent (split.G1 ++ split.G2) (D₁ ++ D₂) →
    HeadCoherent (split.G1 ++ split.G2) (D₁ ++ D₂) →
    (Coherent split.G2 D₂ → HeadCoherent split.G2 D₂ → HeadCoherent G₂' D₂') →
    HeadCoherent (split.G1 ++ G₂') (D₁ ++ D₂') := by
  -- Split head coherence, apply IH on the right, then re-append.
  intro hTS hDisjG hConsL hConsR hCoh hHead ih
  have hHeadL : HeadCoherent split.G1 D₁ := HeadCoherent_split_left hHead hDisjG hConsR
  have hHeadR : HeadCoherent split.G2 D₂ := HeadCoherent_split_right hHead hDisjG hConsL
  have hCohR : Coherent split.G2 D₂ := Coherent_split_right hCoh hDisjG hConsL
  have hHeadR' : HeadCoherent G₂' D₂' := ih hCohR hHeadR
  have hSubG : SessionsOf G₂' ⊆ SessionsOf split.G2 := SessionsOf_subset_of_TypedStep hTS
  have hDisjG' : DisjointG split.G1 G₂' := by
    have hDisjGsym : DisjointG split.G2 split.G1 := DisjointG_symm hDisjG
    have hDisjG'' : DisjointG G₂' split.G1 := DisjointG_of_subset_left hSubG hDisjGsym
    exact DisjointG_symm hDisjG''
  have hSubD : SessionsOfD D₂' ⊆ SessionsOf split.G2 := by
    intro s hs
    have hs' : s ∈ SessionsOfD D₂ ∪ SessionsOf split.G2 :=
      SessionsOfD_subset_of_TypedStep hTS hs
    cases hs' with
    | inl hD2 => exact hConsR hD2
    | inr hG2 => exact hG2
  exact HeadCoherent_append hHeadL hHeadR' hDisjG' hConsL hSubD

/-- Head coherence is preserved by TypedStep. -/
theorem HeadCoherent_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    Coherent G D →
    HeadCoherent G D →
    HeadCoherent G' D' := by
  -- Induct on the step; par cases reassemble via disjoint append lemmas.
  intro hTS hCoh hHead
  induction hTS with
  | send _ _ hG _ _ hRecvReady hEdge hGout hDout _ =>
      exact HeadCoherent_preserved_send hG hRecvReady hEdge hGout hDout hCoh hHead
  | recv _ hG hEdge _ _ hTrace hGout hDout _ _ _ =>
      exact HeadCoherent_preserved_recv hG hEdge hTrace hGout hDout hCoh hHead
  | select _ hG hFind hTargetReady hEdge hGout hDout _ =>
      exact HeadCoherent_preserved_select hG hFind hTargetReady hEdge hGout hDout hCoh hHead
  | branch _ hG hEdge _ _ hFindT hTrace hGout hDout _ =>
      exact HeadCoherent_preserved_branch hG hEdge hFindT hTrace hGout hDout hCoh hHead
  | assign =>
      exact hHead
  | seq_step _ ih =>
      exact ih hCoh hHead
  | seq_skip =>
      exact hHead
  | par_left split hTS hDisjG _ _ hConsL hConsR ih =>
      exact HeadCoherent_preserved_par_left split hTS hDisjG hConsL hConsR hCoh hHead ih
  | par_right split hTS hDisjG _ _ hConsL hConsR ih =>
      exact HeadCoherent_preserved_par_right split hTS hDisjG hConsL hConsR hCoh hHead ih
  | par_skip_left =>
      exact hHead
  | par_skip_right =>
      exact hHead

private theorem ValidLabels_rewriteG {G₁ G₂ : GEnv} {D : DEnv} {bufs : Buffers} :
    (∀ ep, lookupG G₁ ep = lookupG G₂ ep) →
    ValidLabels G₁ D bufs →
    ValidLabels G₂ D bufs := by
  -- Rewrite the receiver lookup through the provided equality.
  intro hEq hValid e source bs hBranch
  have hBranch' : lookupG G₁ ⟨e.sid, e.receiver⟩ = some (.branch source bs) := by
    simpa [hEq] using hBranch
  exact hValid e source bs hBranch'

private theorem HasTypeVal_append_right
    {G₁ G : GEnv} {v : Value} {T : ValType} :
    DisjointG G₁ G →
    HasTypeVal G v T →
    HasTypeVal (G₁ ++ G) v T := by
  -- Lift value typing using right-biased lookup under disjointness.
  intro hDisj hVal
  apply HasTypeVal_mono G (G₁ ++ G) v T hVal
  intro ep L hLookup
  have hNone : lookupG G₁ ep = none :=
    DisjointG_lookup_left (G₁:=G) (G₂:=G₁) (DisjointG_symm hDisj) hLookup
  simpa [lookupG_append_right (G₁:=G₁) (G₂:=G) (e:=ep) hNone] using hLookup

private theorem SendReady_append_left
    {G : GEnv} {D : DEnv} {G₂ : GEnv} {D₂ : DEnv}
    {e : Endpoint} {target : Role} {T : ValType} {L : LocalType} {sendEdge : Edge} :
    lookupG G e = some (.send target T L) →
    (∀ Lrecv, lookupG G { sid := e.sid, role := target } = some Lrecv →
      ∃ L', Consume e.role Lrecv (lookupD D sendEdge) = some L' ∧
            (Consume e.role L' [T]).isSome) →
    sendEdge = { sid := e.sid, sender := e.role, receiver := target } →
    DisjointG G G₂ →
    DConsistent G₂ D₂ →
    ∀ Lrecv, lookupG (G ++ G₂) { sid := e.sid, role := target } = some Lrecv →
      ∃ L', Consume e.role Lrecv (lookupD (D ++ D₂) sendEdge) = some L' ∧
            (Consume e.role L' [T]).isSome := by
  -- Lift readiness through append by showing D₂ has no entries for sendEdge.sid.
  intro hG hRecvReady hEdge hDisj hCons Lrecv hLookup
  have hSid : sendEdge.sid ∈ SessionsOf G := by simpa [hEdge] using ⟨e, .send target T L, hG, rfl⟩
  have hNot : sendEdge.sid ∉ SessionsOf G₂ := sid_not_in_right_of_left hDisj hSid
  have hNone : D₂.find? sendEdge = none := DEnv_find_none_of_notin_sessions hCons hNot
  have hTraceEq : lookupD (D ++ D₂) sendEdge = lookupD D sendEdge :=
    lookupD_append_left_of_right_none (D₁:=D) (D₂:=D₂) (e:=sendEdge) hNone
  have hLookupG : lookupG G { sid := e.sid, role := target } = some Lrecv := by
    cases lookupG_append_inv (G₁:=G) (G₂:=G₂) (e:=_) hLookup with
    | inl hLeft => exact hLeft
    | inr hRight =>
        have hNoneG : lookupG G₂ { sid := e.sid, role := target } = none :=
          lookupG_none_of_not_session (G:=G₂) (e:=_) hNot
        exact (Option.noConfusion (by simpa [hNoneG] using hRight.2)).elim
  obtain ⟨L', hConsume, hConsumeT⟩ := hRecvReady Lrecv hLookupG
  exact ⟨L', by simpa [hTraceEq] using hConsume, by simpa [hTraceEq] using hConsumeT⟩

private theorem ValidLabels_send_frame_left
    {G : GEnv} {D : DEnv} {G₂ : GEnv} {D₂ : DEnv} {bufs : Buffers}
    {e : Endpoint} {target : Role} {T : ValType} {L : LocalType} {v : Value}
    {sendEdge : Edge} :
    lookupG G e = some (.send target T L) →
    (∀ Lrecv, lookupG G { sid := e.sid, role := target } = some Lrecv →
      ∃ L', Consume e.role Lrecv (lookupD D { sid := e.sid, sender := e.role, receiver := target }) = some L' ∧
            (Consume e.role L' [T]).isSome) →
    sendEdge = { sid := e.sid, sender := e.role, receiver := target } →
    DisjointG G G₂ →
    DConsistent G₂ D₂ →
    Coherent (G ++ G₂) (D ++ D₂) →
    BuffersTyped (G ++ G₂) (D ++ D₂) bufs →
    ValidLabels (G ++ G₂) (D ++ D₂) bufs →
    ValidLabels (updateG G e L ++ G₂) (D ++ D₂) (enqueueBuf bufs sendEdge v) := by
  -- Lift receiver readiness to the appended env, then rewrite G.
  intro hG hRecvReady hEdge hDisj hCons hCoh hBT hValid
  have hRecvReady' := SendReady_append_left hG hRecvReady hEdge hDisj hCons
  have hG' : lookupG (G ++ G₂) e = some (.send target T L) :=
    lookupG_append_left (G₁:=G) (G₂:=G₂) hG
  have hValid' := ValidLabels_send_preserved (G:=G ++ G₂) (D:=D ++ D₂) (bufs:=bufs)
    (senderEp:=e) (receiverRole:=target) (T:=T) (L:=L) (v:=v)
    hValid hCoh hBT hG' hRecvReady'
  have hEq : ∀ ep, lookupG (updateG (G ++ G₂) e L) ep =
      lookupG (updateG G e L ++ G₂) ep := by
    intro ep
    exact lookupG_update_append_left (G₁:=G) (G₂:=G₂) (e:=e) (ep:=ep) (L:=L)
      (Lold:=.send target T L) hG
  exact ValidLabels_rewriteG hEq (by simpa [ValidLabels] using hValid')

private theorem SelectReady_append_left
    {G : GEnv} {D : DEnv} {G₂ : GEnv} {D₂ : DEnv}
    {e : Endpoint} {target : Role} {bs : List (String × LocalType)} {ℓ : String} {L : LocalType}
    {selectEdge : Edge} :
    lookupG G e = some (.select target bs) →
    (∀ Ltarget, lookupG G { sid := e.sid, role := target } = some Ltarget →
      ∃ L', Consume e.role Ltarget (lookupD D selectEdge) = some L' ∧
            (Consume e.role L' [.string]).isSome) →
    selectEdge = { sid := e.sid, sender := e.role, receiver := target } →
    DisjointG G G₂ →
    DConsistent G₂ D₂ →
    ∀ Ltarget, lookupG (G ++ G₂) { sid := e.sid, role := target } = some Ltarget →
      ∃ L', Consume e.role Ltarget (lookupD (D ++ D₂) selectEdge) = some L' ∧
            (Consume e.role L' [.string]).isSome := by
  -- Lift select readiness through append by hiding D₂'s traces.
  intro hG hTargetReady hEdge hDisj hCons Ltarget hLookup
  have hSid : selectEdge.sid ∈ SessionsOf G := by simpa [hEdge] using ⟨e, .select target bs, hG, rfl⟩
  have hNot : selectEdge.sid ∉ SessionsOf G₂ := sid_not_in_right_of_left hDisj hSid
  have hNone : D₂.find? selectEdge = none := DEnv_find_none_of_notin_sessions hCons hNot
  have hTraceEq : lookupD (D ++ D₂) selectEdge = lookupD D selectEdge :=
    lookupD_append_left_of_right_none (D₁:=D) (D₂:=D₂) (e:=selectEdge) hNone
  have hLookupG : lookupG G { sid := e.sid, role := target } = some Ltarget := by
    cases lookupG_append_inv (G₁:=G) (G₂:=G₂) (e:=_) hLookup with
    | inl hLeft => exact hLeft
    | inr hRight =>
        have hNoneG : lookupG G₂ { sid := e.sid, role := target } = none :=
          lookupG_none_of_not_session (G:=G₂) (e:=_) hNot
        exact (Option.noConfusion (by simpa [hNoneG] using hRight.2)).elim
  obtain ⟨L', hConsume, hConsumeS⟩ := hTargetReady Ltarget hLookupG
  exact ⟨L', by simpa [hTraceEq] using hConsume, by simpa [hTraceEq] using hConsumeS⟩

private theorem ValidLabels_select_frame_left
    {G : GEnv} {D : DEnv} {G₂ : GEnv} {D₂ : DEnv} {bufs : Buffers}
    {e : Endpoint} {target : Role} {bs : List (String × LocalType)} {ℓ : String}
    {L : LocalType} {selectEdge : Edge} :
    lookupG G e = some (.select target bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    (∀ Ltarget, lookupG G { sid := e.sid, role := target } = some Ltarget →
      ∃ L', Consume e.role Ltarget (lookupD D { sid := e.sid, sender := e.role, receiver := target }) = some L' ∧
            (Consume e.role L' [.string]).isSome) →
    selectEdge = { sid := e.sid, sender := e.role, receiver := target } →
    DisjointG G G₂ →
    DConsistent G₂ D₂ →
    Coherent (G ++ G₂) (D ++ D₂) →
    BuffersTyped (G ++ G₂) (D ++ D₂) bufs →
    ValidLabels (G ++ G₂) (D ++ D₂) bufs →
    ValidLabels (updateG G e L ++ G₂) (D ++ D₂) (enqueueBuf bufs selectEdge (.string ℓ)) := by
  -- Lift target readiness to the appended env, then rewrite G.
  intro hG hFind hTargetReady hEdge hDisj hCons hCoh hBT hValid
  have hTargetReady' := SelectReady_append_left hG hTargetReady hEdge hDisj hCons
  have hG' : lookupG (G ++ G₂) e = some (.select target bs) :=
    lookupG_append_left (G₁:=G) (G₂:=G₂) hG
  have hValid' := ValidLabels_select_preserved (G:=G ++ G₂) (D:=D ++ D₂) (bufs:=bufs)
    (selectorEp:=e) (targetRole:=target) (bs:=bs) (ℓ:=ℓ) (L:=L)
    hValid hCoh hBT hG' hFind hTargetReady'
  have hEq : ∀ ep, lookupG (updateG (G ++ G₂) e L) ep =
      lookupG (updateG G e L ++ G₂) ep := by
    intro ep
    exact lookupG_update_append_left (G₁:=G) (G₂:=G₂) (e:=e) (ep:=ep) (L:=L)
      (Lold:=.select target bs) hG
  exact ValidLabels_rewriteG hEq (by simpa [ValidLabels] using hValid')

private theorem ValidLabels_recv_frame_left
    {G : GEnv} {D : DEnv} {G₂ : GEnv} {D₂ : DEnv} {bufs : Buffers}
    {e : Endpoint} {source : Role} {T : ValType} {L : LocalType} {v : Value}
    {vs : List Value} {recvEdge : Edge} :
    lookupG G e = some (.recv source T L) →
    lookupBuf bufs recvEdge = v :: vs →
    HasTypeVal G v T →
    recvEdge = { sid := e.sid, sender := source, receiver := e.role } →
    DisjointG G G₂ →
    Coherent (G ++ G₂) (D ++ D₂) →
    BuffersTyped (G ++ G₂) (D ++ D₂) bufs →
    ValidLabels (G ++ G₂) (D ++ D₂) bufs →
    ValidLabels (updateG G e L ++ G₂) (D ++ D₂) (updateBuf bufs recvEdge vs) := by
  -- Use recv preservation on the appended env, then rewrite G.
  intro hG hBuf hv hEdge hDisj hCoh hBT hValid
  have hG' : lookupG (G ++ G₂) e = some (.recv source T L) :=
    lookupG_append_left (G₁:=G) (G₂:=G₂) hG
  have hv' : HasTypeVal (G ++ G₂) v T :=
    HasTypeVal_mono G (G ++ G₂) v T hv (by
      intro ep L' hLookup; exact lookupG_append_left (G₁:=G) (G₂:=G₂) hLookup)
  have hValid' := ValidLabels_recv_preserved (G:=G ++ G₂) (D:=D ++ D₂) (bufs:=bufs)
    (receiverEp:=e) (senderRole:=source) (T:=T) (L:=L) (v:=v) (vs:=vs)
    hValid hCoh hBT (by simpa [hEdge] using hBuf) hv' hG'
  have hEq : ∀ ep, lookupG (updateG (G ++ G₂) e L) ep =
      lookupG (updateG G e L ++ G₂) ep := by
    intro ep
    exact lookupG_update_append_left (G₁:=G) (G₂:=G₂) (e:=e) (ep:=ep) (L:=L)
      (Lold:=.recv source T L) hG
  exact ValidLabels_rewriteG hEq (by simpa [ValidLabels] using hValid')

private theorem ValidLabels_branch_frame_left
    {G : GEnv} {D : DEnv} {G₂ : GEnv} {D₂ : DEnv} {bufs : Buffers}
    {e : Endpoint} {source : Role} {bs : List (String × LocalType)} {ℓ : String}
    {L : LocalType} {vs : List Value} {branchEdge : Edge} :
    lookupG G e = some (.branch source bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    lookupBuf bufs branchEdge = .string ℓ :: vs →
    branchEdge = { sid := e.sid, sender := source, receiver := e.role } →
    DisjointG G G₂ →
    Coherent (G ++ G₂) (D ++ D₂) →
    BuffersTyped (G ++ G₂) (D ++ D₂) bufs →
    ValidLabels (G ++ G₂) (D ++ D₂) bufs →
    ValidLabels (updateG G e L ++ G₂) (D ++ D₂) (updateBuf bufs branchEdge vs) := by
  -- Use branch preservation on the appended env, then rewrite G.
  intro hG hFind hBuf hEdge hDisj hCoh hBT hValid
  have hG' : lookupG (G ++ G₂) e = some (.branch source bs) :=
    lookupG_append_left (G₁:=G) (G₂:=G₂) hG
  have hValid' := ValidLabels_branch_preserved (G:=G ++ G₂) (D:=D ++ D₂) (bufs:=bufs)
    (brancherEp:=e) (senderRole:=source) (branchOptions:=bs) (ℓ:=ℓ) (L:=L) (vs:=vs)
    hValid hCoh hBT hG' hFind (by simpa [hEdge] using hBuf)
  have hEq : ∀ ep, lookupG (updateG (G ++ G₂) e L) ep =
      lookupG (updateG G e L ++ G₂) ep := by
    intro ep
    exact lookupG_update_append_left (G₁:=G) (G₂:=G₂) (e:=e) (ep:=ep) (L:=L)
      (Lold:=.branch source bs) hG
  exact ValidLabels_rewriteG hEq (by simpa [ValidLabels] using hValid')

private theorem SendReady_append_right
    {G₁ : GEnv} {D₁ : DEnv} {G : GEnv} {D : DEnv}
    {e : Endpoint} {target : Role} {T : ValType} {L : LocalType} {sendEdge : Edge} :
    lookupG G e = some (.send target T L) →
    (∀ Lrecv, lookupG G { sid := e.sid, role := target } = some Lrecv →
      ∃ L', Consume e.role Lrecv (lookupD D sendEdge) = some L' ∧
            (Consume e.role L' [T]).isSome) →
    sendEdge = { sid := e.sid, sender := e.role, receiver := target } →
    DisjointG G₁ G →
    DConsistent G₁ D₁ →
    ∀ Lrecv, lookupG (G₁ ++ G) { sid := e.sid, role := target } = some Lrecv →
      ∃ L', Consume e.role Lrecv (lookupD (D₁ ++ D) sendEdge) = some L' ∧
            (Consume e.role L' [T]).isSome := by
  -- Lift readiness by routing lookups through the right and hiding D₁ traces.
  intro hG hRecvReady hEdge hDisj hCons Lrecv hLookup
  have hSid : sendEdge.sid ∈ SessionsOf G := by simpa [hEdge] using ⟨e, .send target T L, hG, rfl⟩
  have hNot : sendEdge.sid ∉ SessionsOf G₁ := sid_not_in_right_of_left (DisjointG_symm hDisj) hSid
  have hNone : D₁.find? sendEdge = none := DEnv_find_none_of_notin_sessions hCons hNot
  have hTraceEq : lookupD (D₁ ++ D) sendEdge = lookupD D sendEdge :=
    lookupD_append_right (D₁:=D₁) (D₂:=D) (e:=sendEdge) hNone
  have hLookupG : lookupG G { sid := e.sid, role := target } = some Lrecv := by
    cases lookupG_append_inv (G₁:=G₁) (G₂:=G) (e:=_) hLookup with
    | inl hLeft =>
        have hNoneG : lookupG G₁ { sid := e.sid, role := target } = none :=
          lookupG_none_of_not_session (G:=G₁) (e:=_) hNot
        exact (Option.noConfusion (by simpa [hNoneG] using hLeft)).elim
    | inr hRight => exact hRight.2
  obtain ⟨L', hConsume, hConsumeT⟩ := hRecvReady Lrecv hLookupG
  exact ⟨L', by simpa [hTraceEq] using hConsume, by simpa [hTraceEq] using hConsumeT⟩

private theorem ValidLabels_send_frame_right
    {G₁ : GEnv} {D₁ : DEnv} {G : GEnv} {D : DEnv} {bufs : Buffers}
    {e : Endpoint} {target : Role} {T : ValType} {L : LocalType} {v : Value}
    {sendEdge : Edge} :
    lookupG G e = some (.send target T L) →
    (∀ Lrecv, lookupG G { sid := e.sid, role := target } = some Lrecv →
      ∃ L', Consume e.role Lrecv (lookupD D { sid := e.sid, sender := e.role, receiver := target }) = some L' ∧
            (Consume e.role L' [T]).isSome) →
    sendEdge = { sid := e.sid, sender := e.role, receiver := target } →
    DisjointG G₁ G →
    DConsistent G₁ D₁ →
    Coherent (G₁ ++ G) (D₁ ++ D) →
    BuffersTyped (G₁ ++ G) (D₁ ++ D) bufs →
    ValidLabels (G₁ ++ G) (D₁ ++ D) bufs →
    ValidLabels (G₁ ++ updateG G e L) (D₁ ++ D) (enqueueBuf bufs sendEdge v) := by
  -- Lift receiver readiness to the appended env, then rewrite G on the right.
  intro hG hRecvReady hEdge hDisj hCons hCoh hBT hValid
  have hRecvReady' := SendReady_append_right hG hRecvReady hEdge hDisj hCons
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G) (G₂:=G₁) (DisjointG_symm hDisj) hG
  have hG' : lookupG (G₁ ++ G) e = some (.send target T L) := by
    simpa [lookupG_append_right (G₁:=G₁) (G₂:=G) (e:=e) hNone] using hG
  have hValid' := ValidLabels_send_preserved (G:=G₁ ++ G) (D:=D₁ ++ D) (bufs:=bufs)
    (senderEp:=e) (receiverRole:=target) (T:=T) (L:=L) (v:=v)
    hValid hCoh hBT hG' hRecvReady'
  have hEq : ∀ ep, lookupG (updateG (G₁ ++ G) e L) ep =
      lookupG (G₁ ++ updateG G e L) ep := by
    intro ep
    exact lookupG_update_append_right (G₁:=G₁) (G₂:=G) (e:=e) (ep:=ep) (L:=L) hNone
  exact ValidLabels_rewriteG hEq (by simpa [ValidLabels] using hValid')

private theorem ValidLabels_preserved_frame_left_send
    {G D G₂ D₂ bufs G' D' bufs'} {e : Endpoint} {target : Role} {T : ValType}
    {L : LocalType} {v : Value} {sendEdge : Edge} :
    lookupG G e = some (.send target T L) →
    (∀ Lrecv, lookupG G { sid := e.sid, role := target } = some Lrecv →
      ∃ L', Consume e.role Lrecv (lookupD D sendEdge) = some L' ∧
            (Consume e.role L' [T]).isSome) →
    sendEdge = { sid := e.sid, sender := e.role, receiver := target } →
    G' = updateG G e L →
    bufs' = enqueueBuf bufs sendEdge v →
    DisjointG G G₂ → DConsistent G₂ D₂ →
    Coherent (G ++ G₂) (D ++ D₂) →
    BuffersTyped (G ++ G₂) (D ++ D₂) bufs →
    ValidLabels (G ++ G₂) (D ++ D₂) bufs →
    ValidLabels (G' ++ G₂) (D' ++ D₂) bufs' := by
  -- Reuse send framing, then rewrite G and buffers.
  intro hG hReady hEdge hGout hBufsOut hDisj hCons hCoh hBT hValid
  simpa [hGout, hBufsOut, ValidLabels] using
    ValidLabels_send_frame_left (G:=G) (D:=D) (G₂:=G₂) (D₂:=D₂) (bufs:=bufs)
      (e:=_) (target:=_) (T:=_) (L:=_) (v:=_) (sendEdge:=_)
      hG hReady hEdge hDisj hCons hCoh hBT hValid

private theorem ValidLabels_preserved_frame_left_recv
    {G D G₂ D₂ bufs G' D' bufs'} {e : Endpoint} {source : Role} {T : ValType}
    {L : LocalType} {v : Value} {vs : List Value} {recvEdge : Edge} :
    lookupG G e = some (.recv source T L) →
    lookupBuf bufs recvEdge = v :: vs →
    HasTypeVal G v T →
    recvEdge = { sid := e.sid, sender := source, receiver := e.role } →
    G' = updateG G e L →
    bufs' = updateBuf bufs recvEdge vs →
    DisjointG G G₂ →
    Coherent (G ++ G₂) (D ++ D₂) →
    BuffersTyped (G ++ G₂) (D ++ D₂) bufs →
    ValidLabels (G ++ G₂) (D ++ D₂) bufs →
    ValidLabels (G' ++ G₂) (D' ++ D₂) bufs' := by
  -- Reuse recv framing, then rewrite G and buffers.
  intro hG hBuf hv hEdge hGout hBufsOut hDisj hCoh hBT hValid
  simpa [hGout, hBufsOut, ValidLabels] using
    ValidLabels_recv_frame_left (G:=G) (D:=D) (G₂:=G₂) (D₂:=D₂) (bufs:=bufs)
      (e:=_) (source:=_) (T:=_) (L:=_) (v:=_) (vs:=_) (recvEdge:=_)
      hG hBuf hv hEdge hDisj hCoh hBT hValid

private theorem ValidLabels_preserved_frame_left_select
    {G D G₂ D₂ bufs G' D' bufs'} {e : Endpoint} {target : Role}
    {bs : List (String × LocalType)} {ℓ : String} {L : LocalType} {selectEdge : Edge} :
    lookupG G e = some (.select target bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    (∀ Ltarget, lookupG G { sid := e.sid, role := target } = some Ltarget →
      ∃ L', Consume e.role Ltarget (lookupD D selectEdge) = some L' ∧
            (Consume e.role L' [.string]).isSome) →
    selectEdge = { sid := e.sid, sender := e.role, receiver := target } →
    G' = updateG G e L →
    bufs' = enqueueBuf bufs selectEdge (.string ℓ) →
    DisjointG G G₂ → DConsistent G₂ D₂ →
    Coherent (G ++ G₂) (D ++ D₂) →
    BuffersTyped (G ++ G₂) (D ++ D₂) bufs →
    ValidLabels (G ++ G₂) (D ++ D₂) bufs →
    ValidLabels (G' ++ G₂) (D' ++ D₂) bufs' := by
  -- Reuse select framing, then rewrite G and buffers.
  intro hG hFind hReady hEdge hGout hBufsOut hDisj hCons hCoh hBT hValid
  simpa [hGout, hBufsOut, ValidLabels] using
    ValidLabels_select_frame_left (G:=G) (D:=D) (G₂:=G₂) (D₂:=D₂) (bufs:=bufs)
      (e:=_) (target:=_) (bs:=_) (ℓ:=_) (L:=_) (selectEdge:=_)
      hG hFind hReady hEdge hDisj hCons hCoh hBT hValid

private theorem ValidLabels_preserved_frame_left_branch
    {G D G₂ D₂ bufs G' D' bufs'} {e : Endpoint} {source : Role}
    {bs : List (String × LocalType)} {ℓ : String} {L : LocalType} {vs : List Value}
    {branchEdge : Edge} :
    lookupG G e = some (.branch source bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    lookupBuf bufs branchEdge = .string ℓ :: vs →
    branchEdge = { sid := e.sid, sender := source, receiver := e.role } →
    G' = updateG G e L →
    bufs' = updateBuf bufs branchEdge vs →
    DisjointG G G₂ →
    Coherent (G ++ G₂) (D ++ D₂) →
    BuffersTyped (G ++ G₂) (D ++ D₂) bufs →
    ValidLabels (G ++ G₂) (D ++ D₂) bufs →
    ValidLabels (G' ++ G₂) (D' ++ D₂) bufs' := by
  -- Reuse branch framing, then rewrite G and buffers.
  intro hG hFind hBuf hEdge hGout hBufsOut hDisj hCoh hBT hValid
  simpa [hGout, hBufsOut, ValidLabels] using
    ValidLabels_branch_frame_left (G:=G) (D:=D) (G₂:=G₂) (D₂:=D₂) (bufs:=bufs)
      (e:=_) (source:=_) (bs:=_) (ℓ:=_) (L:=_) (vs:=_) (branchEdge:=_)
      hG hFind hBuf hEdge hDisj hCoh hBT hValid

private theorem SelectReady_append_right
    {G₁ : GEnv} {D₁ : DEnv} {G : GEnv} {D : DEnv}
    {e : Endpoint} {target : Role} {bs : List (String × LocalType)} {ℓ : String} {L : LocalType}
    {selectEdge : Edge} :
    lookupG G e = some (.select target bs) →
    (∀ Ltarget, lookupG G { sid := e.sid, role := target } = some Ltarget →
      ∃ L', Consume e.role Ltarget (lookupD D selectEdge) = some L' ∧
            (Consume e.role L' [.string]).isSome) →
    selectEdge = { sid := e.sid, sender := e.role, receiver := target } →
    DisjointG G₁ G →
    DConsistent G₁ D₁ →
    ∀ Ltarget, lookupG (G₁ ++ G) { sid := e.sid, role := target } = some Ltarget →
      ∃ L', Consume e.role Ltarget (lookupD (D₁ ++ D) selectEdge) = some L' ∧
            (Consume e.role L' [.string]).isSome := by
  -- Lift select readiness by routing lookups through the right.
  intro hG hTargetReady hEdge hDisj hCons Ltarget hLookup
  have hSid : selectEdge.sid ∈ SessionsOf G := by simpa [hEdge] using ⟨e, .select target bs, hG, rfl⟩
  have hNot : selectEdge.sid ∉ SessionsOf G₁ := sid_not_in_right_of_left (DisjointG_symm hDisj) hSid
  have hNone : D₁.find? selectEdge = none := DEnv_find_none_of_notin_sessions hCons hNot
  have hTraceEq : lookupD (D₁ ++ D) selectEdge = lookupD D selectEdge :=
    lookupD_append_right (D₁:=D₁) (D₂:=D) (e:=selectEdge) hNone
  have hLookupG : lookupG G { sid := e.sid, role := target } = some Ltarget := by
    cases lookupG_append_inv (G₁:=G₁) (G₂:=G) (e:=_) hLookup with
    | inl hLeft =>
        have hNoneG : lookupG G₁ { sid := e.sid, role := target } = none :=
          lookupG_none_of_not_session (G:=G₁) (e:=_) hNot
        exact (Option.noConfusion (by simpa [hNoneG] using hLeft)).elim
    | inr hRight => exact hRight.2
  obtain ⟨L', hConsume, hConsumeS⟩ := hTargetReady Ltarget hLookupG
  exact ⟨L', by simpa [hTraceEq] using hConsume, by simpa [hTraceEq] using hConsumeS⟩

private theorem ValidLabels_select_frame_right
    {G₁ : GEnv} {D₁ : DEnv} {G : GEnv} {D : DEnv} {bufs : Buffers}
    {e : Endpoint} {target : Role} {bs : List (String × LocalType)} {ℓ : String}
    {L : LocalType} {selectEdge : Edge} :
    lookupG G e = some (.select target bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    (∀ Ltarget, lookupG G { sid := e.sid, role := target } = some Ltarget →
      ∃ L', Consume e.role Ltarget (lookupD D { sid := e.sid, sender := e.role, receiver := target }) = some L' ∧
            (Consume e.role L' [.string]).isSome) →
    selectEdge = { sid := e.sid, sender := e.role, receiver := target } →
    DisjointG G₁ G →
    DConsistent G₁ D₁ →
    Coherent (G₁ ++ G) (D₁ ++ D) →
    BuffersTyped (G₁ ++ G) (D₁ ++ D) bufs →
    ValidLabels (G₁ ++ G) (D₁ ++ D) bufs →
    ValidLabels (G₁ ++ updateG G e L) (D₁ ++ D) (enqueueBuf bufs selectEdge (.string ℓ)) := by
  intro hG hFind hTargetReady hEdge hDisj hCons hCoh hBT hValid  -- lift readiness, then rewrite G
  have hTargetReady' := SelectReady_append_right hG hTargetReady hEdge hDisj hCons
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G) (G₂:=G₁) (DisjointG_symm hDisj) hG
  have hG' : lookupG (G₁ ++ G) e = some (.select target bs) := by
    simpa [lookupG_append_right (G₁:=G₁) (G₂:=G) (e:=e) hNone] using hG
  have hValid' := ValidLabels_select_preserved (G:=G₁ ++ G) (D:=D₁ ++ D) (bufs:=bufs)
    (selectorEp:=e) (targetRole:=target) (bs:=bs) (ℓ:=ℓ) (L:=L)
    hValid hCoh hBT hG' hFind hTargetReady'
  have hEq : ∀ ep, lookupG (updateG (G₁ ++ G) e L) ep =
      lookupG (G₁ ++ updateG G e L) ep := by
    intro ep
    exact lookupG_update_append_right (G₁:=G₁) (G₂:=G) (e:=e) (ep:=ep) (L:=L) hNone
  exact ValidLabels_rewriteG hEq (by simpa [ValidLabels] using hValid')

private theorem ValidLabels_recv_frame_right
    {G₁ : GEnv} {D₁ : DEnv} {G : GEnv} {D : DEnv} {bufs : Buffers}
    {e : Endpoint} {source : Role} {T : ValType} {L : LocalType} {v : Value}
    {vs : List Value} {recvEdge : Edge} :
    lookupG G e = some (.recv source T L) →
    lookupBuf bufs recvEdge = v :: vs →
    HasTypeVal G v T →
    recvEdge = { sid := e.sid, sender := source, receiver := e.role } →
    DisjointG G₁ G →
    Coherent (G₁ ++ G) (D₁ ++ D) →
    BuffersTyped (G₁ ++ G) (D₁ ++ D) bufs →
    ValidLabels (G₁ ++ G) (D₁ ++ D) bufs →
    ValidLabels (G₁ ++ updateG G e L) (D₁ ++ D) (updateBuf bufs recvEdge vs) := by
  intro hG hBuf hv hEdge hDisj hCoh hBT hValid  -- recv preservation on appended env
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G) (G₂:=G₁) (DisjointG_symm hDisj) hG
  have hG' : lookupG (G₁ ++ G) e = some (.recv source T L) := by
    simpa [lookupG_append_right (G₁:=G₁) (G₂:=G) (e:=e) hNone] using hG
  have hv' : HasTypeVal (G₁ ++ G) v T := HasTypeVal_append_right hDisj hv
  have hValid' := ValidLabels_recv_preserved (G:=G₁ ++ G) (D:=D₁ ++ D) (bufs:=bufs)
    (receiverEp:=e) (senderRole:=source) (T:=T) (L:=L) (v:=v) (vs:=vs)
    hValid hCoh hBT (by simpa [hEdge] using hBuf) hv' hG'
  have hEq : ∀ ep, lookupG (updateG (G₁ ++ G) e L) ep =
      lookupG (G₁ ++ updateG G e L) ep := by
    intro ep
    exact lookupG_update_append_right (G₁:=G₁) (G₂:=G) (e:=e) (ep:=ep) (L:=L) hNone
  exact ValidLabels_rewriteG hEq (by simpa [ValidLabels] using hValid')

private theorem ValidLabels_branch_frame_right
    {G₁ : GEnv} {D₁ : DEnv} {G : GEnv} {D : DEnv} {bufs : Buffers}
    {e : Endpoint} {source : Role} {bs : List (String × LocalType)} {ℓ : String}
    {L : LocalType} {vs : List Value} {branchEdge : Edge} :
    lookupG G e = some (.branch source bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    lookupBuf bufs branchEdge = .string ℓ :: vs →
    branchEdge = { sid := e.sid, sender := source, receiver := e.role } →
    DisjointG G₁ G →
    Coherent (G₁ ++ G) (D₁ ++ D) →
    BuffersTyped (G₁ ++ G) (D₁ ++ D) bufs →
    ValidLabels (G₁ ++ G) (D₁ ++ D) bufs →
    ValidLabels (G₁ ++ updateG G e L) (D₁ ++ D) (updateBuf bufs branchEdge vs) := by
  -- Use branch preservation on the appended env, then rewrite G on the right.
  intro hG hFind hBuf hEdge hDisj hCoh hBT hValid
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G) (G₂:=G₁) (DisjointG_symm hDisj) hG
  have hG' : lookupG (G₁ ++ G) e = some (.branch source bs) := by
    simpa [lookupG_append_right (G₁:=G₁) (G₂:=G) (e:=e) hNone] using hG
  have hValid' := ValidLabels_branch_preserved (G:=G₁ ++ G) (D:=D₁ ++ D) (bufs:=bufs)
    (brancherEp:=e) (senderRole:=source) (branchOptions:=bs) (ℓ:=ℓ) (L:=L) (vs:=vs)
    hValid hCoh hBT hG' hFind (by simpa [hEdge] using hBuf)
  have hEq : ∀ ep, lookupG (updateG (G₁ ++ G) e L) ep =
      lookupG (G₁ ++ updateG G e L) ep := by
    intro ep
    exact lookupG_update_append_right (G₁:=G₁) (G₂:=G) (e:=e) (ep:=ep) (L:=L) hNone
  exact ValidLabels_rewriteG hEq (by simpa [ValidLabels] using hValid')

private theorem ValidLabels_preserved_frame_left
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    ∀ {G₂ D₂}, DisjointG G G₂ → DConsistent G₂ D₂ →
      Coherent (G ++ G₂) (D ++ D₂) → BuffersTyped (G ++ G₂) (D ++ D₂) bufs →
      ValidLabels (G ++ G₂) (D ++ D₂) bufs →
      ValidLabels (G' ++ G₂) (D' ++ D₂) bufs' := by
  -- Induct on the step; buffer-changing cases use the frame lemmas.
  intro hTS; induction hTS generalizing G₂ D₂ with
  | send _ _ hG _ _ hReady hEdge hGout _ hBufsOut =>
      intro _ _ hDisj hCons hCoh hBT hValid; exact
        ValidLabels_preserved_frame_left_send hG hReady hEdge hGout hBufsOut
          hDisj hCons hCoh hBT hValid
  | recv _ hG hEdge hBuf hv _ hGout _ _ _ hBufsOut =>
      intro _ _ hDisj _ hCoh hBT hValid
      exact ValidLabels_preserved_frame_left_recv hG hBuf hv hEdge hGout hBufsOut
        hDisj hCoh hBT hValid
  | select _ hG hFind hReady hEdge hGout _ hBufsOut =>
      intro _ _ hDisj hCons hCoh hBT hValid
      exact ValidLabels_preserved_frame_left_select hG hFind hReady hEdge hGout hBufsOut
        hDisj hCons hCoh hBT hValid
  | branch _ hG hEdge hBuf _ hFind _ hGout _ hBufsOut =>
      intro _ _ hDisj _ hCoh hBT hValid
      exact ValidLabels_preserved_frame_left_branch hG hFind hBuf hEdge hGout hBufsOut
        hDisj hCoh hBT hValid
  | assign | seq_skip | par_skip_left | par_skip_right =>
      intro _ _ _ _ _ _ hValid; simpa [ValidLabels] using hValid
  | seq_step _ ih | par_left _ _ _ _ _ _ ih | par_right _ _ _ _ _ _ ih =>
      intro _ _ hDisj hCons hCoh hBT hValid
      exact ih hDisj hCons hCoh hBT hValid

private theorem ValidLabels_preserved_frame_right_send
    {G₁ D₁ G D bufs G' D' bufs'} {e : Endpoint} {target : Role} {T : ValType}
    {L : LocalType} {v : Value} {sendEdge : Edge} :
    lookupG G e = some (.send target T L) →
    (∀ Lrecv, lookupG G { sid := e.sid, role := target } = some Lrecv →
      ∃ L', Consume e.role Lrecv (lookupD D sendEdge) = some L' ∧
            (Consume e.role L' [T]).isSome) →
    sendEdge = { sid := e.sid, sender := e.role, receiver := target } →
    G' = updateG G e L →
    bufs' = enqueueBuf bufs sendEdge v →
    DisjointG G₁ G → DConsistent G₁ D₁ →
    Coherent (G₁ ++ G) (D₁ ++ D) →
    BuffersTyped (G₁ ++ G) (D₁ ++ D) bufs →
    ValidLabels (G₁ ++ G) (D₁ ++ D) bufs →
    ValidLabels (G₁ ++ G') (D₁ ++ D') bufs' := by
  -- Reuse right-send framing, then rewrite G and buffers.
  intro hG hReady hEdge hGout hBufsOut hDisj hCons hCoh hBT hValid
  simpa [hGout, hBufsOut, ValidLabels] using
    ValidLabels_send_frame_right (G₁:=G₁) (D₁:=D₁) (G:=G) (D:=D) (bufs:=bufs)
      (e:=_) (target:=_) (T:=_) (L:=_) (v:=_) (sendEdge:=_)
      hG hReady hEdge hDisj hCons hCoh hBT hValid

private theorem ValidLabels_preserved_frame_right_recv
    {G₁ D₁ G D bufs G' D' bufs'} {e : Endpoint} {source : Role} {T : ValType}
    {L : LocalType} {v : Value} {vs : List Value} {recvEdge : Edge} :
    lookupG G e = some (.recv source T L) →
    lookupBuf bufs recvEdge = v :: vs →
    HasTypeVal G v T →
    recvEdge = { sid := e.sid, sender := source, receiver := e.role } →
    G' = updateG G e L →
    bufs' = updateBuf bufs recvEdge vs →
    DisjointG G₁ G →
    Coherent (G₁ ++ G) (D₁ ++ D) →
    BuffersTyped (G₁ ++ G) (D₁ ++ D) bufs →
    ValidLabels (G₁ ++ G) (D₁ ++ D) bufs →
    ValidLabels (G₁ ++ G') (D₁ ++ D') bufs' := by
  -- Reuse right-recv framing, then rewrite G and buffers.
  intro hG hBuf hv hEdge hGout hBufsOut hDisj hCoh hBT hValid
  simpa [hGout, hBufsOut, ValidLabels] using
    ValidLabels_recv_frame_right (G₁:=G₁) (D₁:=D₁) (G:=G) (D:=D) (bufs:=bufs)
      (e:=_) (source:=_) (T:=_) (L:=_) (v:=_) (vs:=_) (recvEdge:=_)
      hG hBuf hv hEdge hDisj hCoh hBT hValid

private theorem ValidLabels_preserved_frame_right_select
    {G₁ D₁ G D bufs G' D' bufs'} {e : Endpoint} {target : Role}
    {bs : List (String × LocalType)} {ℓ : String} {L : LocalType} {selectEdge : Edge} :
    lookupG G e = some (.select target bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    (∀ Ltarget, lookupG G { sid := e.sid, role := target } = some Ltarget →
      ∃ L', Consume e.role Ltarget (lookupD D selectEdge) = some L' ∧
            (Consume e.role L' [.string]).isSome) →
    selectEdge = { sid := e.sid, sender := e.role, receiver := target } →
    G' = updateG G e L →
    bufs' = enqueueBuf bufs selectEdge (.string ℓ) →
    DisjointG G₁ G → DConsistent G₁ D₁ →
    Coherent (G₁ ++ G) (D₁ ++ D) →
    BuffersTyped (G₁ ++ G) (D₁ ++ D) bufs →
    ValidLabels (G₁ ++ G) (D₁ ++ D) bufs →
    ValidLabels (G₁ ++ G') (D₁ ++ D') bufs' := by
  -- Reuse right-select framing, then rewrite G and buffers.
  intro hG hFind hReady hEdge hGout hBufsOut hDisj hCons hCoh hBT hValid
  simpa [hGout, hBufsOut, ValidLabels] using
    ValidLabels_select_frame_right (G₁:=G₁) (D₁:=D₁) (G:=G) (D:=D) (bufs:=bufs)
      (e:=_) (target:=_) (bs:=_) (ℓ:=_) (L:=_) (selectEdge:=_)
      hG hFind hReady hEdge hDisj hCons hCoh hBT hValid

private theorem ValidLabels_preserved_frame_right_branch
    {G₁ D₁ G D bufs G' D' bufs'} {e : Endpoint} {source : Role}
    {bs : List (String × LocalType)} {ℓ : String} {L : LocalType} {vs : List Value}
    {branchEdge : Edge} :
    lookupG G e = some (.branch source bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    lookupBuf bufs branchEdge = .string ℓ :: vs →
    branchEdge = { sid := e.sid, sender := source, receiver := e.role } →
    G' = updateG G e L →
    bufs' = updateBuf bufs branchEdge vs →
    DisjointG G₁ G →
    Coherent (G₁ ++ G) (D₁ ++ D) →
    BuffersTyped (G₁ ++ G) (D₁ ++ D) bufs →
    ValidLabels (G₁ ++ G) (D₁ ++ D) bufs →
    ValidLabels (G₁ ++ G') (D₁ ++ D') bufs' := by
  -- Reuse right-branch framing, then rewrite G and buffers.
  intro hG hFind hBuf hEdge hGout hBufsOut hDisj hCoh hBT hValid
  simpa [hGout, hBufsOut, ValidLabels] using
    ValidLabels_branch_frame_right (G₁:=G₁) (D₁:=D₁) (G:=G) (D:=D) (bufs:=bufs)
      (e:=_) (source:=_) (bs:=_) (ℓ:=_) (L:=_) (vs:=_) (branchEdge:=_)
      hG hFind hBuf hEdge hDisj hCoh hBT hValid

private theorem ValidLabels_preserved_frame_right
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    ∀ {G₁ D₁}, DisjointG G₁ G → DConsistent G₁ D₁ →
      Coherent (G₁ ++ G) (D₁ ++ D) → BuffersTyped (G₁ ++ G) (D₁ ++ D) bufs →
      ValidLabels (G₁ ++ G) (D₁ ++ D) bufs →
      ValidLabels (G₁ ++ G') (D₁ ++ D') bufs' := by
  -- Symmetric framing when the step sits on the right of append.
  intro hTS; induction hTS generalizing G₁ D₁ with
  | send _ _ hG _ _ hReady hEdge hGout _ hBufsOut =>
      intro _ _ hDisj hCons hCoh hBT hValid
      exact ValidLabels_preserved_frame_right_send hG hReady hEdge hGout hBufsOut
        hDisj hCons hCoh hBT hValid
  | recv _ hG hEdge hBuf hv _ hGout _ _ _ hBufsOut =>
      intro _ _ hDisj _ hCoh hBT hValid
      exact ValidLabels_preserved_frame_right_recv hG hBuf hv hEdge hGout hBufsOut
        hDisj hCoh hBT hValid
  | select _ hG hFind hReady hEdge hGout _ hBufsOut =>
      intro _ _ hDisj hCons hCoh hBT hValid
      exact ValidLabels_preserved_frame_right_select hG hFind hReady hEdge hGout hBufsOut
        hDisj hCons hCoh hBT hValid
  | branch _ hG hEdge hBuf _ hFind _ hGout _ hBufsOut =>
      intro _ _ hDisj _ hCoh hBT hValid
      exact ValidLabels_preserved_frame_right_branch hG hFind hBuf hEdge hGout hBufsOut
        hDisj hCoh hBT hValid
  | assign | seq_skip | par_skip_left | par_skip_right =>
      intro _ _ _ _ _ _ hValid; simpa [ValidLabels] using hValid
  | seq_step _ ih | par_left _ _ _ _ _ _ ih | par_right _ _ _ _ _ _ ih =>
      intro _ _ hDisj hCons hCoh hBT hValid
      exact ih hDisj hCons hCoh hBT hValid

private theorem ValidLabels_preserved_send
    {G D bufs G' D' bufs'} {e : Endpoint} {target : Role} {T : ValType} {L : LocalType}
    {v : Value} {sendEdge : Edge} :
    lookupG G e = some (.send target T L) →
    (∀ Lrecv, lookupG G { sid := e.sid, role := target } = some Lrecv →
      ∃ L', Consume e.role Lrecv (lookupD D { sid := e.sid, sender := e.role, receiver := target }) = some L' ∧
            (Consume e.role L' [T]).isSome) →
    sendEdge = { sid := e.sid, sender := e.role, receiver := target } →
    G' = updateG G e L →
    bufs' = enqueueBuf bufs sendEdge v →
    Coherent G D →
    BuffersTyped G D bufs →
    ValidLabels G D bufs →
    ValidLabels G' D' bufs' := by
  -- Reuse send preservation, then rewrite G and buffers.
  intro hG hReady hEdge hGout hBufsOut hCoh hBT hValid
  simpa [hGout, hBufsOut, hEdge, enqueueBuf] using
    ValidLabels_send_preserved (G:=G) (D:=D) (bufs:=bufs)
      (senderEp:=e) (receiverRole:=target) (T:=T) (L:=L) (v:=v)
      hValid hCoh hBT hG hReady

private theorem ValidLabels_preserved_recv
    {G D bufs G' D' bufs'} {e : Endpoint} {source : Role} {T : ValType} {L : LocalType}
    {v : Value} {vs : List Value} {recvEdge : Edge} :
    lookupG G e = some (.recv source T L) →
    recvEdge = { sid := e.sid, sender := source, receiver := e.role } →
    lookupBuf bufs recvEdge = v :: vs →
    HasTypeVal G v T →
    G' = updateG G e L →
    bufs' = updateBuf bufs recvEdge vs →
    Coherent G D →
    BuffersTyped G D bufs →
    ValidLabels G D bufs →
    ValidLabels G' D' bufs' := by
  -- Reuse recv preservation, then rewrite G and buffers.
  intro hG hEdge hBuf hv hGout hBufsOut hCoh hBT hValid
  simpa [hGout, hBufsOut, hEdge] using
    ValidLabels_recv_preserved (G:=G) (D:=D) (bufs:=bufs)
      (receiverEp:=e) (senderRole:=source) (T:=T) (L:=L) (v:=v) (vs:=vs)
      hValid hCoh hBT hBuf hv hG

private theorem ValidLabels_preserved_select
    {G D bufs G' D' bufs'} {e : Endpoint} {target : Role}
    {bs : List (String × LocalType)} {ℓ : String} {L : LocalType} {selectEdge : Edge} :
    lookupG G e = some (.select target bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    (∀ Ltarget, lookupG G { sid := e.sid, role := target } = some Ltarget →
      ∃ L', Consume e.role Ltarget (lookupD D { sid := e.sid, sender := e.role, receiver := target }) = some L' ∧
            (Consume e.role L' [.string]).isSome) →
    selectEdge = { sid := e.sid, sender := e.role, receiver := target } →
    G' = updateG G e L →
    bufs' = enqueueBuf bufs selectEdge (.string ℓ) →
    Coherent G D →
    BuffersTyped G D bufs →
    ValidLabels G D bufs →
    ValidLabels G' D' bufs' := by
  -- Reuse select preservation, then rewrite G and buffers.
  intro hG hFind hReady hEdge hGout hBufsOut hCoh hBT hValid
  simpa [hGout, hBufsOut, hEdge, enqueueBuf] using
    ValidLabels_select_preserved (G:=G) (D:=D) (bufs:=bufs)
      (selectorEp:=e) (targetRole:=target) (bs:=bs) (ℓ:=ℓ) (L:=L)
      hValid hCoh hBT hG hFind hReady

private theorem ValidLabels_preserved_branch
    {G D bufs G' D' bufs'} {e : Endpoint} {source : Role}
    {bs : List (String × LocalType)} {ℓ : String} {L : LocalType} {vs : List Value}
    {branchEdge : Edge} :
    lookupG G e = some (.branch source bs) →
    branchEdge = { sid := e.sid, sender := source, receiver := e.role } →
    lookupBuf bufs branchEdge = .string ℓ :: vs →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    G' = updateG G e L →
    bufs' = updateBuf bufs branchEdge vs →
    Coherent G D →
    BuffersTyped G D bufs →
    ValidLabels G D bufs →
    ValidLabels G' D' bufs' := by
  -- Reuse branch preservation, then rewrite G and buffers.
  intro hG hEdge hBuf hFind hGout hBufsOut hCoh hBT hValid
  simpa [hGout, hBufsOut, hEdge] using
    ValidLabels_branch_preserved (G:=G) (D:=D) (bufs:=bufs)
      (brancherEp:=e) (senderRole:=source) (branchOptions:=bs) (ℓ:=ℓ) (L:=L) (vs:=vs)
      hValid hCoh hBT hG hFind hBuf

/-- ValidLabels is preserved by TypedStep. -/
theorem ValidLabels_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    Coherent G D →
    BuffersTyped G D bufs →
    ValidLabels G D bufs →
    ValidLabels G' D' bufs' := by
  -- Induct on the step; par cases use framed preservation.
  intro hTS hCoh hBT hValid
  induction hTS with
  | send _ _ hG _ _ hReady hEdge hGout _ hBufsOut =>
      exact ValidLabels_preserved_send hG hReady hEdge hGout hBufsOut hCoh hBT hValid
  | recv _ hG hEdge hBuf hv _ hGout _ _ _ hBufsOut =>
      exact ValidLabels_preserved_recv hG hEdge hBuf hv hGout hBufsOut hCoh hBT hValid
  | select _ hG hFind hReady hEdge hGout _ hBufsOut =>
      exact ValidLabels_preserved_select hG hFind hReady hEdge hGout hBufsOut hCoh hBT hValid
  | branch _ hG hEdge hBuf _ hFind _ hGout _ hBufsOut =>
      exact ValidLabels_preserved_branch hG hEdge hBuf hFind hGout hBufsOut hCoh hBT hValid
  | assign | seq_skip | par_skip_left | par_skip_right =>
      simpa [ValidLabels] using hValid
  | seq_step _ ih =>
      exact ih hCoh hBT hValid
  | par_left _ hTS hDisjG _ _ _ hConsR _ =>
      exact ValidLabels_preserved_frame_left hTS hDisjG hConsR hCoh hBT hValid
  | par_right _ hTS hDisjG _ _ hConsL _ _ =>
      exact ValidLabels_preserved_frame_right hTS hDisjG hConsL hCoh hBT hValid

/-- No step introduces a new send endpoint in the updated local type. -/
def NoNewSendStep
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' → Prop
  | .send _ _ _ _ _ _ _ _ _ _ _ => ∀ q T L', L ≠ .send q T L' -- updated L is not send
  | .recv _ _ _ _ _ _ _ _ _ _ _ _ => ∀ q T L', L ≠ .send q T L' -- updated L is not send
  | .select _ _ _ _ _ _ _ _ _ _ _ => ∀ q T L', L ≠ .send q T L' -- updated L is not send
  | .branch _ _ _ _ _ _ _ _ _ _ _ _ _ => ∀ q T L', L ≠ .send q T L' -- updated L is not send
  | .assign => True
  | .seq_step h => NoNewSendStep h
  | .seq_skip => True
  | .par_left _ h _ _ _ _ _ => NoNewSendStep h
  | .par_right _ h _ _ _ _ _ => NoNewSendStep h
  | .par_skip_left => True
  | .par_skip_right => True

/-- No step introduces a new select endpoint in the updated local type. -/
def NoNewSelectStep
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' → Prop
  | .send _ _ _ _ _ _ _ _ _ _ _ => ∀ q bs, L ≠ .select q bs -- updated L is not select
  | .recv _ _ _ _ _ _ _ _ _ _ _ _ => ∀ q bs, L ≠ .select q bs -- updated L is not select
  | .select _ _ _ _ _ _ _ _ _ _ _ => ∀ q bs, L ≠ .select q bs -- updated L is not select
  | .branch _ _ _ _ _ _ _ _ _ _ _ _ _ => ∀ q bs, L ≠ .select q bs -- updated L is not select
  | .assign => True
  | .seq_step h => NoNewSelectStep h
  | .seq_skip => True
  | .par_left _ h _ _ _ _ _ => NoNewSelectStep h
  | .par_right _ h _ _ _ _ _ => NoNewSelectStep h
  | .par_skip_left => True
  | .par_skip_right => True

private theorem lookupG_update_send_inv
    {G : GEnv} {e ep : Endpoint} {L : LocalType} {q : Role} {T : ValType} {L' : LocalType}
    (hNo : ∀ q T L', L ≠ .send q T L') :
    lookupG (updateG G e L) ep = some (.send q T L') →
    lookupG G ep = some (.send q T L') := by
  -- Updated endpoint cannot be send; other endpoints use lookupG_update_neq.
  intro hLookup
  by_cases hEq : ep = e
  · subst hEq
    have hSend : L = .send q T L' := by simpa [lookupG_update_eq] using hLookup
    exact (hNo q T L' hSend).elim
  · simpa [lookupG_update_neq _ _ _ _ hEq] using hLookup

private theorem lookupG_update_select_inv
    {G : GEnv} {e ep : Endpoint} {L : LocalType} {q : Role} {bs : List (String × LocalType)}
    (hNo : ∀ q bs, L ≠ .select q bs) :
    lookupG (updateG G e L) ep = some (.select q bs) →
    lookupG G ep = some (.select q bs) := by
  -- Updated endpoint cannot be select; other endpoints use lookupG_update_neq.
  intro hLookup
  by_cases hEq : ep = e
  · subst hEq
    have hSel : L = .select q bs := by simpa [lookupG_update_eq] using hLookup
    exact (hNo q bs hSel).elim
  · simpa [lookupG_update_neq _ _ _ _ hEq] using hLookup

private theorem senderEp_of_edge_eq
    {e senderEp : Endpoint} {q target : Role} :
    { sid := e.sid, sender := e.role, receiver := q } =
      { sid := senderEp.sid, sender := senderEp.role, receiver := target } →
    e = senderEp := by
  -- Edge equality fixes both sid and sender role, hence endpoints coincide.
  cases e; cases senderEp; intro hEq; cases hEq; rfl

private theorem trace_cons_of_head {T : ValType} {ts : List ValType} :
    (ts.head? = some T) → ∃ tail, ts = T :: tail := by
  -- Nonempty list with head? = T has form T :: tail.
  intro hHead
  cases ts with
  | nil => cases hHead
  | cons t tail =>
      cases hHead
      exact ⟨tail, rfl⟩

private theorem Consume_recv_tail_of_head
    {from_ source : Role} {T : ValType} {L : LocalType} {ts : List ValType} {L' : LocalType}
    (hConsume : Consume from_ (.recv source T L) (T :: ts) = some L') :
    from_ = source ∧ Consume from_ L ts = some L' := by
  -- Consume on a recv head succeeds only if sender matches; then it reduces to the tail.
  by_cases hEq : from_ == source
  · have hEq' : from_ = source := eq_of_beq hEq
    subst hEq'
    simpa [Consume_recv_cons] using hConsume
  · simp [Consume, consumeOne, hEq] at hConsume

private theorem recv_sender_of_ready
    {from_ source : Role} {T T' : ValType} {L : LocalType} {ts : List ValType} {L1 : LocalType} :
    Consume from_ (.recv source T L) ts = some L1 →
    (Consume from_ L1 [T']).isSome →
    from_ = source := by
  -- Consuming from a recv and then one more message forces sender match.
  intro hConsume hNext
  cases ts with
  | nil =>
      have hL1 : L1 = .recv source T L := by simpa [Consume] using hConsume
      subst hL1
      by_cases hEq : from_ == source
      · exact eq_of_beq hEq
      · have : False := by simpa [Consume, consumeOne, hEq] using hNext
        exact this.elim
  | cons t ts =>
      by_cases hEq : from_ == source
      · exact eq_of_beq hEq
      · have : Consume from_ (.recv source T L) (t :: ts) = none := by
          simp [Consume, consumeOne, hEq]
        cases this ▸ hConsume

private theorem lookupD_append_neq
    {D : DEnv} {edge e : Edge} {T : ValType} :
    e ≠ edge →
    lookupD (appendD D edge T) e = lookupD D e := by
  -- Append only affects the specified edge.
  intro hNe
  have hTraceEq := lookupD_update_neq (env:=D) (e:=edge) (e':=e)
    (ts:=lookupD D edge ++ [T]) hNe
  simpa [appendD] using hTraceEq

private theorem send_ready_no_send_receiver
    {G : GEnv} {D : DEnv} {e : Endpoint} {q target : Role} {T T' : ValType}
    {L : LocalType} {L' : LocalType} :
    SendReady G D →
    lookupG G e = some (.send q T L) →
    lookupG G { sid := e.sid, role := q } = some (.send target T' L') →
    False := by
  -- Send local types cannot consume any buffered value.
  intro hReady hG hRecv
  obtain ⟨L1, hConsume, hConsumeT⟩ := hReady e q T L hG _ hRecv
  cases hTrace : lookupD D { sid := e.sid, sender := e.role, receiver := q } with
  | nil =>
      have hL1 : L1 = .send target T' L' := by simpa [hTrace, Consume] using hConsume
      simpa [hL1, Consume, consumeOne] using hConsumeT
  | cons t ts =>
      have : (none : Option LocalType) = some L1 := by
        simpa [hTrace, Consume, consumeOne] using hConsume
      cases this

private theorem send_ready_no_select_receiver
    {G : GEnv} {D : DEnv} {e : Endpoint} {q target : Role} {T : ValType}
    {L : LocalType} {bs : List (String × LocalType)} :
    SendReady G D →
    lookupG G e = some (.send q T L) →
    lookupG G { sid := e.sid, role := q } = some (.select target bs) →
    False := by
  -- Select local types cannot consume a value.
  intro hReady hG hRecv
  obtain ⟨L1, hConsume, hConsumeT⟩ := hReady e q T L hG _ hRecv
  cases hTrace : lookupD D { sid := e.sid, sender := e.role, receiver := q } with
  | nil =>
      have hL1 : L1 = .select target bs := by simpa [hTrace, Consume] using hConsume
      simpa [hL1, Consume, consumeOne] using hConsumeT
  | cons t ts =>
      have : (none : Option LocalType) = some L1 := by
        simpa [hTrace, Consume, consumeOne] using hConsume
      cases this

private theorem select_ready_no_send_receiver
    {G : GEnv} {D : DEnv} {e : Endpoint} {q target : Role} {bs : List (String × LocalType)}
    {ℓ : String} {L : LocalType} {T : ValType} {L' : LocalType} :
    SelectReady G D →
    lookupG G e = some (.select q bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    lookupG G { sid := e.sid, role := q } = some (.send target T L') →
    False := by
  -- Send local types cannot consume a label.
  intro hReady hG hFind hRecv
  obtain ⟨L1, hConsume, hConsumeS⟩ := hReady e q bs ℓ L hG hFind _ hRecv
  cases hTrace : lookupD D { sid := e.sid, sender := e.role, receiver := q } with
  | nil =>
      have hL1 : L1 = .send target T L' := by simpa [hTrace, Consume] using hConsume
      simpa [hL1, Consume, consumeOne] using hConsumeS
  | cons t ts =>
      have : (none : Option LocalType) = some L1 := by
        simpa [hTrace, Consume, consumeOne] using hConsume
      cases this

private theorem select_ready_no_select_receiver
    {G : GEnv} {D : DEnv} {e : Endpoint} {q target : Role} {bs bs' : List (String × LocalType)}
    {ℓ : String} {L : LocalType} :
    SelectReady G D →
    lookupG G e = some (.select q bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    lookupG G { sid := e.sid, role := q } = some (.select target bs') →
    False := by
  -- Select local types cannot consume a label.
  intro hReady hG hFind hRecv
  obtain ⟨L1, hConsume, hConsumeS⟩ := hReady e q bs ℓ L hG hFind _ hRecv
  cases hTrace : lookupD D { sid := e.sid, sender := e.role, receiver := q } with
  | nil =>
      have hL1 : L1 = .select target bs' := by simpa [hTrace, Consume] using hConsume
      simpa [hL1, Consume, consumeOne] using hConsumeS
  | cons t ts =>
      have : (none : Option LocalType) = some L1 := by
        simpa [hTrace, Consume, consumeOne] using hConsume
      cases this

private theorem select_ready_no_branch_receiver
    {G : GEnv} {D : DEnv} {e : Endpoint} {q source : Role} {bs : List (String × LocalType)}
    {ℓ : String} {L : LocalType} {bs' : List (String × LocalType)} :
    SelectReady G D →
    lookupG G e = some (.select q bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    lookupG G { sid := e.sid, role := q } = some (.branch source bs') →
    False := by
  -- Branch local types cannot consume a label via Consume.
  intro hReady hG hFind hRecv
  obtain ⟨L1, hConsume, hConsumeS⟩ := hReady e q bs ℓ L hG hFind _ hRecv
  cases hTrace : lookupD D { sid := e.sid, sender := e.role, receiver := q } with
  | nil =>
      have hL1 : L1 = .branch source bs' := by simpa [hTrace, Consume] using hConsume
      simpa [hL1, Consume, consumeOne] using hConsumeS
  | cons t ts =>
      exact (Consume_branch_nonempty_false (by simpa [hTrace] using hConsume)).elim

private theorem SendReady_left_of_append
    {G G₂ : GEnv} {D₁ : DEnv} {D₂' : DEnv} :
    DisjointG G G₂ → DConsistent G₂ D₂' →
    SendReady (G ++ G₂) (D₁ ++ D₂') → SendReady G D₁ := by
  -- Restrict readiness to the left by rewriting lookupD with disjointness.
  intro hDisj hCons hReady e q T L hG Lrecv hGrecv
  have hG' : lookupG (G ++ G₂) e = some (.send q T L) := lookupG_append_left hG
  have hGrecv' : lookupG (G ++ G₂) { sid := e.sid, role := q } = some Lrecv :=
    lookupG_append_left hGrecv
  obtain ⟨L', hConsume, hConsumeT⟩ := hReady e q T L hG' Lrecv hGrecv'
  have hSid : e.sid ∈ SessionsOf G := ⟨e, .send q T L, hG, rfl⟩
  have hNot : e.sid ∉ SessionsOf G₂ := sid_not_in_right_of_left hDisj hSid
  have hNone : D₂'.find? { sid := e.sid, sender := e.role, receiver := q } = none :=
    DEnv_find_none_of_notin_sessions hCons hNot
  have hTraceEq : lookupD (D₁ ++ D₂') { sid := e.sid, sender := e.role, receiver := q } =
      lookupD D₁ { sid := e.sid, sender := e.role, receiver := q } :=
    lookupD_append_left_of_right_none (D₁:=D₁) (D₂:=D₂') (e:=_) hNone
  exact ⟨L', by simpa [hTraceEq] using hConsume, by simpa [hTraceEq] using hConsumeT⟩

private theorem SendReady_right_of_append
    {G₁ G : GEnv} {D₁ : DEnv} {D₂ : DEnv} :
    DisjointG G₁ G → DConsistent G₁ D₁ →
    SendReady (G₁ ++ G) (D₁ ++ D₂) → SendReady G D₂ := by
  -- Restrict readiness to the right by rewriting lookupD with disjointness.
  intro hDisj hCons hReady e q T L hG Lrecv hGrecv
  have hG' : lookupG (G₁ ++ G) e = some (.send q T L) := by
    have hNone : lookupG G₁ e = none :=
      DisjointG_lookup_left (G₁:=G) (G₂:=G₁) (DisjointG_symm hDisj) hG
    simpa [lookupG_append_right (G₁:=G₁) (G₂:=G) (e:=e) hNone] using hG
  have hGrecv' : lookupG (G₁ ++ G) { sid := e.sid, role := q } = some Lrecv := by
    have hNone : lookupG G₁ { sid := e.sid, role := q } = none :=
      DisjointG_lookup_left (G₁:=G) (G₂:=G₁) (DisjointG_symm hDisj) hGrecv
    simpa [lookupG_append_right (G₁:=G₁) (G₂:=G) (e:=_) hNone] using hGrecv
  obtain ⟨L', hConsume, hConsumeT⟩ := hReady e q T L hG' Lrecv hGrecv'
  have hSid : e.sid ∈ SessionsOf G := ⟨e, .send q T L, hG, rfl⟩
  have hNot : e.sid ∉ SessionsOf G₁ := sid_not_in_right_of_left (DisjointG_symm hDisj) hSid
  have hNone : D₁.find? { sid := e.sid, sender := e.role, receiver := q } = none :=
    DEnv_find_none_of_notin_sessions hCons hNot
  have hTraceEq : lookupD (D₁ ++ D₂) { sid := e.sid, sender := e.role, receiver := q } =
      lookupD D₂ { sid := e.sid, sender := e.role, receiver := q } :=
    lookupD_append_right (D₁:=D₁) (D₂:=D₂) (e:=_) hNone
  exact ⟨L', by simpa [hTraceEq] using hConsume, by simpa [hTraceEq] using hConsumeT⟩

private theorem SendReady_append_left_total
    {G : GEnv} {D : DEnv} {G₂ : GEnv} {D₂ : DEnv} :
    DisjointG G G₂ → DConsistent G₂ D₂ →
    SendReady G D → SendReady (G ++ G₂) (D ++ D₂) := by
  -- Lift readiness to the append using SendReady_append_left.
  intro hDisj hCons hReady e q T L hG Lrecv hGrecv
  have hRecvReady := hReady e q T L hG
  have hEdge : { sid := e.sid, sender := e.role, receiver := q } =
      { sid := e.sid, sender := e.role, receiver := q } := rfl
  exact SendReady_append_left hG hRecvReady hEdge hDisj hCons Lrecv hGrecv

private theorem SendReady_append_right_total
    {G₁ : GEnv} {D₁ : DEnv} {G : GEnv} {D : DEnv} :
    DisjointG G₁ G → DConsistent G₁ D₁ →
    SendReady G D → SendReady (G₁ ++ G) (D₁ ++ D) := by
  -- Lift readiness to the append using SendReady_append_right.
  intro hDisj hCons hReady e q T L hG Lrecv hGrecv
  have hRecvReady := hReady e q T L hG
  have hEdge : { sid := e.sid, sender := e.role, receiver := q } =
      { sid := e.sid, sender := e.role, receiver := q } := rfl
  exact SendReady_append_right hG hRecvReady hEdge hDisj hCons Lrecv hGrecv

/-- Send readiness is preserved by TypedStep (no new send continuations). -/
private theorem send_ready_no_branch_receiver
    {G : GEnv} {D : DEnv} {e : Endpoint} {q : Role} {T : ValType} {L : LocalType}
    {source : Role} {bs : List (String × LocalType)} :
    SendReady G D →
    lookupG G e = some (.send q T L) →
    lookupG G { sid := e.sid, role := q } = some (.branch source bs) →
    False := by
  -- Branch receiver cannot satisfy the Consume/[T] readiness condition.
  intro hReady hG hBranch
  obtain ⟨L', hConsume, hConsumeT⟩ := hReady e q T L hG _ hBranch
  cases hTrace : lookupD D { sid := e.sid, sender := e.role, receiver := q } with
  | nil =>
      have hL' : L' = .branch source bs := by simpa [hTrace, Consume] using hConsume
      simpa [hL', Consume, consumeOne] using hConsumeT
  | cons t ts =>
      exact (Consume_branch_nonempty_false (by simpa [hTrace] using hConsume)).elim

private theorem SendReady_preserved_send
    {G : GEnv} {D : DEnv} {senderEp : Endpoint} {target : Role} {T : ValType} {L : LocalType}
    {sendEdge : Edge} {G' : GEnv} {D' : DEnv} :
    lookupG G senderEp = some (.send target T L) →
    sendEdge = { sid := senderEp.sid, sender := senderEp.role, receiver := target } →
    G' = updateG G senderEp L → D' = appendD D sendEdge T →
    (∀ q T L', L ≠ .send q T L') → SendReady G D → SendReady G' D' := by
  -- Updated endpoint is not send; append only affects the updated edge.
  intro hG hEdge hGout hDout hNo hReady e q T' L' hGe Lrecv hGrecv
  have hGe' := lookupG_update_send_inv (e:=senderEp) (ep:=e) hNo (by simpa [hGout] using hGe)
  have hNe : e ≠ senderEp := by
    intro hEq; subst hEq
    have hSend : L = .send q T' L' := by simpa [hGout, lookupG_update_eq] using hGe
    exact (hNo q T' L' hSend).elim
  let recvEp : Endpoint := { sid := e.sid, role := q }
  have hRecvNe : recvEp ≠ senderEp := by
    intro hEq; subst hEq
    exact (send_ready_no_send_receiver hReady hGe' hG).elim
  have hRecv : lookupG G recvEp = some Lrecv := by
    simpa [hGout, lookupG_update_neq _ _ _ _ hRecvNe] using hGrecv
  obtain ⟨L1, hConsume, hConsumeT⟩ := hReady e q T' L' hGe' Lrecv hRecv
  have hEdgeNe : { sid := e.sid, sender := e.role, receiver := q } ≠ sendEdge := by
    intro hEq
    exact hNe (senderEp_of_edge_eq (q:=q) (target:=target) (by simpa [hEdge] using hEq))
  have hTraceEq :
      lookupD D' { sid := e.sid, sender := e.role, receiver := q } =
        lookupD D { sid := e.sid, sender := e.role, receiver := q } := by
    simpa [hDout] using lookupD_append_neq (D:=D) (edge:=sendEdge) (e:=_) (T:=T) hEdgeNe
  exact ⟨L1, by simpa [hTraceEq] using hConsume, by simpa [hTraceEq] using hConsumeT⟩

private theorem SendReady_preserved_recv_eq
    {G : GEnv} {D : DEnv} {receiverEp : Endpoint} {source : Role} {T : ValType}
    {L : LocalType} {recvEdge : Edge} {G' : GEnv} {D' : DEnv}
    {e : Endpoint} {q : Role} {T' : ValType} {L' : LocalType} {Lrecv : LocalType} :
    lookupG G receiverEp = some (.recv source T L) → recvEdge = { sid := receiverEp.sid, sender := source, receiver := receiverEp.role } →
    (lookupD D recvEdge).head? = some T →
    G' = updateG G receiverEp L → D' = updateD D recvEdge (lookupD D recvEdge).tail →
    SendReady G D → lookupG G e = some (.send q T' L') →
    { sid := e.sid, role := q } = receiverEp → lookupG G' { sid := e.sid, role := q } = some Lrecv →
    ∃ L1, Consume e.role Lrecv (lookupD D' { sid := e.sid, sender := e.role, receiver := q }) = some L1 ∧
      (Consume e.role L1 [T']).isSome := by
  -- If the receiver is updated, consume the head and reuse the tail.
  intro hG hEdge hTrace hGout hDout hReady hGe hRecvEq hGrecv
  subst hRecvEq
  have hLrecv : Lrecv = L := by simpa [hGout, lookupG_update_eq] using hGrecv
  subst hLrecv
  obtain ⟨L1, hConsume, hConsumeT⟩ := hReady e q T' L' hGe _ hG
  have hEqSender : e.role = source :=
    recv_sender_of_ready (from_:=e.role) (source:=source) (T:=T) (T':=T') (L:=L)
      (ts:=lookupD D { sid := e.sid, sender := e.role, receiver := q }) (L1:=L1) hConsume hConsumeT
  obtain ⟨tail, hTraceEq⟩ := trace_cons_of_head (by simpa [hEdge] using hTrace)
  have hEdgeEq : { sid := e.sid, sender := e.role, receiver := q } = recvEdge := by
    cases hEqSender; simpa [hEdge] using rfl
  have hTail : Consume e.role L (tail) = some L1 := by
    exact (Consume_recv_tail_of_head (by simpa [hEdgeEq, hTraceEq] using hConsume)).2
  have hTraceEq' :
      lookupD D' { sid := e.sid, sender := e.role, receiver := q } = tail := by
    simpa [hDout, hEdgeEq, hTraceEq] using (lookupD_update_eq (env:=D) (e:=recvEdge) (ts:=tail))
  exact ⟨L1, by simpa [hTraceEq'] using hTail, hConsumeT⟩

private theorem SendReady_preserved_recv_neq
    {G : GEnv} {D : DEnv} {receiverEp : Endpoint} {source : Role} {T : ValType}
    {L : LocalType} {recvEdge : Edge} {G' : GEnv} {D' : DEnv}
    {e : Endpoint} {q : Role} {T' : ValType} {L' : LocalType} {Lrecv : LocalType} :
    recvEdge = { sid := receiverEp.sid, sender := source, receiver := receiverEp.role } →
    G' = updateG G receiverEp L →
    D' = updateD D recvEdge (lookupD D recvEdge).tail →
    SendReady G D →
    lookupG G e = some (.send q T' L') →
    { sid := e.sid, role := q } ≠ receiverEp →
    lookupG G' { sid := e.sid, role := q } = some Lrecv →
    ∃ L1, Consume e.role Lrecv (lookupD D' { sid := e.sid, sender := e.role, receiver := q }) = some L1 ∧
      (Consume e.role L1 [T']).isSome := by
  -- If the receiver differs, D and G lookups are unchanged on the edge.
  intro hEdge hGout hDout hReady hGe hRecvNe hGrecv
  let recvEp : Endpoint := { sid := e.sid, role := q }
  have hRecv : lookupG G recvEp = some Lrecv := by
    simpa [hGout, lookupG_update_neq _ _ _ _ hRecvNe] using hGrecv
  obtain ⟨L1, hConsume, hConsumeT⟩ := hReady e q T' L' hGe Lrecv hRecv
  have hEdgeNe : { sid := e.sid, sender := e.role, receiver := q } ≠ recvEdge := by
    intro hEq; exact hRecvNe (by simpa [recvEp, hEdge] using hEq)
  have hTraceEq :
      lookupD D' { sid := e.sid, sender := e.role, receiver := q } =
        lookupD D { sid := e.sid, sender := e.role, receiver := q } := by
    simpa [hDout] using lookupD_update_neq (env:=D) (e:=recvEdge)
      (e':={ sid := e.sid, sender := e.role, receiver := q })
      (ts:=lookupD D recvEdge |>.tail) hEdgeNe
  exact ⟨L1, by simpa [hTraceEq] using hConsume, by simpa [hTraceEq] using hConsumeT⟩

private theorem SendReady_preserved_recv
    {G : GEnv} {D : DEnv} {receiverEp : Endpoint} {source : Role} {T : ValType}
    {L : LocalType} {recvEdge : Edge} {G' : GEnv} {D' : DEnv} :
    lookupG G receiverEp = some (.recv source T L) → recvEdge = { sid := receiverEp.sid, sender := source, receiver := receiverEp.role } →
    (lookupD D recvEdge).head? = some T →
    G' = updateG G receiverEp L →
    D' = updateD D recvEdge (lookupD D recvEdge).tail →
    (∀ q T L', L ≠ .send q T L') →
    SendReady G D →
    SendReady G' D' := by
  -- Split on whether the target receiver is updated.
  intro hG hEdge hTrace hGout hDout hNo hReady e q T' L' hGe Lrecv hGrecv
  have hGe' := lookupG_update_send_inv (e:=receiverEp) (ep:=e) hNo (by simpa [hGout] using hGe)
  let recvEp : Endpoint := { sid := e.sid, role := q }
  by_cases hRecvEq : recvEp = receiverEp
  · exact SendReady_preserved_recv_eq hG hEdge hTrace hGout hDout hReady hGe' hRecvEq hGrecv
  · exact SendReady_preserved_recv_neq hEdge hGout hDout hReady hGe' hRecvEq hGrecv

private theorem SendReady_preserved_select
    {G : GEnv} {D : DEnv} {senderEp : Endpoint} {target : Role}
    {bs : List (String × LocalType)} {ℓ : String} {L : LocalType} {selectEdge : Edge} {G' : GEnv} {D' : DEnv} :
    lookupG G senderEp = some (.select target bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    selectEdge = { sid := senderEp.sid, sender := senderEp.role, receiver := target } →
    G' = updateG G senderEp L → D' = appendD D selectEdge .string →
    (∀ q T L', L ≠ .send q T L') → SendReady G D → SendReady G' D' := by
  -- Updated endpoint is not send; append only affects the select edge.
  intro hG _ hEdge hGout hDout hNo hReady e q T' L' hGe Lrecv hGrecv
  have hGe' := lookupG_update_send_inv (e:=senderEp) (ep:=e) hNo (by simpa [hGout] using hGe)
  have hNe : e ≠ senderEp := by
    intro hEq; subst hEq
    have hSend : L = .send q T' L' := by simpa [hGout, lookupG_update_eq] using hGe
    exact (hNo q T' L' hSend).elim
  let recvEp : Endpoint := { sid := e.sid, role := q }
  have hRecvNe : recvEp ≠ senderEp := by
    intro hEq; subst hEq
    exact (send_ready_no_select_receiver hReady hGe' hG).elim
  have hRecv : lookupG G recvEp = some Lrecv := by
    simpa [hGout, lookupG_update_neq _ _ _ _ hRecvNe] using hGrecv
  obtain ⟨L1, hConsume, hConsumeT⟩ := hReady e q T' L' hGe' Lrecv hRecv
  have hEdgeNe : { sid := e.sid, sender := e.role, receiver := q } ≠ selectEdge := by
    intro hEq
    exact hNe (senderEp_of_edge_eq (q:=q) (target:=target) (by simpa [hEdge] using hEq))
  have hTraceEq :
      lookupD D' { sid := e.sid, sender := e.role, receiver := q } =
        lookupD D { sid := e.sid, sender := e.role, receiver := q } := by
    simpa [hDout] using lookupD_append_neq (D:=D) (edge:=selectEdge) (e:=_) (T:=.string) hEdgeNe
  exact ⟨L1, by simpa [hTraceEq] using hConsume, by simpa [hTraceEq] using hConsumeT⟩

private theorem SendReady_preserved_branch
    {G : GEnv} {D : DEnv} {brancherEp : Endpoint} {source : Role}
    {bs : List (String × LocalType)} {ℓ : String} {L : LocalType} {vs : List Value}
    {branchEdge : Edge} {G' : GEnv} {D' : DEnv} :
    lookupG G brancherEp = some (.branch source bs) →
    branchEdge = { sid := brancherEp.sid, sender := source, receiver := brancherEp.role } →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    G' = updateG G brancherEp L →
    D' = updateD D branchEdge (lookupD D branchEdge).tail →
    (∀ q T L', L ≠ .send q T L') → SendReady G D → SendReady G' D' := by
  -- Branch receiver cannot be a target of any send endpoint.
  intro hG hEdge _ hGout hDout hNo hReady e q T L hGe Lrecv hGrecv
  have hGe' := lookupG_update_send_inv (e:=brancherEp) (ep:=e) hNo (by simpa [hGout] using hGe)
  let recvEp : Endpoint := { sid := e.sid, role := q }
  have hRecvNe : recvEp ≠ brancherEp := by
    intro hEq; subst hEq
    exact (send_ready_no_branch_receiver hReady hGe' hG).elim
  have hRecv : lookupG G recvEp = some Lrecv := by
    simpa [hGout, lookupG_update_neq _ _ _ _ hRecvNe] using hGrecv
  obtain ⟨L1, hConsume, hConsumeT⟩ := hReady e q T L hGe' Lrecv hRecv
  have hEdgeNe : { sid := e.sid, sender := e.role, receiver := q } ≠ branchEdge := by
    intro hEq; exact hRecvNe (by simpa [recvEp, hEdge] using hEq)
  have hTraceEq :
      lookupD D' { sid := e.sid, sender := e.role, receiver := q } =
        lookupD D { sid := e.sid, sender := e.role, receiver := q } := by
    simpa [hDout] using lookupD_update_neq (env:=D) (e:=branchEdge)
      (e':={ sid := e.sid, sender := e.role, receiver := q })
      (ts:=lookupD D branchEdge |>.tail) hEdgeNe
  exact ⟨L1, by simpa [hTraceEq] using hConsume, by simpa [hTraceEq] using hConsumeT⟩

private theorem SendReady_preserved_par_left
    {Ssh store bufs store' bufs' P P' Q S G D₁ D₂ G₁' D₁' S₁'} (split : ParSplit S G) :
    TypedStep split.G1 D₁ Ssh split.S1 store bufs P G₁' D₁' S₁' store' bufs' P' →
    DisjointG split.G1 split.G2 →
    DConsistent split.G2 D₂ →
    NoNewSendStep (G:=split.G1) (D:=D₁) (Ssh:=Ssh) (Sown:=split.S1) (store:=store) (bufs:=bufs)
      (P:=P) (G':=G₁') (D':=D₁') (Sown':=S₁') (store':=store') (bufs':=bufs') (P':=P') →
    SendReady (split.G1 ++ split.G2) (D₁ ++ D₂) →
    (SendReady split.G1 D₁ → SendReady G₁' D₁') →
    SendReady (G₁' ++ split.G2) (D₁' ++ D₂) := by
  -- Split readiness to the left, apply IH, then re-append.
  intro hTS hDisj hCons hNo hReady ih
  have hReadyL := SendReady_left_of_append (G:=split.G1) (G₂:=split.G2) (D₁:=D₁) (D₂':=D₂)
    hDisj hCons hReady
  have hReadyL' := ih hReadyL
  have hSubG : SessionsOf G₁' ⊆ SessionsOf split.G1 := SessionsOf_subset_of_TypedStep hTS
  have hDisj' : DisjointG G₁' split.G2 := DisjointG_of_subset_left hSubG hDisj
  exact SendReady_append_left_total hDisj' hCons hReadyL'

private theorem SendReady_preserved_par_right
    {Ssh store bufs store' bufs' P Q Q' S G D₁ D₂ G₂' D₂' S₂'} (split : ParSplit S G) :
    TypedStep split.G2 D₂ Ssh split.S2 store bufs Q G₂' D₂' S₂' store' bufs' Q' →
    DisjointG split.G1 split.G2 →
    DConsistent split.G1 D₁ →
    NoNewSendStep (G:=split.G2) (D:=D₂) (Ssh:=Ssh) (Sown:=split.S2) (store:=store) (bufs:=bufs)
      (P:=Q) (G':=G₂') (D':=D₂') (Sown':=S₂') (store':=store') (bufs':=bufs') (P':=Q') →
    SendReady (split.G1 ++ split.G2) (D₁ ++ D₂) →
    (SendReady split.G2 D₂ → SendReady G₂' D₂') →
    SendReady (split.G1 ++ G₂') (D₁ ++ D₂') := by
  -- Split readiness to the right, apply IH, then re-append.
  intro hTS hDisj hCons hNo hReady ih
  have hReadyR := SendReady_right_of_append (G₁:=split.G1) (G:=split.G2) (D₁:=D₁) (D₂:=D₂)
    hDisj hCons hReady
  have hReadyR' := ih hReadyR
  have hSubG : SessionsOf G₂' ⊆ SessionsOf split.G2 := SessionsOf_subset_of_TypedStep hTS
  have hDisj' : DisjointG split.G1 G₂' := by
    have hDisjSymm := DisjointG_symm hDisj
    exact DisjointG_of_subset_left hSubG hDisjSymm
  exact SendReady_append_right_total hDisj' hCons hReadyR'

/-- Send readiness is preserved by TypedStep (no new send continuations). -/
theorem SendReady_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    (hTS : TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P') →
    NoNewSendStep hTS →
    SendReady G D →
    SendReady G' D' := by
  -- Induct on the step; recv uses Consume on the tail, par uses append framing.
  intro hTS hNo hReady
  induction hTS with
  | send _ _ hG _ _ _ hEdge hGout hDout _ =>
      exact SendReady_preserved_send hG hEdge hGout hDout (by simpa [NoNewSendStep] using hNo) hReady
  | recv _ hG hEdge _ _ hTrace hGout hDout _ _ _ =>
      exact SendReady_preserved_recv hG hEdge hTrace hGout hDout (by simpa [NoNewSendStep] using hNo) hReady
  | select _ hG hFind _ _ hEdge hGout hDout _ =>
      exact SendReady_preserved_select hG hFind hEdge hGout hDout (by simpa [NoNewSendStep] using hNo) hReady
  | branch _ hG hEdge _ _ hFind _ hGout hDout _ =>
      exact SendReady_preserved_branch hG hEdge hFind hGout hDout (by simpa [NoNewSendStep] using hNo) hReady
  | assign =>
      exact hReady
  | seq_step _ ih =>
      exact ih (by simpa [NoNewSendStep] using hNo) hReady
  | seq_skip =>
      exact hReady
  | par_left split hTS hDisjG _ _ hConsL hConsR ih =>
      exact SendReady_preserved_par_left split hTS hDisjG hConsR (by simpa [NoNewSendStep] using hNo) hReady ih
  | par_right split hTS hDisjG _ _ hConsL hConsR ih =>
      exact SendReady_preserved_par_right split hTS hDisjG hConsL (by simpa [NoNewSendStep] using hNo) hReady ih
  | par_skip_left | par_skip_right =>
      exact hReady

private theorem SelectReady_left_of_append
    {G G₂ : GEnv} {D₁ : DEnv} {D₂' : DEnv} :
    DisjointG G G₂ → DConsistent G₂ D₂' →
    SelectReady (G ++ G₂) (D₁ ++ D₂') → SelectReady G D₁ := by
  -- Restrict select readiness to the left by rewriting lookupD with disjointness.
  intro hDisj hCons hReady e q bs ℓ L hG hFind Lrecv hGrecv
  have hG' : lookupG (G ++ G₂) e = some (.select q bs) := lookupG_append_left hG
  have hGrecv' : lookupG (G ++ G₂) { sid := e.sid, role := q } = some Lrecv :=
    lookupG_append_left hGrecv
  obtain ⟨L', hConsume, hConsumeS⟩ := hReady e q bs ℓ L hG' hFind Lrecv hGrecv'
  have hSid : e.sid ∈ SessionsOf G := ⟨e, .select q bs, hG, rfl⟩
  have hNot : e.sid ∉ SessionsOf G₂ := sid_not_in_right_of_left hDisj hSid
  have hNone : D₂'.find? { sid := e.sid, sender := e.role, receiver := q } = none :=
    DEnv_find_none_of_notin_sessions hCons hNot
  have hTraceEq : lookupD (D₁ ++ D₂') { sid := e.sid, sender := e.role, receiver := q } =
      lookupD D₁ { sid := e.sid, sender := e.role, receiver := q } :=
    lookupD_append_left_of_right_none (D₁:=D₁) (D₂:=D₂') (e:=_) hNone
  exact ⟨L', by simpa [hTraceEq] using hConsume, by simpa [hTraceEq] using hConsumeS⟩

private theorem SelectReady_right_of_append
    {G₁ G : GEnv} {D₁ : DEnv} {D₂ : DEnv} :
    DisjointG G₁ G → DConsistent G₁ D₁ →
    SelectReady (G₁ ++ G) (D₁ ++ D₂) → SelectReady G D₂ := by
  -- Restrict select readiness to the right by rewriting lookupD with disjointness.
  intro hDisj hCons hReady e q bs ℓ L hG hFind Lrecv hGrecv
  have hG' : lookupG (G₁ ++ G) e = some (.select q bs) := by
    have hNone : lookupG G₁ e = none :=
      DisjointG_lookup_left (G₁:=G) (G₂:=G₁) (DisjointG_symm hDisj) hG
    simpa [lookupG_append_right (G₁:=G₁) (G₂:=G) (e:=e) hNone] using hG
  have hGrecv' : lookupG (G₁ ++ G) { sid := e.sid, role := q } = some Lrecv := by
    have hNone : lookupG G₁ { sid := e.sid, role := q } = none :=
      DisjointG_lookup_left (G₁:=G) (G₂:=G₁) (DisjointG_symm hDisj) hGrecv
    simpa [lookupG_append_right (G₁:=G₁) (G₂:=G) (e:=_) hNone] using hGrecv
  obtain ⟨L', hConsume, hConsumeS⟩ := hReady e q bs ℓ L hG' hFind Lrecv hGrecv'
  have hSid : e.sid ∈ SessionsOf G := ⟨e, .select q bs, hG, rfl⟩
  have hNot : e.sid ∉ SessionsOf G₁ := sid_not_in_right_of_left (DisjointG_symm hDisj) hSid
  have hNone : D₁.find? { sid := e.sid, sender := e.role, receiver := q } = none :=
    DEnv_find_none_of_notin_sessions hCons hNot
  have hTraceEq : lookupD (D₁ ++ D₂) { sid := e.sid, sender := e.role, receiver := q } =
      lookupD D₂ { sid := e.sid, sender := e.role, receiver := q } :=
    lookupD_append_right (D₁:=D₁) (D₂:=D₂) (e:=_) hNone
  exact ⟨L', by simpa [hTraceEq] using hConsume, by simpa [hTraceEq] using hConsumeS⟩

private theorem SelectReady_append_left_total
    {G : GEnv} {D : DEnv} {G₂ : GEnv} {D₂ : DEnv} :
    DisjointG G G₂ → DConsistent G₂ D₂ →
    SelectReady G D → SelectReady (G ++ G₂) (D ++ D₂) := by
  -- Lift select readiness to the append using SelectReady_append_left.
  intro hDisj hCons hReady e q bs ℓ L hG hFind Lrecv hGrecv
  have hTargetReady := hReady e q bs ℓ L hG hFind
  have hEdge : { sid := e.sid, sender := e.role, receiver := q } =
      { sid := e.sid, sender := e.role, receiver := q } := rfl
  exact SelectReady_append_left hG hTargetReady hEdge hDisj hCons Lrecv hGrecv

private theorem SelectReady_append_right_total
    {G₁ : GEnv} {D₁ : DEnv} {G : GEnv} {D : DEnv} :
    DisjointG G₁ G → DConsistent G₁ D₁ →
    SelectReady G D → SelectReady (G₁ ++ G) (D₁ ++ D) := by
  -- Lift select readiness to the append using SelectReady_append_right.
  intro hDisj hCons hReady e q bs ℓ L hG hFind Lrecv hGrecv
  have hTargetReady := hReady e q bs ℓ L hG hFind
  have hEdge : { sid := e.sid, sender := e.role, receiver := q } =
      { sid := e.sid, sender := e.role, receiver := q } := rfl
  exact SelectReady_append_right hG hTargetReady hEdge hDisj hCons Lrecv hGrecv

private theorem SelectReady_preserved_send
    {G : GEnv} {D : DEnv} {senderEp : Endpoint} {target : Role}
    {T : ValType} {L : LocalType} {sendEdge : Edge} {G' : GEnv} {D' : DEnv} :
    lookupG G senderEp = some (.send target T L) →
    sendEdge = { sid := senderEp.sid, sender := senderEp.role, receiver := target } →
    G' = updateG G senderEp L → D' = appendD D sendEdge T →
    (∀ q bs, L ≠ .select q bs) → SelectReady G D → SelectReady G' D' := by
  -- Updated endpoint is not select; append only affects the send edge.
  intro hG hEdge hGout hDout hNo hReady e q bs ℓ L' hGe hFind Lrecv hGrecv
  have hGe' := lookupG_update_select_inv (e:=senderEp) (ep:=e) hNo (by simpa [hGout] using hGe)
  have hNe : e ≠ senderEp := by
    intro hEq; subst hEq
    have hSel : L = .select q bs := by simpa [hGout, lookupG_update_eq] using hGe
    exact (hNo q bs hSel).elim
  let recvEp : Endpoint := { sid := e.sid, role := q }
  have hRecvNe : recvEp ≠ senderEp := by
    intro hEq; subst hEq
    exact (select_ready_no_send_receiver hReady hGe' hFind hG).elim
  have hRecv : lookupG G recvEp = some Lrecv := by
    simpa [hGout, lookupG_update_neq _ _ _ _ hRecvNe] using hGrecv
  obtain ⟨L1, hConsume, hConsumeS⟩ := hReady e q bs ℓ L' hGe' hFind Lrecv hRecv
  have hEdgeNe : { sid := e.sid, sender := e.role, receiver := q } ≠ sendEdge := by
    intro hEq
    exact hNe (senderEp_of_edge_eq (q:=q) (target:=target) (by simpa [hEdge] using hEq))
  have hTraceEq :
      lookupD D' { sid := e.sid, sender := e.role, receiver := q } =
        lookupD D { sid := e.sid, sender := e.role, receiver := q } := by
    simpa [hDout] using lookupD_append_neq (D:=D) (edge:=sendEdge) (e:=_) (T:=T) hEdgeNe
  exact ⟨L1, by simpa [hTraceEq] using hConsume, by simpa [hTraceEq] using hConsumeS⟩

private theorem SelectReady_preserved_recv_eq
    {G : GEnv} {D : DEnv} {receiverEp : Endpoint} {source : Role} {T : ValType}
    {L : LocalType} {recvEdge : Edge} {G' : GEnv} {D' : DEnv}
    {e : Endpoint} {q : Role} {bs : List (String × LocalType)} {ℓ : String} {L' : LocalType}
    {Lrecv : LocalType} :
    lookupG G receiverEp = some (.recv source T L) → recvEdge = { sid := receiverEp.sid, sender := source, receiver := receiverEp.role } →
    (lookupD D recvEdge).head? = some T →
    G' = updateG G receiverEp L → D' = updateD D recvEdge (lookupD D recvEdge).tail →
    SelectReady G D → lookupG G e = some (.select q bs) → bs.find? (fun b => b.1 == ℓ) = some (ℓ, L') →
    { sid := e.sid, role := q } = receiverEp → lookupG G' { sid := e.sid, role := q } = some Lrecv →
    ∃ L1, Consume e.role Lrecv (lookupD D' { sid := e.sid, sender := e.role, receiver := q }) = some L1 ∧
      (Consume e.role L1 [.string]).isSome := by
  -- If the receiver is updated, consume the head and reuse the tail.
  intro hG hEdge hTrace hGout hDout hReady hGe hFind hRecvEq hGrecv
  subst hRecvEq
  have hLrecv : Lrecv = L := by simpa [hGout, lookupG_update_eq] using hGrecv
  subst hLrecv
  obtain ⟨L1, hConsume, hConsumeS⟩ := hReady e q bs ℓ L' hGe hFind _ hG
  have hEqSender : e.role = source :=
    recv_sender_of_ready (from_:=e.role) (source:=source) (T:=T) (T':=.string) (L:=L)
      (ts:=lookupD D { sid := e.sid, sender := e.role, receiver := q }) (L1:=L1) hConsume hConsumeS
  obtain ⟨tail, hTraceEq⟩ := trace_cons_of_head (by simpa [hEdge] using hTrace)
  have hEdgeEq : { sid := e.sid, sender := e.role, receiver := q } = recvEdge := by
    cases hEqSender; simpa [hEdge] using rfl
  have hTail : Consume e.role L tail = some L1 := by
    exact (Consume_recv_tail_of_head (by simpa [hEdgeEq, hTraceEq] using hConsume)).2
  have hTraceEq' :
      lookupD D' { sid := e.sid, sender := e.role, receiver := q } = tail := by
    simpa [hDout, hEdgeEq, hTraceEq] using (lookupD_update_eq (env:=D) (e:=recvEdge) (ts:=tail))
  exact ⟨L1, by simpa [hTraceEq'] using hTail, hConsumeS⟩

private theorem SelectReady_preserved_recv_neq
    {G : GEnv} {D : DEnv} {receiverEp : Endpoint} {source : Role} {T : ValType}
    {L : LocalType} {recvEdge : Edge} {G' : GEnv} {D' : DEnv}
    {e : Endpoint} {q : Role} {bs : List (String × LocalType)} {ℓ : String}
    {L' : LocalType} {Lrecv : LocalType} :
    recvEdge = { sid := receiverEp.sid, sender := source, receiver := receiverEp.role } →
    G' = updateG G receiverEp L →
    D' = updateD D recvEdge (lookupD D recvEdge).tail →
    SelectReady G D →
    lookupG G e = some (.select q bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L') →
    { sid := e.sid, role := q } ≠ receiverEp →
    lookupG G' { sid := e.sid, role := q } = some Lrecv →
    ∃ L1, Consume e.role Lrecv (lookupD D' { sid := e.sid, sender := e.role, receiver := q }) = some L1 ∧
      (Consume e.role L1 [.string]).isSome := by
  -- If the receiver differs, D and G lookups are unchanged on the edge.
  intro hEdge hGout hDout hReady hGe hFind hRecvNe hGrecv
  let recvEp : Endpoint := { sid := e.sid, role := q }
  have hRecv : lookupG G recvEp = some Lrecv := by
    simpa [hGout, lookupG_update_neq _ _ _ _ hRecvNe] using hGrecv
  obtain ⟨L1, hConsume, hConsumeS⟩ := hReady e q bs ℓ L' hGe hFind Lrecv hRecv
  have hEdgeNe : { sid := e.sid, sender := e.role, receiver := q } ≠ recvEdge := by
    intro hEq; exact hRecvNe (by simpa [recvEp, hEdge] using hEq)
  have hTraceEq :
      lookupD D' { sid := e.sid, sender := e.role, receiver := q } =
        lookupD D { sid := e.sid, sender := e.role, receiver := q } := by
    simpa [hDout] using lookupD_update_neq (env:=D) (e:=recvEdge)
      (e':={ sid := e.sid, sender := e.role, receiver := q })
      (ts:=lookupD D recvEdge |>.tail) hEdgeNe
  exact ⟨L1, by simpa [hTraceEq] using hConsume, by simpa [hTraceEq] using hConsumeS⟩

private theorem SelectReady_preserved_recv
    {G : GEnv} {D : DEnv} {receiverEp : Endpoint} {source : Role} {T : ValType}
    {L : LocalType} {recvEdge : Edge} {G' : GEnv} {D' : DEnv} :
    lookupG G receiverEp = some (.recv source T L) →
    recvEdge = { sid := receiverEp.sid, sender := source, receiver := receiverEp.role } →
    (lookupD D recvEdge).head? = some T →
    G' = updateG G receiverEp L →
    D' = updateD D recvEdge (lookupD D recvEdge).tail →
    (∀ q bs, L ≠ .select q bs) →
    SelectReady G D →
    SelectReady G' D' := by
  -- Split on whether the target receiver is updated.
  intro hG hEdge hTrace hGout hDout hNo hReady e q bs ℓ L' hGe hFind Lrecv hGrecv
  have hGe' := lookupG_update_select_inv (e:=receiverEp) (ep:=e) hNo (by simpa [hGout] using hGe)
  let recvEp : Endpoint := { sid := e.sid, role := q }
  by_cases hRecvEq : recvEp = receiverEp
  · exact SelectReady_preserved_recv_eq hG hEdge hTrace hGout hDout hReady hGe' hFind hRecvEq hGrecv
  · exact SelectReady_preserved_recv_neq hEdge hGout hDout hReady hGe' hFind hRecvEq hGrecv

private theorem SelectReady_preserved_select
    {G : GEnv} {D : DEnv} {senderEp : Endpoint} {target : Role}
    {bs : List (String × LocalType)} {ℓ : String} {L : LocalType} {selectEdge : Edge} {G' : GEnv} {D' : DEnv} :
    lookupG G senderEp = some (.select target bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    selectEdge = { sid := senderEp.sid, sender := senderEp.role, receiver := target } →
    G' = updateG G senderEp L → D' = appendD D selectEdge .string →
    (∀ q bs, L ≠ .select q bs) → SelectReady G D → SelectReady G' D' := by
  -- Updated endpoint is not select; append only affects the select edge.
  intro hG _ hEdge hGout hDout hNo hReady e q bs' ℓ' L' hGe hFind Lrecv hGrecv
  have hGe' := lookupG_update_select_inv (e:=senderEp) (ep:=e) hNo (by simpa [hGout] using hGe)
  have hNe : e ≠ senderEp := by
    intro hEq; subst hEq
    have hSel : L = .select q bs' := by simpa [hGout, lookupG_update_eq] using hGe
    exact (hNo q bs' hSel).elim
  let recvEp : Endpoint := { sid := e.sid, role := q }
  have hRecvNe : recvEp ≠ senderEp := by
    intro hEq; subst hEq
    exact (select_ready_no_select_receiver hReady hGe' hFind hG).elim
  have hRecv : lookupG G recvEp = some Lrecv := by
    simpa [hGout, lookupG_update_neq _ _ _ _ hRecvNe] using hGrecv
  obtain ⟨L1, hConsume, hConsumeS⟩ := hReady e q bs' ℓ' L' hGe' hFind Lrecv hRecv
  have hEdgeNe : { sid := e.sid, sender := e.role, receiver := q } ≠ selectEdge := by
    intro hEq
    exact hNe (senderEp_of_edge_eq (q:=q) (target:=target) (by simpa [hEdge] using hEq))
  have hTraceEq :
      lookupD D' { sid := e.sid, sender := e.role, receiver := q } =
        lookupD D { sid := e.sid, sender := e.role, receiver := q } := by
    simpa [hDout] using lookupD_append_neq (D:=D) (edge:=selectEdge) (e:=_) (T:=.string) hEdgeNe
  exact ⟨L1, by simpa [hTraceEq] using hConsume, by simpa [hTraceEq] using hConsumeS⟩

private theorem SelectReady_preserved_branch
    {G : GEnv} {D : DEnv} {brancherEp : Endpoint} {source : Role}
    {bs : List (String × LocalType)} {ℓ : String} {L : LocalType} {vs : List Value} {branchEdge : Edge}
    {G' : GEnv} {D' : DEnv} :
    lookupG G brancherEp = some (.branch source bs) →
    branchEdge = { sid := brancherEp.sid, sender := source, receiver := brancherEp.role } →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    G' = updateG G brancherEp L →
    D' = updateD D branchEdge (lookupD D branchEdge).tail →
    (∀ q bs, L ≠ .select q bs) → SelectReady G D → SelectReady G' D' := by
  -- Branch receiver cannot be a target of any select endpoint.
  intro hG hEdge _ hGout hDout hNo hReady e q bs' ℓ' L' hGe hFind Lrecv hGrecv
  have hGe' := lookupG_update_select_inv (e:=brancherEp) (ep:=e) hNo (by simpa [hGout] using hGe)
  let recvEp : Endpoint := { sid := e.sid, role := q }
  have hRecvNe : recvEp ≠ brancherEp := by
    intro hEq; subst hEq
    exact (select_ready_no_branch_receiver hReady hGe' hFind hG).elim
  have hRecv : lookupG G recvEp = some Lrecv := by
    simpa [hGout, lookupG_update_neq _ _ _ _ hRecvNe] using hGrecv
  obtain ⟨L1, hConsume, hConsumeS⟩ := hReady e q bs' ℓ' L' hGe' hFind Lrecv hRecv
  have hEdgeNe : { sid := e.sid, sender := e.role, receiver := q } ≠ branchEdge := by
    intro hEq; exact hRecvNe (by simpa [recvEp, hEdge] using hEq)
  have hTraceEq :
      lookupD D' { sid := e.sid, sender := e.role, receiver := q } =
        lookupD D { sid := e.sid, sender := e.role, receiver := q } := by
    simpa [hDout] using lookupD_update_neq (env:=D) (e:=branchEdge)
      (e':={ sid := e.sid, sender := e.role, receiver := q })
      (ts:=lookupD D branchEdge |>.tail) hEdgeNe
  exact ⟨L1, by simpa [hTraceEq] using hConsume, by simpa [hTraceEq] using hConsumeS⟩

private theorem SelectReady_preserved_par_left
    {Ssh store bufs store' bufs' P P' Q S G D₁ D₂ G₁' D₁' S₁'} (split : ParSplit S G) :
    TypedStep split.G1 D₁ Ssh split.S1 store bufs P G₁' D₁' S₁' store' bufs' P' →
    DisjointG split.G1 split.G2 →
    DConsistent split.G2 D₂ →
    NoNewSelectStep (G:=split.G1) (D:=D₁) (Ssh:=Ssh) (Sown:=split.S1) (store:=store) (bufs:=bufs)
      (P:=P) (G':=G₁') (D':=D₁') (Sown':=S₁') (store':=store') (bufs':=bufs') (P':=P') →
    SelectReady (split.G1 ++ split.G2) (D₁ ++ D₂) →
    (SelectReady split.G1 D₁ → SelectReady G₁' D₁') →
    SelectReady (G₁' ++ split.G2) (D₁' ++ D₂) := by
  -- Split readiness to the left, apply IH, then re-append.
  intro hTS hDisj hCons hNo hReady ih
  have hReadyL := SelectReady_left_of_append (G:=split.G1) (G₂:=split.G2)
    (D₁:=_) (D₂':=_) hDisj hCons hReady
  have hReadyL' := ih hReadyL
  have hSubG : SessionsOf G₁' ⊆ SessionsOf split.G1 := SessionsOf_subset_of_TypedStep hTS
  have hDisj' : DisjointG G₁' split.G2 := DisjointG_of_subset_left hSubG hDisj
  exact SelectReady_append_left_total hDisj' hCons hReadyL'

private theorem SelectReady_preserved_par_right
    {Ssh store bufs store' bufs' P Q Q' S G D₁ D₂ G₂' D₂' S₂'} (split : ParSplit S G) :
    TypedStep split.G2 D₂ Ssh split.S2 store bufs Q G₂' D₂' S₂' store' bufs' Q' →
    DisjointG split.G1 split.G2 →
    DConsistent split.G1 D₁ →
    NoNewSelectStep (G:=split.G2) (D:=D₂) (Ssh:=Ssh) (Sown:=split.S2) (store:=store) (bufs:=bufs)
      (P:=Q) (G':=G₂') (D':=D₂') (Sown':=S₂') (store':=store') (bufs':=bufs') (P':=Q') →
    SelectReady (split.G1 ++ split.G2) (D₁ ++ D₂) →
    (SelectReady split.G2 D₂ → SelectReady G₂' D₂') →
    SelectReady (split.G1 ++ G₂') (D₁ ++ D₂') := by
  -- Split readiness to the right, apply IH, then re-append.
  intro hTS hDisj hCons hNo hReady ih
  have hReadyR := SelectReady_right_of_append (G₁:=split.G1) (G:=split.G2)
    (D₁:=_) (D₂:=_) hDisj hCons hReady
  have hReadyR' := ih hReadyR
  have hSubG : SessionsOf G₂' ⊆ SessionsOf split.G2 := SessionsOf_subset_of_TypedStep hTS
  have hDisj' : DisjointG split.G1 G₂' := by
    have hDisjSymm := DisjointG_symm hDisj
    exact DisjointG_of_subset_left hSubG hDisjSymm
  exact SelectReady_append_right_total hDisj' hCons hReadyR'

/-- Select readiness is preserved by TypedStep (no new select continuations). -/
theorem SelectReady_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    (hTS : TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P') →
    NoNewSelectStep hTS →
    SelectReady G D →
    SelectReady G' D' := by
  -- Induct on the step; recv uses Consume on the tail, par uses append framing.
  intro hTS hNo hReady
  induction hTS with
  | send _ _ hG _ _ _ hEdge hGout hDout _ =>
      exact SelectReady_preserved_send hG hEdge hGout hDout (by simpa [NoNewSelectStep] using hNo) hReady
  | recv _ hG hEdge _ _ hTrace hGout hDout _ _ _ =>
      exact SelectReady_preserved_recv hG hEdge hTrace hGout hDout (by simpa [NoNewSelectStep] using hNo) hReady
  | select _ hG hFind _ _ hEdge hGout hDout _ =>
      exact SelectReady_preserved_select hG hFind hEdge hGout hDout (by simpa [NoNewSelectStep] using hNo) hReady
  | branch _ hG hEdge _ _ hFind _ hGout hDout _ =>
      exact SelectReady_preserved_branch hG hEdge hFind hGout hDout (by simpa [NoNewSelectStep] using hNo) hReady
  | assign =>
      exact hReady
  | seq_step _ ih =>
      exact ih (by simpa [NoNewSelectStep] using hNo) hReady
  | seq_skip =>
      exact hReady
  | par_left split hTS hDisjG _ _ hConsL hConsR ih =>
      exact SelectReady_preserved_par_left split hTS hDisjG hConsR (by simpa [NoNewSelectStep] using hNo) hReady ih
  | par_right split hTS hDisjG _ _ hConsL hConsR ih =>
      exact SelectReady_preserved_par_right split hTS hDisjG hConsL (by simpa [NoNewSelectStep] using hNo) hReady ih
  | par_skip_left | par_skip_right =>
      exact hReady


/-- Shared/owned disjointness is preserved by TypedStep (assumed for now). -/
private theorem DisjointS_update_right
    {Ssh Sown : SEnv} {x : Var} {T : ValType}
    (hDisj : DisjointS Ssh Sown)
    (hNone : lookupSEnv Ssh x = none) :
    DisjointS Ssh (updateSEnv Sown x T) := by
  -- Updated variable cannot be in Ssh; otherwise reduce to hDisj.
  intro y Ty Ty' hLsh hLown
  by_cases hEq : y = x
  · subst hEq
    exact (Option.noConfusion (by simpa [hNone] using hLsh))
  · have hLown' : lookupSEnv Sown y = some Ty' := by
      simpa using (lookupSEnv_update_neq (env:=Sown) (x:=x) (y:=y) (T:=T) hEq)
    exact hDisj y Ty Ty' hLsh hLown'

private theorem DisjointS_left_of_append {Ssh S₁ S₂ : SEnv} :
    DisjointS Ssh (S₁ ++ S₂) →
    DisjointS Ssh S₁ := by
  -- Lift the right lookup into the append, then use disjointness.
  intro hDisj x T₁ T₂ hLsh hL1
  have hL12 := lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂) (x:=x) (T:=T₂) hL1
  exact hDisj x T₁ T₂ hLsh hL12

private theorem DisjointS_right_of_append {Ssh S₁ S₂ : SEnv} :
    DisjointS Ssh (S₁ ++ S₂) →
    DisjointS Ssh S₂ := by
  -- Split on whether S₁ already binds x, then use hDisj.
  intro hDisj x T₁ T₂ hLsh hL2
  cases hL1 : lookupSEnv S₁ x with
  | some T₁' =>
      have hL12 := lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂) (x:=x) (T:=T₁') hL1
      exact hDisj x T₁ T₁' hLsh hL12
  | none =>
      have hEq := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hL1
      have hL12 : lookupSEnv (S₁ ++ S₂) x = some T₂ := by
        simpa [hEq] using hL2
      exact hDisj x T₁ T₂ hLsh hL12

private theorem DisjointS_append_right
    {Ssh S₁ S₂ : SEnv} :
    DisjointS Ssh S₁ →
    DisjointS Ssh S₂ →
    DisjointS Ssh (S₁ ++ S₂) := by
  -- Route the append lookup to the appropriate side.
  intro hDisj1 hDisj2 x T₁ T₂ hLsh hL12
  cases hL1 : lookupSEnv S₁ x with
  | some T₁' =>
      have hEq : T₁' = T₂ := by
        have hLeft := lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂) (x:=x) (T:=T₁') hL1
        exact Option.some.inj (by simpa [hLeft] using hL12)
      exact hDisj1 x T₁ T₁' hLsh (by simpa [hEq] using hL1)
  | none =>
      have hRight := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hL1
      have hL2 : lookupSEnv S₂ x = some T₂ := by
        simpa [hRight] using hL12
      exact hDisj2 x T₁ T₂ hLsh hL2

/-- Disjointness is unchanged when Sown is unchanged. -/
private theorem DisjointS_preserved_nochange
    {Ssh Sown : SEnv} {G P Sfin Gfin W Δ} :
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    DisjointS Ssh Sown →
    DisjointS Ssh Sown := by
  -- No SEnv update: return the original disjointness.
  intro _ hDisj
  exact hDisj

private theorem DisjointS_preserved_recv_core
    {Ssh Sown : SEnv} {G : GEnv} {k x : Var} {e : Endpoint}
    {p : Role} {T : ValType} {L : LocalType} {Sfin Gfin W Δ} :
    HasTypeProcPreOut Ssh Sown G (.recv k x) Sfin Gfin W Δ →
    DisjointS Ssh Sown →
    DisjointS Ssh (updateSEnv Sown x T) := by
  -- recv pre-out typing guarantees x is not in Ssh.
  intro hPre hDisj
  cases hPre with
  | recv_new _ _ hSsh _ =>
      exact DisjointS_update_right hDisj hSsh
  | recv_old _ _ hSsh _ =>
      exact DisjointS_update_right hDisj hSsh

private theorem DisjointS_preserved_recv
    {Ssh Sown Sown' : SEnv} {G : GEnv} {k x : Var} {e : Endpoint}
    {p : Role} {T : ValType} {L : LocalType} {Sfin Gfin W Δ} :
    Sown' = updateSEnv Sown x T →
    HasTypeProcPreOut Ssh Sown G (.recv k x) Sfin Gfin W Δ →
    DisjointS Ssh Sown →
    DisjointS Ssh Sown' := by
  -- Rewrite the post-environment, then apply the core lemma.
  intro hSout hPre hDisj
  simpa [hSout] using DisjointS_preserved_recv_core (Ssh:=Ssh) (Sown:=Sown) (G:=G)
    (k:=k) (x:=x) (e:=e) (p:=p) (T:=T) (L:=L) (Sfin:=Sfin) (Gfin:=Gfin)
    (W:=W) (Δ:=Δ) hPre hDisj

private theorem DisjointS_preserved_assign_core
    {Ssh Sown : SEnv} {G : GEnv} {x : Var} {v : Value}
    {T T' : ValType} {Sfin Gfin W Δ} :
    HasTypeProcPreOut Ssh Sown G (.assign x v) Sfin Gfin W Δ →
    DisjointS Ssh Sown →
    DisjointS Ssh (updateSEnv Sown x T) := by
  -- assign pre-out typing also ensures x is not in Ssh.
  intro hPre hDisj
  cases hPre with
  | assign_new hSsh _ _ =>
      exact DisjointS_update_right hDisj hSsh
  | assign_old hSsh _ _ =>
      exact DisjointS_update_right hDisj hSsh

private theorem DisjointS_preserved_assign
    {Ssh Sown Sown' : SEnv} {G : GEnv} {x : Var} {v : Value}
    {T T' : ValType} {Sfin Gfin W Δ} :
    Sown' = updateSEnv Sown x T →
    HasTypeProcPreOut Ssh Sown G (.assign x v) Sfin Gfin W Δ →
    DisjointS Ssh Sown →
    DisjointS Ssh Sown' := by
  -- Rewrite the post-environment, then apply the core lemma.
  intro hSout hPre hDisj
  simpa [hSout] using DisjointS_preserved_assign_core (Ssh:=Ssh) (Sown:=Sown) (G:=G)
    (x:=x) (v:=v) (T:=T) (T':=T') (Sfin:=Sfin) (Gfin:=Gfin) (W:=W) (Δ:=Δ) hPre hDisj

private theorem DisjointS_preserved_seq
    {G D Ssh Sown store bufs P P' Q G' D' Sown' store' bufs'}
    {Sfin Gfin W Δ} :
    (∀ {Sfin Gfin W Δ},
      HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
      DisjointS Ssh Sown →
      DisjointS Ssh Sown') →
    HasTypeProcPreOut Ssh Sown G (.seq P Q) Sfin Gfin W Δ →
    DisjointS Ssh Sown →
    DisjointS Ssh Sown' := by
  -- The step is in P, so use the pre-out typing for P.
  intro ih hPre hDisj
  cases hPre with
  | seq hP _ =>
      exact ih hP hDisj

private theorem DisjointS_preserved_par_left
    {Ssh store bufs store' bufs' P P' Q S G D₁ D₂ G₁' D₁' S₁'}
    {Sfin Gfin W Δ} (split : ParSplit S G) :
    (∀ {Sfin Gfin W Δ},
      HasTypeProcPreOut Ssh split.S1 split.G1 P Sfin Gfin W Δ →
      DisjointS Ssh split.S1 →
      DisjointS Ssh S₁') →
    HasTypeProcPreOut Ssh S G (.par P Q) Sfin Gfin W Δ →
    DisjointS Ssh S →
    DisjointS Ssh (S₁' ++ split.S2) := by
  -- Invert the par pre-out typing and combine the two disjointness results.
  intro ih hPre hDisj
  cases hPre with
  | par split' _ _ _ _ _ _ _ _ _ _ _ _ _ hP _ =>
      have hEq : split' = split := ParSplit.unique split' split
      cases hEq
      have hDisjAll : DisjointS Ssh (split.S1 ++ split.S2) := by
        simpa [split.hS] using hDisj
      have hDisjS1 : DisjointS Ssh split.S1 := DisjointS_left_of_append hDisjAll
      have hDisjS2 : DisjointS Ssh split.S2 := DisjointS_right_of_append hDisjAll
      have hDisjS1' : DisjointS Ssh S₁' := ih hP hDisjS1
      exact DisjointS_append_right hDisjS1' hDisjS2

private theorem DisjointS_preserved_par_right
    {Ssh store bufs store' bufs' P Q Q' S G D₁ D₂ G₂' D₂' S₂'}
    {Sfin Gfin W Δ} (split : ParSplit S G) :
    (∀ {Sfin Gfin W Δ},
      HasTypeProcPreOut Ssh split.S2 split.G2 Q Sfin Gfin W Δ →
      DisjointS Ssh split.S2 →
      DisjointS Ssh S₂') →
    HasTypeProcPreOut Ssh S G (.par P Q) Sfin Gfin W Δ →
    DisjointS Ssh S →
    DisjointS Ssh (split.S1 ++ S₂') := by
  -- Invert the par pre-out typing and combine disjointness.
  intro ih hPre hDisj
  cases hPre with
  | par split' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hQ =>
      have hEq : split' = split := ParSplit.unique split' split
      cases hEq
      have hDisjAll : DisjointS Ssh (split.S1 ++ split.S2) := by
        simpa [split.hS] using hDisj
      have hDisjS1 : DisjointS Ssh split.S1 := DisjointS_left_of_append hDisjAll
      have hDisjS2 : DisjointS Ssh split.S2 := DisjointS_right_of_append hDisjAll
      have hDisjS2' : DisjointS Ssh S₂' := ih hQ hDisjS2
      exact DisjointS_append_right hDisjS1 hDisjS2'

/-- Shared/owned disjointness is preserved by TypedStep (requires pre-out typing). -/
theorem DisjointS_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'}
    {Sfin Gfin W Δ} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    DisjointS Ssh Sown →
    DisjointS Ssh Sown' := by
  -- Induction on steps; pre-out typing rules out shared-variable writes.
  intro hTS hPre hDisj
  induction hTS generalizing hPre with
  | send .. =>
      exact DisjointS_preserved_nochange hPre hDisj
  | recv _ _ _ _ _ _ _ _ hSout _ _ =>
      exact DisjointS_preserved_recv hSout hPre hDisj
  | select .. =>
      exact DisjointS_preserved_nochange hPre hDisj
  | branch .. =>
      exact DisjointS_preserved_nochange hPre hDisj
  | assign _ hSout _ =>
      exact DisjointS_preserved_assign hSout hPre hDisj
  | seq_step _ ih =>
      exact DisjointS_preserved_seq ih hPre hDisj
  | seq_skip =>
      exact DisjointS_preserved_nochange hPre hDisj
  | par_left split _ _ _ _ _ _ ih =>
      exact DisjointS_preserved_par_left split ih hPre hDisj
  | par_right split _ _ _ _ _ _ ih =>
      exact DisjointS_preserved_par_right split ih hPre hDisj
  | par_skip_left =>
      exact DisjointS_preserved_nochange hPre hDisj
  | par_skip_right =>
      exact DisjointS_preserved_nochange hPre hDisj

/-- DEnv consistency is preserved by TypedStep (assumed for now). -/
private theorem DConsistent_updateD
    {G : GEnv} {D : DEnv} {ep : Endpoint} {edge : Edge} {ts : List ValType}
    {Lold Lnew : LocalType}
    (hG : lookupG G ep = some Lold)
    (hSid : edge.sid = ep.sid)
    (hCons : DConsistent G D) :
    DConsistent (updateG G ep Lnew) (updateD D edge ts) := by
  -- Reduce to the old D or the updated session id using SessionsOfD_updateD_subset.
  intro s hs
  have hEqG : SessionsOf (updateG G ep Lnew) = SessionsOf G :=
    SessionsOf_updateG_eq (G:=G) (e:=ep) (L:=Lnew) (L':=Lold) hG
  have hs' := SessionsOfD_updateD_subset (D:=D) (e:=edge) (ts:=ts) hs
  cases hs' with
  | inl hOld =>
      -- Old session ids remain consistent via hCons and SessionsOf_updateG_eq.
      have hInG : s ∈ SessionsOf G := hCons hOld
      simpa [hEqG] using hInG
  | inr hNew =>
      -- The updated edge session id is present in G via the updated endpoint.
      have hEq : s = edge.sid := by simpa using hNew
      subst hEq
      have hInG : edge.sid ∈ SessionsOf G := by
        have hInG' : ep.sid ∈ SessionsOf G := ⟨ep, Lold, hG, rfl⟩
        simpa [hSid] using hInG'
      simpa [hEqG] using hInG

private theorem DConsistent_append
    {G₁ G₂ : GEnv} {D₁ D₂ : DEnv}
    (hCons₁ : DConsistent G₁ D₁) (hCons₂ : DConsistent G₂ D₂) :
    DConsistent (G₁ ++ G₂) (D₁ ++ D₂) := by
  -- Split on whether the session id comes from D₁ or D₂.
  intro s hs
  have hs' := SessionsOfD_append_subset (D₁:=D₁) (D₂:=D₂) hs
  cases hs' with
  | inl hLeft =>
      have hInG : s ∈ SessionsOf G₁ := hCons₁ hLeft
      exact SessionsOf_append_left (G₂:=G₂) hInG
  | inr hRight =>
      have hInG : s ∈ SessionsOf G₂ := hCons₂ hRight
      exact SessionsOf_append_right (G₁:=G₁) hInG

private theorem DConsistent_send
    {G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'}
    (hG : lookupG G e = some (.send target T L))
    (hEdge : sendEdge = { sid := e.sid, sender := e.role, receiver := target })
    (hGout : G' = updateG G e L)
    (hDout : D' = appendD D sendEdge T)
    (hCons : DConsistent G D) :
    DConsistent G' D' := by
  -- Send is just updateG + updateD on the send edge.
  have hSid : sendEdge.sid = e.sid := by simpa [hEdge]
  simpa [hGout, hDout, appendD] using
    (DConsistent_updateD (G:=G) (D:=D) (ep:=e) (edge:=sendEdge)
      (ts:=lookupD D sendEdge ++ [T]) (Lold:=.send target T L) (Lnew:=L) hG hSid hCons)

private theorem DConsistent_recv
    {G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'}
    (hG : lookupG G e = some (.recv source T L))
    (hEdge : recvEdge = { sid := e.sid, sender := source, receiver := e.role })
    (hGout : G' = updateG G e L)
    (hDout : D' = updateD D recvEdge (lookupD D recvEdge).tail)
    (hCons : DConsistent G D) :
    DConsistent G' D' := by
  -- Recv is updateG + updateD on the recv edge.
  have hSid : recvEdge.sid = e.sid := by simpa [hEdge]
  simpa [hGout, hDout] using
    (DConsistent_updateD (G:=G) (D:=D) (ep:=e) (edge:=recvEdge)
      (ts:=(lookupD D recvEdge).tail) (Lold:=.recv source T L) (Lnew:=L) hG hSid hCons)

private theorem DConsistent_select
    {G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'}
    (hG : lookupG G e = some (.select target bs))
    (hEdge : selectEdge = { sid := e.sid, sender := e.role, receiver := target })
    (hGout : G' = updateG G e L)
    (hDout : D' = appendD D selectEdge .string)
    (hCons : DConsistent G D) :
    DConsistent G' D' := by
  -- Select is updateG + updateD on the select edge.
  have hSid : selectEdge.sid = e.sid := by simpa [hEdge]
  simpa [hGout, hDout, appendD] using
    (DConsistent_updateD (G:=G) (D:=D) (ep:=e) (edge:=selectEdge)
      (ts:=lookupD D selectEdge ++ [.string]) (Lold:=.select target bs) (Lnew:=L) hG hSid hCons)

private theorem DConsistent_branch
    {G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'}
    (hG : lookupG G e = some (.branch source bs))
    (hEdge : branchEdge = { sid := e.sid, sender := source, receiver := e.role })
    (hGout : G' = updateG G e L)
    (hDout : D' = updateD D branchEdge (lookupD D branchEdge).tail)
    (hCons : DConsistent G D) :
    DConsistent G' D' := by
  -- Branch is updateG + updateD on the branch edge.
  have hSid : branchEdge.sid = e.sid := by simpa [hEdge]
  simpa [hGout, hDout] using
    (DConsistent_updateD (G:=G) (D:=D) (ep:=e) (edge:=branchEdge)
      (ts:=(lookupD D branchEdge).tail) (Lold:=.branch source bs) (Lnew:=L) hG hSid hCons)

/-- DEnv consistency is preserved by TypedStep. -/
theorem DConsistent_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    DConsistent G D →
    DConsistent G' D' := by
  -- Induct on the step; each constructor is handled by a focused helper lemma.
  intro hTS hCons
  induction hTS with
  | send _ _ hG _ _ _ hEdge hGout hDout _ =>
      exact DConsistent_send hG hEdge hGout hDout hCons
  | recv _ hG hEdge _ _ _ hGout hDout _ _ _ =>
      exact DConsistent_recv hG hEdge hGout hDout hCons
  | select _ hG _ _ hEdge hGout hDout _ =>
      exact DConsistent_select hG hEdge hGout hDout hCons
  | branch _ hG hEdge _ _ _ _ hGout hDout _ =>
      exact DConsistent_branch hG hEdge hGout hDout hCons
  | assign =>
      simpa using hCons
  | seq_step _ ih =>
      exact ih hCons
  | seq_skip =>
      simpa using hCons
  | par_left _ _ _ _ _ hConsL hConsR ih =>
      exact DConsistent_append (ih hConsL) hConsR
  | par_right _ _ _ _ _ hConsL hConsR ih =>
      exact DConsistent_append hConsL (ih hConsR)
  | par_skip_left =>
      simpa using hCons
  | par_skip_right =>
      simpa using hCons

/-- Main preservation theorem: TypedStep preserves well-formedness.

    **This is the resolution of Phase 4's blocking issue**: With TypedStep,
    preservation is straightforward because the judgment explicitly tracks
    resource transitions.

    **Proof strategy**: Case analysis on TypedStep:
    - StoreTyped: Use StoreTyped_update_nonChan for assign, unchanged for others
    - BuffersTyped: Use BuffersTyped_enqueue for send, handle recv
    - Coherent: Use typed_step_preserves_coherence
    - Compatible: Use Compatible_preserved (coinductive closure)
    - Process typing: By construction of TypedStep -/
theorem preservation_typed {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    (hTS : TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P') →
    WellFormed G D Ssh Sown store bufs P →
    WellFormed G' D' Ssh Sown' store' bufs' P' := by
  intro hTS hWF
  unfold WellFormed at hWF
  rcases hWF with
    ⟨hStore, hBufs, hCoh, hHead, hValid, hCompat, hDisjS, hCons, hPreOut⟩
  rcases hPreOut with ⟨Sfin, Gfin, W, Δ, hPreOut⟩
  have hStoreTyped : StoreTyped G (SEnvAll Ssh Sown) store := hStore.typeCorr
  obtain ⟨W', Δ', hPreOut'⟩ := HasTypeProcPreOut_preserved hStoreTyped hTS hPreOut
  have hCompat' : Compatible G' D' := Compatible_preserved hCompat hTS
  refine ⟨
    StoreTypedStrong_preserved hTS hStore hPreOut,
    BuffersTyped_preserved hTS hBufs,
    typed_step_preserves_coherence hTS hCoh,
    HeadCoherent_preserved hTS hCoh hHead,
    ValidLabels_preserved hTS hCoh hBufs hValid,
    hCompat',
    DisjointS_preserved hTS hPreOut hDisjS,
    DConsistent_preserved hTS hCons,
    ?_⟩
  exact ⟨Sfin, Gfin, W', Δ', hPreOut'⟩


end
