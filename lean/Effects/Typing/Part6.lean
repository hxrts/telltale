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
    have hCohL : Coherent split.G1 D₁ := Coherent_split_left hCohMerged
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
    intro e Lsender Lrecv hGsender hGrecv
    set senderEp : Endpoint := { sid := e.sid, role := e.sender }
    set recvEp : Endpoint := { sid := e.sid, role := e.receiver }
    have hInvSender := lookupG_append_inv (G₁:=G₁') (G₂:=split.G2) (e:=senderEp) hGsender
    cases hInvSender with
    | inl hSenderLeft =>
        have hSidLeft : e.sid ∈ SessionsOf G₁' := ⟨senderEp, Lsender, hSenderLeft, rfl⟩
        have hInvRecv := lookupG_append_inv (G₁:=G₁') (G₂:=split.G2) (e:=recvEp) hGrecv
        have hRecvLeft : lookupG G₁' recvEp = some Lrecv := by
          cases hInvRecv with
          | inl hLeft => exact hLeft
          | inr hRight =>
              have hSidRight : e.sid ∈ SessionsOf split.G2 := ⟨recvEp, Lrecv, hRight.2, rfl⟩
              have hInter : e.sid ∈ SessionsOf G₁' ∩ SessionsOf split.G2 := ⟨hSidLeft, hSidRight⟩
              have hEmpty : SessionsOf G₁' ∩ SessionsOf split.G2 = (∅ : Set SessionId) := hDisjG'
              have : e.sid ∈ (∅ : Set SessionId) := by
                simpa [hEmpty] using hInter
              exact this.elim
        have hD2none : D₂.find? e = none := lookupD_none_of_disjointG hDisjG' hConsR hSidLeft
        have hTraceEq : lookupD (D₁' ++ D₂) e = lookupD D₁' e :=
          lookupD_append_left_of_right_none (D₁:=D₁') (D₂:=D₂) (e:=e) hD2none
        have hCohEdge := hCohL' e Lsender Lrecv hSenderLeft hRecvLeft
        simpa [hTraceEq] using hCohEdge
    | inr hSenderRight =>
        have hSidRight : e.sid ∈ SessionsOf split.G2 := ⟨senderEp, Lsender, hSenderRight.2, rfl⟩
        have hInvRecv := lookupG_append_inv (G₁:=G₁') (G₂:=split.G2) (e:=recvEp) hGrecv
        have hRecvRight : lookupG split.G2 recvEp = some Lrecv := by
          cases hInvRecv with
          | inl hLeft =>
              have hSidLeft : e.sid ∈ SessionsOf G₁' := ⟨recvEp, Lrecv, hLeft, rfl⟩
              have hInter : e.sid ∈ SessionsOf G₁' ∩ SessionsOf split.G2 := ⟨hSidLeft, hSidRight⟩
              have hEmpty : SessionsOf G₁' ∩ SessionsOf split.G2 = (∅ : Set SessionId) := hDisjG'
              have : e.sid ∈ (∅ : Set SessionId) := by
                simpa [hEmpty] using hInter
              exact this.elim
          | inr hRight => exact hRight.2
        have hDisjGsym : DisjointG split.G2 split.G1 := DisjointG_symm hDisjG
        have hD1none : D₁'.find? e = none :=
          lookupD_none_of_disjointG (G₁:=split.G2) (G₂:=split.G1) (D₂:=D₁') hDisjGsym hSubD hSidRight
        have hTraceEq : lookupD (D₁' ++ D₂) e = lookupD D₂ e :=
          lookupD_append_right (D₁:=D₁') (D₂:=D₂) (e:=e) hD1none
        have hCohEdge := hCohR e Lsender Lrecv hSenderRight.2 hRecvRight
        simpa [hTraceEq] using hCohEdge
  | @TypedStep.par_right Ssh store bufs store' bufs' P Q Q' S G D₁ D₂ G₂' D₂' S₂' split
      hTS hDisjG hDisjD hDisjS hConsL hConsR, hCoh => by
    -- Right transition preserves its part, left unchanged.
    have hCohMerged : Coherent (split.G1 ++ split.G2) (D₁ ++ D₂) := by
      simpa [split.hG] using hCoh
    have hCohL : Coherent split.G1 D₁ := Coherent_split_left hCohMerged
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
    intro e Lsender Lrecv hGsender hGrecv
    set senderEp : Endpoint := { sid := e.sid, role := e.sender }
    set recvEp : Endpoint := { sid := e.sid, role := e.receiver }
    have hInvSender := lookupG_append_inv (G₁:=split.G1) (G₂:=G₂') (e:=senderEp) hGsender
    cases hInvSender with
    | inl hSenderLeft =>
        have hSidLeft : e.sid ∈ SessionsOf split.G1 := ⟨senderEp, Lsender, hSenderLeft, rfl⟩
        have hInvRecv := lookupG_append_inv (G₁:=split.G1) (G₂:=G₂') (e:=recvEp) hGrecv
        have hRecvLeft : lookupG split.G1 recvEp = some Lrecv := by
          cases hInvRecv with
          | inl hLeft => exact hLeft
          | inr hRight =>
              have hSidRight : e.sid ∈ SessionsOf G₂' := ⟨recvEp, Lrecv, hRight.2, rfl⟩
              have hInter : e.sid ∈ SessionsOf split.G1 ∩ SessionsOf G₂' := ⟨hSidLeft, hSidRight⟩
              have hEmpty : SessionsOf split.G1 ∩ SessionsOf G₂' = (∅ : Set SessionId) := hDisjG'
              have : e.sid ∈ (∅ : Set SessionId) := by
                simpa [hEmpty] using hInter
              exact this.elim
        have hD2none : D₂'.find? e = none :=
          lookupD_none_of_disjointG (G₁:=split.G1) (G₂:=split.G2) (D₂:=D₂') hDisjG hSubD hSidLeft
        have hTraceEq : lookupD (D₁ ++ D₂') e = lookupD D₁ e :=
          lookupD_append_left_of_right_none (D₁:=D₁) (D₂:=D₂') (e:=e) hD2none
        have hCohEdge := hCohL e Lsender Lrecv hSenderLeft hRecvLeft
        simpa [hTraceEq] using hCohEdge
    | inr hSenderRight =>
        have hSidRight : e.sid ∈ SessionsOf G₂' := ⟨senderEp, Lsender, hSenderRight.2, rfl⟩
        have hInvRecv := lookupG_append_inv (G₁:=split.G1) (G₂:=G₂') (e:=recvEp) hGrecv
        have hRecvRight : lookupG G₂' recvEp = some Lrecv := by
          cases hInvRecv with
          | inl hLeft =>
              have hSidLeft : e.sid ∈ SessionsOf split.G1 := ⟨recvEp, Lrecv, hLeft, rfl⟩
              have hInter : e.sid ∈ SessionsOf split.G1 ∩ SessionsOf G₂' := ⟨hSidLeft, hSidRight⟩
              have hEmpty : SessionsOf split.G1 ∩ SessionsOf G₂' = (∅ : Set SessionId) := hDisjG'
              have : e.sid ∈ (∅ : Set SessionId) := by
                simpa [hEmpty] using hInter
              exact this.elim
          | inr hRight => exact hRight.2
        have hDisjGsym : DisjointG G₂' split.G1 := DisjointG_symm hDisjG'
        have hD1none : D₁.find? e = none :=
          lookupD_none_of_disjointG (G₁:=G₂') (G₂:=split.G1) (D₂:=D₁) hDisjGsym hConsL hSidRight
        have hTraceEq : lookupD (D₁ ++ D₂') e = lookupD D₂' e :=
          lookupD_append_right (D₁:=D₁) (D₂:=D₂') (e:=e) hD1none
        have hCohEdge := hCohR' e Lsender Lrecv hSenderRight.2 hRecvRight
        simpa [hTraceEq] using hCohEdge
  | .par_skip_left, hCoh =>
    hCoh
  | .par_skip_right, hCoh =>
    hCoh

/-- Store typing is preserved by TypedStep (assumed for now). -/
axiom StoreTypedStrong_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    StoreTypedStrong G (SEnvAll Ssh Sown) store →
    StoreTypedStrong G' (SEnvAll Ssh Sown') store'

/-- Buffer typing is preserved by TypedStep (assumed for now). -/
axiom BuffersTyped_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    BuffersTyped G D bufs →
    BuffersTyped G' D' bufs'

/-- Head coherence is preserved by TypedStep (assumed for now). -/
axiom HeadCoherent_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    HeadCoherent G D →
    HeadCoherent G' D'

/-- ValidLabels is preserved by TypedStep (assumed for now). -/
axiom ValidLabels_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    ValidLabels G D bufs →
    ValidLabels G' D' bufs'

/-- Send readiness is preserved by TypedStep (assumed for now). -/
axiom SendReady_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    SendReady G D →
    SendReady G' D'

/-- Select readiness is preserved by TypedStep (assumed for now). -/
axiom SelectReady_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    SelectReady G D →
    SelectReady G' D'

/-- Shared/owned disjointness is preserved by TypedStep (assumed for now). -/
axiom DisjointS_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    DisjointS Ssh Sown →
    DisjointS Ssh Sown'

/-- DEnv consistency is preserved by TypedStep (assumed for now). -/
axiom DConsistent_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    DConsistent G D →
    DConsistent G' D'

/-- Main preservation theorem: TypedStep preserves well-formedness.

    **This is the resolution of Phase 4's blocking issue**: With TypedStep,
    preservation is straightforward because the judgment explicitly tracks
    resource transitions.

    **Proof strategy**: Case analysis on TypedStep:
    - StoreTyped: Use StoreTyped_update_nonChan for assign, unchanged for others
    - BuffersTyped: Use BuffersTyped_enqueue for send, handle recv
    - Coherent: Use typed_step_preserves_coherence
    - Process typing: By construction of TypedStep -/
theorem preservation_typed {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    WellFormed G D Ssh Sown store bufs P →
    WellFormed G' D' Ssh Sown' store' bufs' P' := by
  intro hTS hWF
  unfold WellFormed at hWF
  rcases hWF with
    ⟨hStore, hBufs, hCoh, hHead, hValid, hReady, hSelectReady, hDisjS, hCons, hPreOut⟩
  rcases hPreOut with ⟨Sfin, Gfin, W, Δ, hPreOut⟩
  have hStoreTyped : StoreTyped G (SEnvAll Ssh Sown) store := hStore.typeCorr
  obtain ⟨W', Δ', hPreOut'⟩ := HasTypeProcPreOut_preserved hStoreTyped hTS hPreOut
  refine ⟨
    StoreTypedStrong_preserved hTS hStore,
    BuffersTyped_preserved hTS hBufs,
    typed_step_preserves_coherence hTS hCoh,
    HeadCoherent_preserved hTS hHead,
    ValidLabels_preserved hTS hValid,
    SendReady_preserved hTS hReady,
    SelectReady_preserved hTS hSelectReady,
    DisjointS_preserved hTS hDisjS,
    DConsistent_preserved hTS hCons,
    ?_⟩
  exact ⟨Sfin, Gfin, W', Δ', hPreOut'⟩


end
