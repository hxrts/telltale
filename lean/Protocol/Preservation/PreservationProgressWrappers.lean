
import Protocol.Preservation.ValidLabelsHeadCoherent

/-! # Preservation and Progress Wrappers

HeadCoherent splitting lemmas and wrapper theorems connecting typed
configurations to preservation/progress guarantees. -/

/-
The Problem. HeadCoherent (buffer heads match expected types) must be
preserved through framing operations. When splitting a framed config
back into components, we need to recover HeadCoherent for each part.

Solution Structure. Prove `HeadCoherent_split_left` and `_split_right`
using disjointness and consistency to isolate each component's trace.
Provide wrapper theorems connecting typed configs to progress.
-/

/- ## Structured Block 1 -/
set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section

-- HeadCoherent Preservation

theorem HeadCoherent_split_left {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} :
    HeadCoherent (G₁ ++ G₂) (D₁ ++ D₂) →
    DisjointG G₁ G₂ →
    DConsistent G₂ D₂ →
    HeadCoherent G₁ D₁ := by
  intro hHead hDisj hCons e hActive
  rcases hActive with ⟨hSenderSome, hRecvSome⟩
  rcases (Option.isSome_iff_exists).1 hSenderSome with ⟨Lsender, hGsender⟩
  rcases (Option.isSome_iff_exists).1 hRecvSome with ⟨Lrecv, hGrecv⟩
  have hGrecv' : lookupG (G₁ ++ G₂) { sid := e.sid, role := e.receiver } = some Lrecv :=
    lookupG_append_left (G₁:=G₁) (G₂:=G₂) hGrecv
  have hGsender' : lookupG (G₁ ++ G₂) { sid := e.sid, role := e.sender } = some Lsender :=
    lookupG_append_left (G₁:=G₁) (G₂:=G₂) hGsender
  have hActiveMerged : ActiveEdge (G₁ ++ G₂) e :=
    ActiveEdge_of_endpoints hGsender' hGrecv'
  have hSid : e.sid ∈ SessionsOf G₁ :=
    ⟨{ sid := e.sid, role := e.receiver }, Lrecv, hGrecv, rfl⟩
  have hD2none : D₂.find? e = none := lookupD_none_of_disjointG hDisj hCons hSid
  have hTraceEq : lookupD (D₁ ++ D₂) e = lookupD D₁ e :=
    lookupD_append_left_of_right_none (D₁:=D₁) (D₂:=D₂) (e:=e) hD2none
  have hHeadMerged := hHead e hActiveMerged
  simp [hGrecv', hTraceEq] at hHeadMerged
  simpa [hGrecv, hTraceEq] using hHeadMerged

-- HeadCoherent Split: Right Component
theorem HeadCoherent_split_right {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} :
    HeadCoherent (G₁ ++ G₂) (D₁ ++ D₂) →
    DisjointG G₁ G₂ →
    DConsistent G₁ D₁ →
    HeadCoherent G₂ D₂ := by
  intro hHead hDisj hCons e hActive
  rcases hActive with ⟨hSenderSome, hRecvSome⟩
  rcases (Option.isSome_iff_exists).1 hSenderSome with ⟨Lsender, hGsender⟩
  rcases (Option.isSome_iff_exists).1 hRecvSome with ⟨Lrecv, hGrecv⟩
  have hSid : e.sid ∈ SessionsOf G₂ :=
    ⟨{ sid := e.sid, role := e.receiver }, Lrecv, hGrecv, rfl⟩
  have hNot : e.sid ∉ SessionsOf G₁ := by
    intro hIn
    have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hIn, hSid⟩
    have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = (∅ : Set SessionId) := hDisj
    simp [hEmpty] at hInter
  have hG1none : lookupG G₁ { sid := e.sid, role := e.receiver } = none :=
    lookupG_none_of_not_session hNot
  have hGrecv' : lookupG (G₁ ++ G₂) { sid := e.sid, role := e.receiver } = some Lrecv := by
    simpa [lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:={ sid := e.sid, role := e.receiver }) hG1none]
      using hGrecv
/- ## Structured Block 2 -/
  have hGsender' : lookupG (G₁ ++ G₂) { sid := e.sid, role := e.sender } = some Lsender := by
    have hG1none' : lookupG G₁ { sid := e.sid, role := e.sender } = none :=
      lookupG_none_of_not_session hNot
    simpa [lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:={ sid := e.sid, role := e.sender }) hG1none']
      using hGsender
  have hActiveMerged : ActiveEdge (G₁ ++ G₂) e :=
    ActiveEdge_of_endpoints hGsender' hGrecv'
  have hD1none : D₁.find? e = none :=
    lookupD_none_of_disjointG (G₁:=G₂) (G₂:=G₁) (D₂:=D₁) (DisjointG_symm hDisj) hCons hSid
  have hTraceEq : lookupD (D₁ ++ D₂) e = lookupD D₂ e :=
    lookupD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) hD1none
  have hHeadMerged := hHead e hActiveMerged
  simp [hGrecv', hTraceEq] at hHeadMerged
  simpa [hGrecv, hTraceEq] using hHeadMerged

-- HeadCoherent Merge Reconstruction
theorem HeadCoherent_merge {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} :
    HeadCoherent G₁ D₁ →
    HeadCoherent G₂ D₂ →
    DisjointG G₁ G₂ →
    DConsistent G₁ D₁ →
    DConsistent G₂ D₂ →
    HeadCoherent (G₁ ++ G₂) (D₁ ++ D₂) := by
  intro hHead1 hHead2 hDisj hCons1 hCons2 e hActive
  rcases hActive with ⟨hSenderSome, hRecvSome⟩
  rcases (Option.isSome_iff_exists).1 hSenderSome with ⟨Lsender, hGsender⟩
  rcases (Option.isSome_iff_exists).1 hRecvSome with ⟨Lrecv, hGrecv⟩
  have hCases :=
    lookupG_append_inv (G₁:=G₁) (G₂:=G₂) (e:={ sid := e.sid, role := e.receiver }) (L:=Lrecv)
      (by simpa using hGrecv)
  cases hCases with
  | inl hLeft =>
      have hSid : e.sid ∈ SessionsOf G₁ :=
        ⟨{ sid := e.sid, role := e.receiver }, Lrecv, hLeft, rfl⟩
      have hSenderCases :=
        lookupG_append_inv (G₁:=G₁) (G₂:=G₂) (e:={ sid := e.sid, role := e.sender }) (L:=Lsender)
          (by simpa using hGsender)
      have hSenderLeft : lookupG G₁ { sid := e.sid, role := e.sender } = some Lsender := by
        cases hSenderCases with
        | inl h => exact h
        | inr h =>
            have hSidSender : e.sid ∈ SessionsOf G₂ :=
              ⟨{ sid := e.sid, role := e.sender }, Lsender, h.2, rfl⟩
            have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hSid, hSidSender⟩
            have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = (∅ : Set SessionId) := hDisj
            simp [hEmpty] at hInter
      have hD2none : D₂.find? e = none := lookupD_none_of_disjointG hDisj hCons2 hSid
      have hTraceEq : lookupD (D₁ ++ D₂) e = lookupD D₁ e :=
        lookupD_append_left_of_right_none (D₁:=D₁) (D₂:=D₂) (e:=e) hD2none
      have hActiveLeft : ActiveEdge G₁ e :=
        ActiveEdge_of_endpoints hSenderLeft hLeft
      have hHeadLeft := hHead1 e hActiveLeft
/- ## Structured Block 3 -/
      have hHeadLeft' : match some Lrecv with
        | some (LocalType.recv a T a_1) =>
          match lookupD D₁ e with
          | [] => True
          | T' :: tail => T = T'
        | some (LocalType.branch a a_1) =>
          match lookupD D₁ e with
          | [] => True
          | T' :: tail => T' = ValType.string
        | x => True := by
          simpa [HeadCoherent, hLeft] using hHeadLeft
      simpa [HeadCoherent, hGrecv, hTraceEq] using hHeadLeft'
  -- HeadCoherent Merge: Right-side Receiver Case
  | inr hRight =>
      have hSid : e.sid ∈ SessionsOf G₂ :=
        ⟨{ sid := e.sid, role := e.receiver }, Lrecv, hRight.2, rfl⟩
      have hSenderCases :=
        lookupG_append_inv (G₁:=G₁) (G₂:=G₂) (e:={ sid := e.sid, role := e.sender }) (L:=Lsender)
          (by simpa using hGsender)
      have hSenderRight : lookupG G₂ { sid := e.sid, role := e.sender } = some Lsender := by
        cases hSenderCases with
        | inl h =>
            have hSidSender : e.sid ∈ SessionsOf G₁ :=
              ⟨{ sid := e.sid, role := e.sender }, Lsender, h, rfl⟩
            have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hSidSender, hSid⟩
            have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = (∅ : Set SessionId) := hDisj
            simp [hEmpty] at hInter
        | inr h => exact h.2
      have hD1none : D₁.find? e = none :=
        lookupD_none_of_disjointG (G₁:=G₂) (G₂:=G₁) (D₂:=D₁) (DisjointG_symm hDisj) hCons1 hSid
      have hTraceEq : lookupD (D₁ ++ D₂) e = lookupD D₂ e :=
        lookupD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) hD1none
      have hActiveRight : ActiveEdge G₂ e :=
        ActiveEdge_of_endpoints hSenderRight hRight.2
      have hHeadRight := hHead2 e hActiveRight
      have hHeadRight' : match some Lrecv with
        | some (LocalType.recv a T a_1) =>
          match lookupD D₂ e with
          | [] => True
          | T' :: tail => T = T'
        | some (LocalType.branch a a_1) =>
          match lookupD D₂ e with
          | [] => True
          | T' :: tail => T' = ValType.string
        | x => True := by
          simpa [HeadCoherent, hRight.2] using hHeadRight
      simpa [HeadCoherent, hGrecv, hTraceEq] using hHeadRight'

-- TypedStep HeadCoherent Preservation
theorem typed_step_preserves_headcoherent
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    HeadCoherent G D →
/- ## Structured Block 4 -/
    Coherent G D →
    HeadCoherent G' D' := by
  intro hTS hHead hCoh
  induction hTS with
  | send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
      subst hEdge hGout hDout
      simpa [hBufsOut] using
        (HeadCoherent_send_preserved G D e target T L hHead hCoh hG hRecvReady)
  | recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
      subst hEdge hGout hDout
      simpa [hBufsOut] using
        (HeadCoherent_recv_preserved G D e source T L hHead hCoh hG hTrace)
  | select hk hG hFind hReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
      subst hEdge hGout hDout
      simpa [hBufsOut] using
        (HeadCoherent_select_preserved G D e target bs ℓ L hHead hCoh hG hFind hReady)
  | branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
      subst hEdge hGout hDout
      simpa [hBufsOut] using
        (HeadCoherent_branch_preserved G D e source bs ℓ L hHead hCoh hG hFindT hTrace)
  | assign =>
      simpa using hHead
  | seq_step _ ih =>
      exact ih hHead hCoh
  | seq_skip =>
      simpa using hHead
  | par_left split hSlen hStep hDisjG hDisjD hDisjS ih =>
      exact ih hHead hCoh
  | par_right split hSlen hStep hDisjG hDisjD hDisjS ih =>
      exact ih hHead hCoh
  | par_skip_left =>
      simpa using hHead
  | par_skip_right =>
      simpa using hHead

-- Main Preservation Theorem

/-- TypedStep preserves LocalTypeR.WellFormed. -/
theorem preservation_typed
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    HasTypeProcPreOut_preserved_sub_middle_frame_spec →
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    LocalTypeR.WellFormed G D Ssh Sown store bufs P →
    LocalTypeR.WellFormed G' D' Ssh Sown' store' bufs' P' := by
  intro hMiddle hTS hWF
  rcases hWF with ⟨hStore, hBT, hCoh, hHead, hValid, hCompat, hDisjS, hOwn, hCons, hPre⟩
  rcases hPre with ⟨Sfin, Gfin, W, Δ, hPre, hDisjRightFin⟩
  have hStore' :
      StoreTypedStrong G' (SEnvAll Ssh Sown') store' :=
    StoreTypedStrong_preserved hTS hStore hPre hOwn hDisjRightFin
/- ## Structured Block 5 -/
  have hCoh' : Coherent G' D' := typed_step_preserves_coherence hTS hCoh
  have hBT' : BuffersTyped G' D' bufs' := BuffersTyped_preserved hTS hCoh hBT
  have hHead' : HeadCoherent G' D' := typed_step_preserves_headcoherent hTS hHead hCoh
  have hValid' : ValidLabels G' D' bufs' := ValidLabels_preserved hTS hValid hCoh hBT
  have hCompat' : Compatible G' D' := Compatible_preserved hCompat hTS
  have hDisjS' : DisjointS Ssh Sown' :=
    DisjointS_preserved_TypedStep_right hTS hPre hDisjS hOwn hDisjRightFin
  have hOwn' : OwnedDisjoint Sown' := OwnedDisjoint_preserved_TypedStep hTS hPre hOwn hDisjRightFin
  have hCons' : DConsistent G' D' := DConsistent_preserved hTS hCons
  have hStoreTyped : StoreTyped G (SEnvAll Ssh Sown) store := hStore.toStoreTyped
  obtain ⟨W', Δ', hPre'⟩ :=
    HasTypeProcPreOut_preserved hMiddle hStoreTyped hDisjS hOwn hTS hPre hDisjRightFin
  have hRightSub : SEnvDomSubset Sown'.right Sown.right :=
    TypedStep_right_domsubset hTS hPre
  have hDisjRightFin' : DisjointS Sown'.right Sfin.left :=
    DisjointS_of_domsubset_left hRightSub hDisjRightFin
  refine ⟨hStore', hBT', hCoh', hHead', hValid', hCompat', hDisjS', hOwn', hCons', ?_⟩
  exact ⟨Sfin, Gfin, W', Δ', hPre', hDisjRightFin'⟩

/-- Preservation: TypedStep preserves WellFormed. -/
theorem preservation
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    HasTypeProcPreOut_preserved_sub_middle_frame_spec →
    (hTS : TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P') →
    LocalTypeR.WellFormed G D Ssh Sown store bufs P →
    LocalTypeR.WellFormed G' D' Ssh Sown' store' bufs' P' := by
  -- Delegate to the canonical proof in Typing.Framing.
  exact preservation_typed

-- Progress Theorem

/-- Progress: a well-formed process can step or is blocked. -/
theorem progress {G D Ssh Sown store bufs P} :
    WellFormedComplete G D Ssh Sown store bufs P →
    (P = .skip) ∨
      (∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs P
        G' D' Sown' store' bufs' P') ∨
      BlockedProc store bufs P := by
  -- Delegate to the canonical progress proof in Typing.Preservation.
  exact progress_typed

/-- Progress with explicit RoleComplete (wrapper for convenience). -/
theorem progress_with_rolecomplete {G D Ssh Sown store bufs P} :
    LocalTypeR.WellFormed G D Ssh Sown store bufs P →
    RoleComplete G →
    (P = .skip) ∨
      (∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs P
        G' D' Sown' store' bufs' P') ∨
      BlockedProc store bufs P := by
  intro hWF hComplete
  exact progress (G:=G) (D:=D) (Ssh:=Ssh) (Sown:=Sown) (store:=store) (bufs:=bufs) (P:=P)
    ⟨hWF, hComplete⟩


end
