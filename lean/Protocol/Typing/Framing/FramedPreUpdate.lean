import Protocol.Environments.Core
import Protocol.Typing.StepLemmas
import Protocol.Typing.MergeLemmas
import Protocol.Typing.Framing.Lemmas
import Protocol.Typing.Framing.PreUpdateHelpers
import Protocol.Typing.Framing.LeftCases
import Protocol.Typing.Framing.RightCases
import Protocol.Typing.Framing.GEnvFrameLeft
import Protocol.Typing.Framing.GEnvFrameRight

/-! # MPST Framed Pre-Update Preservation

Stability of pre-out typing under single steps with G-frame on the right. -/

/-
The Problem. Show that pre-out typing is stable under a single step when the
global environment is framed on the right. This isolates how G-frames flow
through TypedStep.

Solution Structure. Prove case-specific stepping lemmas and assemble them by
induction on the TypedStep derivation, keeping frame and subset facts explicit.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ## Framed Pre-Update Preservation -/

/-- Specialize middle-frame preservation to the left-frame goal shape. -/
private lemma preserved_sub_left_frame_via_middle
    {Gstore G₁ G₂ G G' D Ssh Sown store bufs P D' Sown' store' bufs' P' Sfin Gfin W Δ G₁'} :
    HasTypeProcPreOut_preserved_sub_middle_frame_spec →
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    DisjointS Ssh (Sown : SEnv) →
    OwnedDisjoint Sown →
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    G' = G₁' ++ G₂ →
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    DisjointS Sown.right Sfin.left →
    HasTypeProcPreOut Ssh Sown G₁ P Sfin Gfin W Δ →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown' G₁' P' Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  intro hMiddle hStore hDisjShAll hOwnDisj hDisj hEq hEq' hTS hDisjRightFin hPre
  have hDisjG_left_mid : DisjointG ([] : GEnv) G₁ :=
    DisjointG_symm (DisjointG_right_empty G₁)
  have hDisjG_left_right : DisjointG ([] : GEnv) G₂ :=
    DisjointG_symm (DisjointG_right_empty G₂)
  have hEq_mid : G = ([] : GEnv) ++ G₁ ++ G₂ := by
    simpa using hEq
  obtain ⟨G₁_step', W', Δ', hEqG', _, hPre', hSubW, hSubΔ⟩ :=
    hMiddle
      (Gstore:=Gstore) (Gleft:=[]) (Gmid:=G₁) (Gright:=G₂)
      (G:=G) (G':=G')
      (D:=D) (Ssh:=Ssh) (Sown:=Sown)
      (store:=store) (bufs:=bufs) (P:=P)
      (Sfin:=Sfin) (Gfin:=Gfin) (W:=W) (Δ:=Δ)
      hStore hDisjShAll hOwnDisj
      hDisjG_left_mid hDisjG_left_right hDisj hEq_mid hTS hDisjRightFin hPre
  have hG₁' : G₁' = G₁_step' := by
    apply append_left_eq_of_eq
    calc
      G₁' ++ G₂ = G' := by simpa using hEq'.symm
      _ = ([] : GEnv) ++ G₁_step' ++ G₂ := hEqG'
      _ = G₁_step' ++ G₂ := by simp
  exact ⟨W', Δ', by simpa [hG₁'] using hPre', hSubW, hSubΔ⟩

/-- Specialize middle-frame preservation to the right-frame goal shape. -/
/-! ## Right-Frame Specialization via Middle -/
private lemma preserved_sub_right_frame_via_middle
    {Gstore G₁ G₂ G G' D Ssh Sown store bufs P D' Sown' store' bufs' P' Sfin Gfin W Δ G₂'} :
    HasTypeProcPreOut_preserved_sub_middle_frame_spec →
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    DisjointS Ssh (Sown : SEnv) →
    OwnedDisjoint Sown →
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    G' = G₁ ++ G₂' →
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    DisjointS Sown.right Sfin.left →
    HasTypeProcPreOut Ssh Sown G₂ P Sfin Gfin W Δ →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown' G₂' P' Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  intro hMiddle hStore hDisjShAll hOwnDisj hDisj hEq hEq' hTS hDisjRightFin hPre
  have hDisjG_left_empty : DisjointG G₁ ([] : GEnv) := DisjointG_right_empty G₁
  have hDisjG_mid_empty : DisjointG G₂ ([] : GEnv) := DisjointG_right_empty G₂
  have hEq_mid : G = G₁ ++ G₂ ++ ([] : GEnv) := by
    simpa using hEq
  obtain ⟨G₂_step', W', Δ', hEqG', _, hPre', hSubW, hSubΔ⟩ :=
    hMiddle
      (Gstore:=Gstore) (Gleft:=G₁) (Gmid:=G₂) (Gright:=[])
      (G:=G) (G':=G')
      (D:=D) (Ssh:=Ssh) (Sown:=Sown)
      (store:=store) (bufs:=bufs) (P:=P)
      (Sfin:=Sfin) (Gfin:=Gfin) (W:=W) (Δ:=Δ)
      hStore hDisjShAll hOwnDisj
      hDisj hDisjG_left_empty hDisjG_mid_empty hEq_mid hTS hDisjRightFin hPre
  have hG₂' : G₂' = G₂_step' := by
    apply append_right_eq_of_eq
    calc
      G₁ ++ G₂' = G' := by simpa using hEq'.symm
      _ = G₁ ++ G₂_step' ++ [] := hEqG'
      _ = G₁ ++ G₂_step' := by simp
  exact ⟨W', Δ', by simpa [hG₂'] using hPre', hSubW, hSubΔ⟩


/-- Pre-out typing is preserved under a step with a right G-frame. -/
/-! ## Left-Frame Preservation Theorem -/
theorem HasTypeProcPreOut_preserved_sub_left_frame
    {Gstore G₁ G₂ G G' D Ssh Sown store bufs P G₁' D' Sown' store' bufs' P' Sfin Gfin W Δ} :
    HasTypeProcPreOut_preserved_sub_middle_frame_spec →
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    DisjointS Ssh (Sown : SEnv) →
    OwnedDisjoint Sown →
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    G' = G₁' ++ G₂ →
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    HasTypeProcPreOut Ssh Sown G₁ P Sfin Gfin W Δ →
    DisjointS Sown.right Sfin.left →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown' G₁' P' Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  intro hMiddle hStore hDisjShAll hOwnDisj hDisj hEq hEq' hTS hPre hDisjRightFin
  induction hTS generalizing Sfin Gfin W Δ G₁ G₂ G₁' with
  /-! ## Left-Frame Case: send -/
  | send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
      have hStoreVis : StoreTypedVisible Gstore Ssh Sown store :=
        StoreTypedVisible_of_all (G:=Gstore) (Ssh:=Ssh) (Sown:=Sown) (store:=store)
          hStore hDisjShAll hOwnDisj
      -- Use the dedicated helper for the send case.
      exact preserved_sub_left_frame_send (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G')
        (Ssh:=Ssh) (Sown:=Sown) (k:=k) (x:=x) (e:=e) (target:=target) (T:=T) (L:=L)
        (G₁':=G₁')
        hStoreVis hEq hEq' hk hG hGout hPre
  /-! ## Left-Frame Case: recv -/
  | recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
      have hStoreVis : StoreTypedVisible Gstore Ssh Sown store :=
        StoreTypedVisible_of_all (G:=Gstore) (Ssh:=Ssh) (Sown:=Sown) (store:=store)
          hStore hDisjShAll hOwnDisj
      cases hPre with
      | recv_new hk' hG' hSsh hSownL =>
          -- Dispatch to the recv-new helper.
          exact preserved_sub_left_frame_recv_new (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G')
            (Ssh:=Ssh) (Sown:=Sown) (k:=k) (x:=x) (e:=e) (source:=source) (T:=T) (L:=L)
            (G₁':=G₁') (Sown':=Sown')
            hStoreVis hEq hEq' hk hG hGout hSout rfl rfl hk' hG'
      | recv_old hk' hG' hSsh hSownL =>
          -- Dispatch to the recv-old helper.
          exact preserved_sub_left_frame_recv_old (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G')
            (Ssh:=Ssh) (Sown:=Sown) (k:=k) (x:=x) (e:=e) (source:=source) (T:=T) (L:=L)
            (G₁':=G₁') (Sown':=Sown')
            hStoreVis hEq hEq' hk hG hGout hSout rfl rfl hk' hG'
  /-! ## Left-Frame Case: select -/
  | select hk hG hFind hReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
      have hStoreVis : StoreTypedVisible Gstore Ssh Sown store :=
        StoreTypedVisible_of_all (G:=Gstore) (Ssh:=Ssh) (Sown:=Sown) (store:=store)
          hStore hDisjShAll hOwnDisj
      -- Use the dedicated helper for the select case.
      exact preserved_sub_left_frame_select (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G')
        (Ssh:=Ssh) (Sown:=Sown) (k:=k) (ℓ:=ℓ) (e:=e) (target:=target) (bs:=bs) (L:=L)
        (G₁':=G₁')
        hStoreVis hEq hEq' hk hG hFind hGout hPre
  /-! ## Left-Frame Case: branch -/
  | branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
      have hStoreVis : StoreTypedVisible Gstore Ssh Sown store :=
        StoreTypedVisible_of_all (G:=Gstore) (Ssh:=Ssh) (Sown:=Sown) (store:=store)
          hStore hDisjShAll hOwnDisj
      -- Use the dedicated helper for the branch case.
      exact preserved_sub_left_frame_branch (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G')
        (Ssh:=Ssh) (Sown:=Sown) (k:=k) (procs:=procs) (e:=e) (source:=source) (bs:=bs)
        (ℓ:=ℓ) (P:=P) (L:=L) (G₁':=G₁')
        hStoreVis hEq hEq' hk hG hFindP hFindT hGout hPre
  /-! ## Left-Frame Case: assign -/
  | assign hv hSout hStoreOut =>
      rename_i G D Ssh Sown store bufs x v T_step Sown' store'
      cases hPre with
      | assign_new hSsh hSownL hv' =>
          -- Use the dedicated helper for the assign-new case.
          exact preserved_sub_left_frame_assign_new (G₁:=G₁) (G₂:=G₂) (G:=G)
            (Ssh:=Ssh) (Sown:=Sown) (x:=x) (v:=v) (T_step:=T_step) (Sown':=Sown')
            (G₁':=G₁')
            hEq hEq' hv hSout rfl rfl hSsh hSownL hv'
      | assign_old hSsh hSownL hv' =>
          -- Use the dedicated helper for the assign-old case.
          exact preserved_sub_left_frame_assign_old (G₁:=G₁) (G₂:=G₂) (G:=G)
            (Ssh:=Ssh) (Sown:=Sown) (x:=x) (v:=v) (T_step:=T_step) (Sown':=Sown')
            (G₁':=G₁')
            hEq hEq' hv hSout rfl rfl hSsh hSownL hv'
  /-! ## Left-Frame Case: seq_step -/
  | seq_step hTS ih =>
      cases hPre with
      | seq hP hQ =>
          rename_i W₁ W₂ Δ₁ Δ₂
          have hDomQ := HasTypeProcPreOut_domsubset hQ
          have hDisjRightMid :=
            DisjointS_of_domsubset_right hDomQ (by simpa using hDisjRightFin)
          obtain ⟨W₁', Δ₁', hP', hSubW, hSubΔ⟩ :=
            ih hStore hDisjShAll hOwnDisj hDisj hEq hEq' hP
              (by simpa using hDisjRightMid)
          refine ⟨W₁' ++ W₂, Δ₁' ++ Δ₂, ?_, ?_, ?_⟩
          · exact HasTypeProcPreOut.seq hP' hQ
          · exact FootprintSubset_append_left hSubW
          · exact SEnvDomSubset_append_left_of_domsubset hSubΔ
  /-! ## Left-Frame Case: seq_skip -/
  | seq_skip =>
      cases hPre with
      | seq hP hQ =>
          rename_i W₁ W₂ Δ₁ Δ₂
          cases hP
          refine ⟨W₂, Δ₂, ?_, ?_, ?_⟩
          ·
            have hEqG : G₁' ++ G₂ = G₁ ++ G₂ :=
              hEq'.symm.trans hEq
            have hG₁' : G₁' = G₁ := append_left_eq_of_eq hEqG
            simpa [hG₁'] using hQ
	          · simpa using (FootprintSubset_refl (W:=W₂))
	          · simpa using (SEnvDomSubset_append_right (S₁:=∅) (S₂:=Δ₂))
  /-! ## Left-Frame Case: par_left -/
  | par_left split hSlen hTS hDisjG hDisjD hDisjS ih =>
      rename_i Ssh Sown store bufs store' bufs' P P' Q G D₁ D₂ G₁_step D₁_step S₁_step nS nG
      have hTS_outer :
          TypedStep G (D₁ ++ D₂) Ssh Sown store bufs (.par nS nG P Q)
            (G₁_step ++ split.G2) (D₁_step ++ D₂)
            { right := Sown.right, left := S₁_step ++ split.S2 } store' bufs'
            (.par S₁_step.length nG P' Q) :=
        TypedStep.par_left split hSlen hTS hDisjG hDisjD hDisjS
      exact preserved_sub_left_frame_via_middle
        (Gstore:=Gstore) (G₁:=G₁) (G₂:=G₂)
        (G:=G) (G':=G₁_step ++ split.G2)
        (D:=D₁ ++ D₂) (Ssh:=Ssh) (Sown:=Sown)
        (store:=store) (bufs:=bufs) (P:=.par nS nG P Q)
        (D':=D₁_step ++ D₂) (Sown':={ right := Sown.right, left := S₁_step ++ split.S2 })
        (store':=store') (bufs':=bufs') (P':=.par S₁_step.length nG P' Q)
	        (Sfin:=Sfin) (Gfin:=Gfin) (W:=W) (Δ:=Δ) (G₁':=G₁')
	        hMiddle hStore hDisjShAll hOwnDisj hDisj hEq (by simpa using hEq') hTS_outer hDisjRightFin hPre
  /-! ## Left-Frame Case: par_right -/
  | par_right split hSlen hTS hDisjG hDisjD hDisjS ih =>
      rename_i Ssh Sown store bufs store' bufs' P Q Q' G D₁ D₂ G₂_step D₂_step S₂_step nS nG
      have hTS_outer :
          TypedStep G (D₁ ++ D₂) Ssh Sown store bufs (.par nS nG P Q)
            (split.G1 ++ G₂_step) (D₁ ++ D₂_step)
            { right := Sown.right, left := split.S1 ++ S₂_step } store' bufs'
            (.par split.S1.length nG P Q') :=
        TypedStep.par_right split hSlen hTS hDisjG hDisjD hDisjS
      exact preserved_sub_left_frame_via_middle
        (Gstore:=Gstore) (G₁:=G₁) (G₂:=G₂)
        (G:=G) (G':=split.G1 ++ G₂_step)
        (D:=D₁ ++ D₂) (Ssh:=Ssh) (Sown:=Sown)
        (store:=store) (bufs:=bufs) (P:=.par nS nG P Q)
        (D':=D₁ ++ D₂_step) (Sown':={ right := Sown.right, left := split.S1 ++ S₂_step })
        (store':=store') (bufs':=bufs') (P':=.par split.S1.length nG P Q')
	        (Sfin:=Sfin) (Gfin:=Gfin) (W:=W) (Δ:=Δ) (G₁':=G₁')
	        hMiddle hStore hDisjShAll hOwnDisj hDisj hEq (by simpa using hEq') hTS_outer hDisjRightFin hPre

  /-! ## Left-Frame Case: par_skip_left -/
  | par_skip_left split hSlen hS1Nil =>
      rename_i G D Ssh Sown store bufs Q nS nG
      have hTS_outer :
          TypedStep G D Ssh Sown store bufs (.par nS nG .skip Q)
            G D Sown store bufs Q :=
        TypedStep.par_skip_left split hSlen hS1Nil
      exact preserved_sub_left_frame_via_middle
        (Gstore:=Gstore) (G₁:=G₁) (G₂:=G₂)
        (G:=G) (G':=G)
        (D:=D) (Ssh:=Ssh) (Sown:=Sown)
        (store:=store) (bufs:=bufs) (P:=.par nS nG .skip Q)
        (D':=D) (Sown':=Sown)
        (store':=store) (bufs':=bufs) (P':=Q)
	        (Sfin:=Sfin) (Gfin:=Gfin) (W:=W) (Δ:=Δ) (G₁':=G₁')
	        hMiddle hStore hDisjShAll hOwnDisj hDisj hEq (by simpa using hEq') hTS_outer hDisjRightFin hPre
  /-! ## Left-Frame Case: par_skip_right -/
  | par_skip_right split hSlen hS2Nil =>
      rename_i G D Ssh Sown store bufs P nS nG
      have hTS_outer :
          TypedStep G D Ssh Sown store bufs (.par nS nG P .skip)
            G D Sown store bufs P :=
        TypedStep.par_skip_right split hSlen hS2Nil
      exact preserved_sub_left_frame_via_middle
        (Gstore:=Gstore) (G₁:=G₁) (G₂:=G₂)
        (G:=G) (G':=G)
        (D:=D) (Ssh:=Ssh) (Sown:=Sown)
        (store:=store) (bufs:=bufs) (P:=.par nS nG P .skip)
        (D':=D) (Sown':=Sown)
        (store':=store) (bufs':=bufs) (P':=P)
	        (Sfin:=Sfin) (Gfin:=Gfin) (W:=W) (Δ:=Δ) (G₁':=G₁')
	        hMiddle hStore hDisjShAll hOwnDisj hDisj hEq (by simpa using hEq') hTS_outer hDisjRightFin hPre

/-- Pre-out typing is preserved under a step with a left G-frame. -/
/-! ## Right-Frame Preservation Theorem -/
theorem HasTypeProcPreOut_preserved_sub_right_frame
    {Gstore G₁ G₂ G G' D Ssh Sown store bufs P G₂' D' Sown' store' bufs' P' Sfin Gfin W Δ} :
    HasTypeProcPreOut_preserved_sub_middle_frame_spec →
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    DisjointS Ssh (Sown : SEnv) →
    OwnedDisjoint Sown →
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    G' = G₁ ++ G₂' →
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    HasTypeProcPreOut Ssh Sown G₂ P Sfin Gfin W Δ →
    DisjointS Sown.right Sfin.left →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown' G₂' P' Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  intro hMiddle hStore hDisjShAll hOwnDisj hDisj hEq hEq' hTS hPre hDisjRightFin
  induction hTS generalizing Sfin Gfin W Δ G₁ G₂ G₂' with
  /-! ## Right-Frame Case: send -/
  | send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
      have hStoreVis : StoreTypedVisible Gstore Ssh Sown store :=
        StoreTypedVisible_of_all (G:=Gstore) (Ssh:=Ssh) (Sown:=Sown) (store:=store)
          hStore hDisjShAll hOwnDisj
      -- Use the dedicated helper for the send case.
      exact preserved_sub_right_frame_send (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G')
        (Ssh:=Ssh) (Sown:=Sown) (k:=k) (x:=x) (e:=e) (target:=target) (T:=T) (L:=L)
        (G₂':=G₂')
        hStoreVis hDisj hEq hEq' hk hG hGout hPre
  /-! ## Right-Frame Case: recv -/
  | recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
      have hStoreVis : StoreTypedVisible Gstore Ssh Sown store :=
        StoreTypedVisible_of_all (G:=Gstore) (Ssh:=Ssh) (Sown:=Sown) (store:=store)
          hStore hDisjShAll hOwnDisj
      cases hPre with
      | recv_new hk' hG' hSsh hSownL =>
          -- Use the dedicated helper for the recv-new case.
          exact preserved_sub_right_frame_recv_new (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G')
            (Ssh:=Ssh) (Sown:=Sown) (k:=k) (x:=x) (e:=e) (source:=source) (T:=T) (L:=L)
            (G₂':=G₂') (Sown':=Sown')
            hStoreVis hDisj hEq hEq' hk hG hGout hSout rfl rfl hk' hG'
      | recv_old hk' hG' hSsh hSownL =>
          -- Use the dedicated helper for the recv-old case.
          exact preserved_sub_right_frame_recv_old (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G')
            (Ssh:=Ssh) (Sown:=Sown) (k:=k) (x:=x) (e:=e) (source:=source) (T:=T) (L:=L)
            (G₂':=G₂') (Sown':=Sown')
            hStoreVis hDisj hEq hEq' hk hG hGout hSout rfl rfl hk' hG'
  /-! ## Right-Frame Case: select -/
  | select hk hG hFind hReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
      have hStoreVis : StoreTypedVisible Gstore Ssh Sown store :=
        StoreTypedVisible_of_all (G:=Gstore) (Ssh:=Ssh) (Sown:=Sown) (store:=store)
          hStore hDisjShAll hOwnDisj
      -- Use the dedicated helper for the select case.
      exact preserved_sub_right_frame_select (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G')
        (Ssh:=Ssh) (Sown:=Sown) (k:=k) (ℓ:=ℓ) (e:=e) (target:=target) (bs:=bs) (L:=L)
        (G₂':=G₂')
        hStoreVis hDisj hEq hEq' hk hG hFind hGout hPre
  /-! ## Right-Frame Case: branch -/
  | branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
      have hStoreVis : StoreTypedVisible Gstore Ssh Sown store :=
        StoreTypedVisible_of_all (G:=Gstore) (Ssh:=Ssh) (Sown:=Sown) (store:=store)
          hStore hDisjShAll hOwnDisj
      -- Use the dedicated helper for the branch case.
      exact preserved_sub_right_frame_branch (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G')
        (Ssh:=Ssh) (Sown:=Sown) (k:=k) (procs:=procs) (e:=e) (source:=source) (bs:=bs)
        (ℓ:=ℓ) (P:=P) (L:=L) (G₂':=G₂')
        hStoreVis hDisj hEq hEq' hk hG hFindP hFindT hGout hPre
  /-! ## Right-Frame Case: assign -/
  | assign hv hSout hStoreOut =>
      rename_i G D Ssh Sown store bufs x v T_step Sown' store'
      cases hPre with
      | assign_new hSsh hSownL hv' =>
          -- Use the dedicated helper for the assign-new case.
          exact preserved_sub_right_frame_assign_new (G₁:=G₁) (G₂:=G₂) (G:=G)
            (Ssh:=Ssh) (Sown:=Sown) (x:=x) (v:=v) (T_step:=T_step) (Sown':=Sown')
            (G₂':=G₂')
            hDisj hEq hEq' hv hSout rfl rfl hSsh hSownL hv'
      | assign_old hSsh hSownL hv' =>
          -- Use the dedicated helper for the assign-old case.
          exact preserved_sub_right_frame_assign_old (G₁:=G₁) (G₂:=G₂) (G:=G)
            (Ssh:=Ssh) (Sown:=Sown) (x:=x) (v:=v) (T_step:=T_step) (Sown':=Sown')
            (G₂':=G₂')
            hDisj hEq hEq' hv hSout rfl rfl hSsh hSownL hv'
  /-! ## Right-Frame Case: seq_step -/
  | seq_step hTS ih =>
      rename_i G D Ssh Sown G' D' Sown' store bufs store' bufs' P P' Q
      cases hPre with
      | seq hP hQ =>
          rename_i S₁ G₁_mid W₁ W₂ Δ₁ Δ₂
          have hDomQ : SEnvDomSubset S₁.left Sfin.left := HasTypeProcPreOut_domsubset hQ
          have hDisjRightMid : DisjointS Sown.right S₁.left :=
            DisjointS_of_domsubset_right hDomQ hDisjRightFin
          obtain ⟨W₁', Δ₁', hP', hSubW, hSubΔ⟩ :=
            ih hStore hDisjShAll hOwnDisj hDisj hEq hEq' hP hDisjRightMid
          refine ⟨W₁' ++ W₂, Δ₁' ++ Δ₂, ?_, ?_, ?_⟩
          · exact HasTypeProcPreOut.seq hP' hQ
	          · exact FootprintSubset_append_left hSubW
	          · exact SEnvDomSubset_append_left_of_domsubset hSubΔ
  /-! ## Right-Frame Case: seq_skip -/
  | seq_skip =>
      cases hPre with
      | seq hP hQ =>
          rename_i W₁ W₂ Δ₁ Δ₂
          cases hP
          refine ⟨W₂, Δ₂, ?_, ?_, ?_⟩
          ·
            have hEqG : G₁ ++ G₂' = G₁ ++ G₂ :=
              hEq'.symm.trans hEq
            have hG₂' : G₂' = G₂ := append_right_eq_of_eq hEqG
            simpa [hG₂'] using hQ
	          · simpa using (FootprintSubset_refl (W:=W₂))
	          · simpa using (SEnvDomSubset_append_right (S₁:=∅) (S₂:=Δ₂))
  /-! ## Right-Frame Case: par_left -/
  | par_left split hSlen hTS hDisjG hDisjD hDisjS ih =>
      rename_i Ssh Sown store bufs store' bufs' P P' Q G D₁ D₂ G₁_step D₁_step S₁_step nS nG
      have hTS_outer :
          TypedStep G (D₁ ++ D₂) Ssh Sown store bufs (.par nS nG P Q)
            (G₁_step ++ split.G2) (D₁_step ++ D₂)
            { right := Sown.right, left := S₁_step ++ split.S2 } store' bufs'
            (.par S₁_step.length nG P' Q) :=
        TypedStep.par_left split hSlen hTS hDisjG hDisjD hDisjS
      exact preserved_sub_right_frame_via_middle
        (Gstore:=Gstore) (G₁:=G₁) (G₂:=G₂)
        (G:=G) (G':=G₁_step ++ split.G2)
        (D:=D₁ ++ D₂) (Ssh:=Ssh) (Sown:=Sown)
        (store:=store) (bufs:=bufs) (P:=.par nS nG P Q)
        (D':=D₁_step ++ D₂) (Sown':={ right := Sown.right, left := S₁_step ++ split.S2 })
        (store':=store') (bufs':=bufs') (P':=.par S₁_step.length nG P' Q)
	        (Sfin:=Sfin) (Gfin:=Gfin) (W:=W) (Δ:=Δ) (G₂':=G₂')
	        hMiddle hStore hDisjShAll hOwnDisj hDisj hEq (by simpa using hEq') hTS_outer hDisjRightFin hPre
  /-! ## Right-Frame Case: par_right -/
  | par_right split hSlen hTS hDisjG hDisjD hDisjS ih =>
      rename_i Ssh Sown store bufs store' bufs' P Q Q' G D₁ D₂ G₂_step D₂_step S₂_step nS nG
      have hTS_outer :
          TypedStep G (D₁ ++ D₂) Ssh Sown store bufs (.par nS nG P Q)
            (split.G1 ++ G₂_step) (D₁ ++ D₂_step)
            { right := Sown.right, left := split.S1 ++ S₂_step } store' bufs'
            (.par split.S1.length nG P Q') :=
        TypedStep.par_right split hSlen hTS hDisjG hDisjD hDisjS
      exact preserved_sub_right_frame_via_middle
        (Gstore:=Gstore) (G₁:=G₁) (G₂:=G₂)
        (G:=G) (G':=split.G1 ++ G₂_step)
        (D:=D₁ ++ D₂) (Ssh:=Ssh) (Sown:=Sown)
        (store:=store) (bufs:=bufs) (P:=.par nS nG P Q)
        (D':=D₁ ++ D₂_step) (Sown':={ right := Sown.right, left := split.S1 ++ S₂_step })
        (store':=store') (bufs':=bufs') (P':=.par split.S1.length nG P Q')
	        (Sfin:=Sfin) (Gfin:=Gfin) (W:=W) (Δ:=Δ) (G₂':=G₂')
	        hMiddle hStore hDisjShAll hOwnDisj hDisj hEq (by simpa using hEq') hTS_outer hDisjRightFin hPre
  /-! ## Right-Frame Case: par_skip_left -/
  | par_skip_left split hSlen hS1Nil =>
      rename_i G D Ssh Sown store bufs Q nS nG
      have hTS_outer :
          TypedStep G D Ssh Sown store bufs (.par nS nG .skip Q)
            G D Sown store bufs Q :=
        TypedStep.par_skip_left split hSlen hS1Nil
      exact preserved_sub_right_frame_via_middle
        (Gstore:=Gstore) (G₁:=G₁) (G₂:=G₂)
        (G:=G) (G':=G)
        (D:=D) (Ssh:=Ssh) (Sown:=Sown)
        (store:=store) (bufs:=bufs) (P:=.par nS nG .skip Q)
        (D':=D) (Sown':=Sown)
        (store':=store) (bufs':=bufs) (P':=Q)
	        (Sfin:=Sfin) (Gfin:=Gfin) (W:=W) (Δ:=Δ) (G₂':=G₂')
	        hMiddle hStore hDisjShAll hOwnDisj hDisj hEq (by simpa using hEq') hTS_outer hDisjRightFin hPre
  /-! ## Right-Frame Case: par_skip_right -/
  | par_skip_right split hSlen hS2Nil =>
      rename_i G D Ssh Sown store bufs P nS nG
      have hTS_outer :
          TypedStep G D Ssh Sown store bufs (.par nS nG P .skip)
            G D Sown store bufs P :=
        TypedStep.par_skip_right split hSlen hS2Nil
      exact preserved_sub_right_frame_via_middle
        (Gstore:=Gstore) (G₁:=G₁) (G₂:=G₂)
        (G:=G) (G':=G)
        (D:=D) (Ssh:=Ssh) (Sown:=Sown)
        (store:=store) (bufs:=bufs) (P:=.par nS nG P .skip)
        (D':=D) (Sown':=Sown)
        (store':=store) (bufs':=bufs) (P':=P)
        (Sfin:=Sfin) (Gfin:=Gfin) (W:=W) (Δ:=Δ) (G₂':=G₂')
        hMiddle hStore hDisjShAll hOwnDisj hDisj hEq (by simpa using hEq') hTS_outer hDisjRightFin hPre


end
