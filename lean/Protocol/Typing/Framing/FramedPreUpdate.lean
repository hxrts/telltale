import Protocol.Environments.Core
import Protocol.Typing.StepLemmas
import Protocol.Typing.MergeLemmas
import Protocol.Typing.Framing.Lemmas
import Protocol.Typing.Framing.PreUpdateHelpers
import Protocol.Typing.Framing.LeftCases
import Protocol.Typing.Framing.RightCases
import Protocol.Typing.Framing.ParCases

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

noncomputable section

/-! ### Framed Pre-Update Preservation -/


/-- Pre-out typing is preserved under a step with a right G-frame. -/
theorem HasTypeProcPreOut_preserved_sub_left_frame
    {Gstore G₁ G₂ G G' D Ssh Sown store bufs P G₁' D' Sown' store' bufs' P' Sfin Gfin W Δ} :
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    G' = G₁' ++ G₂ →
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    HasTypeProcPreOut Ssh Sown G₁ P Sfin Gfin W Δ →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown' G₁' P' Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  intro hStore hDisj hEq hEq' hTS hPre
  induction hTS generalizing Sfin Gfin W Δ G₁ G₂ G₁' with
  | send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
      -- Use the dedicated helper for the send case.
      exact preserved_sub_left_frame_send (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G')
        (Ssh:=Ssh) (Sown:=Sown) (k:=k) (x:=x) (e:=e) (target:=target) (T:=T) (L:=L)
        (G₁':=G₁')
        hStore hEq hEq' hk hG hGout hPre
  | recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
      cases hPre with
      | recv_new hk' hG' hSsh hSownR hSownL =>
          -- Dispatch to the recv-new helper.
          exact preserved_sub_left_frame_recv_new (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G')
            (Ssh:=Ssh) (Sown:=Sown) (k:=k) (x:=x) (e:=e) (source:=source) (T:=T) (L:=L)
            (G₁':=G₁') (Sown':=Sown')
            hStore hEq hEq' hk hG hGout hSout rfl rfl hk' hG'
      | recv_old hk' hG' hSsh hSownR hSownL =>
          -- Dispatch to the recv-old helper.
          exact preserved_sub_left_frame_recv_old (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G')
            (Ssh:=Ssh) (Sown:=Sown) (k:=k) (x:=x) (e:=e) (source:=source) (T:=T) (L:=L)
            (G₁':=G₁') (Sown':=Sown')
            hStore hEq hEq' hk hG hGout hSout rfl rfl hk' hG'
  | select hk hG hFind hReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
      -- Use the dedicated helper for the select case.
      exact preserved_sub_left_frame_select (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G')
        (Ssh:=Ssh) (Sown:=Sown) (k:=k) (ℓ:=ℓ) (e:=e) (target:=target) (bs:=bs) (L:=L)
        (G₁':=G₁')
        hStore hEq hEq' hk hG hFind hGout hPre
  | branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
      -- Use the dedicated helper for the branch case.
      exact preserved_sub_left_frame_branch (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G')
        (Ssh:=Ssh) (Sown:=Sown) (k:=k) (procs:=procs) (e:=e) (source:=source) (bs:=bs)
        (ℓ:=ℓ) (P:=P) (L:=L) (G₁':=G₁')
        hStore hEq hEq' hk hG hFindP hFindT hGout hPre
  | assign hv hSout hStoreOut =>
      rename_i G D Ssh Sown store bufs x v T_step Sown' store'
      cases hPre with
      | assign_new hSsh hSownR hSownL hv' =>
          -- Use the dedicated helper for the assign-new case.
          exact preserved_sub_left_frame_assign_new (G₁:=G₁) (G₂:=G₂) (G:=G)
            (Ssh:=Ssh) (Sown:=Sown) (x:=x) (v:=v) (T_step:=T_step) (Sown':=Sown')
            (G₁':=G₁')
            hEq hEq' hv hSout rfl rfl hSsh hSownR hSownL hv'
      | assign_old hSsh hSownR hSownL hv' =>
          -- Use the dedicated helper for the assign-old case.
          exact preserved_sub_left_frame_assign_old (G₁:=G₁) (G₂:=G₂) (G:=G)
            (Ssh:=Ssh) (Sown:=Sown) (x:=x) (v:=v) (T_step:=T_step) (Sown':=Sown')
            (G₁':=G₁')
            hEq hEq' hv hSout rfl rfl hSsh hSownR hSownL hv'
  | seq_step hTS ih =>
      cases hPre with
      | seq hP hQ =>
          rename_i W₁ W₂ Δ₁ Δ₂
          obtain ⟨W₁', Δ₁', hP', hSubW, hSubΔ⟩ := ih hStore hDisj hEq hEq' hP
          refine ⟨W₁' ++ W₂, Δ₁' ++ Δ₂, ?_, ?_, ?_⟩
          · exact HasTypeProcPreOut.seq hP' hQ
          · exact FootprintSubset_append_left hSubW
          · exact SEnvDomSubset_append_left_of_domsubset hSubΔ
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
  | par_left split hSlen hGlen hTS hDisjG hDisjD hDisjS ih =>
      rename_i Ssh Sown store bufs store' bufs' P P' Q G D₁ D₂ G₁_step D₁_step S₁_step nS nG
      have hStore' : StoreTyped Gstore (SEnvAll Ssh { right := Sown.right, left := split.S1 ++ split.S2 }) store := by
        simpa [SEnvAll, split.hS, List.append_assoc] using hStore
      have hStoreL : StoreTyped Gstore (SEnvAll Ssh { right := Sown.right ++ split.S2, left := split.S1 }) store :=
        store_typed_left_swap (Ssh:=Ssh) (Sown:=Sown) (S1:=split.S1) (S2:=split.S2) hStore' hDisjS
      exact preserved_sub_left_frame_par_left
        (split:=split) hStoreL hDisj hEq hEq' hSlen hGlen hTS hDisjG hDisjS ih hPre
  | par_right split hSlen hGlen hTS hDisjG hDisjD hDisjS ih =>
      rename_i Ssh Sown store bufs store' bufs' P Q Q' G D₁ D₂ G₂_step D₂_step S₂_step nS nG
      have hStoreR :
          StoreTyped Gstore (SEnvAll Ssh { right := Sown.right ++ split.S1, left := split.S2 }) store := by
        simpa [SEnvAll, split.hS, List.append_assoc] using hStore
      exact preserved_sub_left_frame_par_right
        (split:=split) hStoreR hDisj hEq hEq' hSlen hGlen hTS hDisjG hDisjS ih hPre

  | par_skip_left =>
      have hQ := HasTypeProcPreOut_par_skip_left hPre
      have hEqG : G₁' ++ G₂ = G₁ ++ G₂ := by
        simpa [hEq] using hEq'.symm
      have hG₁' : G₁' = G₁ := append_left_eq_of_eq hEqG
      refine ⟨W, Δ, ?_, FootprintSubset_refl, SEnvDomSubset_refl⟩
      cases hG₁'
      exact hQ
  | par_skip_right =>
      have hP := HasTypeProcPreOut_par_skip_right hPre
      have hEqG : G₁' ++ G₂ = G₁ ++ G₂ := by
        simpa [hEq] using hEq'.symm
      have hG₁' : G₁' = G₁ := append_left_eq_of_eq hEqG
      refine ⟨W, Δ, ?_, FootprintSubset_refl, SEnvDomSubset_refl⟩
      cases hG₁'
      exact hP

/-- Pre-out typing is preserved under a step with a left G-frame. -/
theorem HasTypeProcPreOut_preserved_sub_right_frame
    {Gstore G₁ G₂ G G' D Ssh Sown store bufs P G₂' D' Sown' store' bufs' P' Sfin Gfin W Δ} :
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    G' = G₁ ++ G₂' →
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    HasTypeProcPreOut Ssh Sown G₂ P Sfin Gfin W Δ →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown' G₂' P' Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  intro hStore hDisj hEq hEq' hTS hPre
  induction hTS generalizing Sfin Gfin W Δ G₁ G₂ G₂' with
  | send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
      -- Use the dedicated helper for the send case.
      exact preserved_sub_right_frame_send (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G')
        (Ssh:=Ssh) (Sown:=Sown) (k:=k) (x:=x) (e:=e) (target:=target) (T:=T) (L:=L)
        (G₂':=G₂')
        hStore hDisj hEq hEq' hk hG hGout hPre
  | recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
      cases hPre with
      | recv_new hk' hG' hSsh hSownR hSownL =>
          -- Use the dedicated helper for the recv-new case.
          exact preserved_sub_right_frame_recv_new (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G')
            (Ssh:=Ssh) (Sown:=Sown) (k:=k) (x:=x) (e:=e) (source:=source) (T:=T) (L:=L)
            (G₂':=G₂') (Sown':=Sown')
            hStore hDisj hEq hEq' hk hG hGout hSout rfl rfl hk' hG'
      | recv_old hk' hG' hSsh hSownR hSownL =>
          -- Use the dedicated helper for the recv-old case.
          exact preserved_sub_right_frame_recv_old (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G')
            (Ssh:=Ssh) (Sown:=Sown) (k:=k) (x:=x) (e:=e) (source:=source) (T:=T) (L:=L)
            (G₂':=G₂') (Sown':=Sown')
            hStore hDisj hEq hEq' hk hG hGout hSout rfl rfl hk' hG'
  | select hk hG hFind hReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
      -- Use the dedicated helper for the select case.
      exact preserved_sub_right_frame_select (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G')
        (Ssh:=Ssh) (Sown:=Sown) (k:=k) (ℓ:=ℓ) (e:=e) (target:=target) (bs:=bs) (L:=L)
        (G₂':=G₂')
        hStore hDisj hEq hEq' hk hG hFind hGout hPre
  | branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
      -- Use the dedicated helper for the branch case.
      exact preserved_sub_right_frame_branch (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G')
        (Ssh:=Ssh) (Sown:=Sown) (k:=k) (procs:=procs) (e:=e) (source:=source) (bs:=bs)
        (ℓ:=ℓ) (P:=P) (L:=L) (G₂':=G₂')
        hStore hDisj hEq hEq' hk hG hFindP hFindT hGout hPre
  | assign hv hSout hStoreOut =>
      rename_i G D Ssh Sown store bufs x v T_step Sown' store'
      cases hPre with
      | assign_new hSsh hSownR hSownL hv' =>
          -- Use the dedicated helper for the assign-new case.
          exact preserved_sub_right_frame_assign_new (G₁:=G₁) (G₂:=G₂) (G:=G)
            (Ssh:=Ssh) (Sown:=Sown) (x:=x) (v:=v) (T_step:=T_step) (Sown':=Sown')
            (G₂':=G₂')
            hDisj hEq hEq' hv hSout rfl rfl hSsh hSownR hSownL hv'
      | assign_old hSsh hSownR hSownL hv' =>
          -- Use the dedicated helper for the assign-old case.
          exact preserved_sub_right_frame_assign_old (G₁:=G₁) (G₂:=G₂) (G:=G)
            (Ssh:=Ssh) (Sown:=Sown) (x:=x) (v:=v) (T_step:=T_step) (Sown':=Sown')
            (G₂':=G₂')
            hDisj hEq hEq' hv hSout rfl rfl hSsh hSownR hSownL hv'
  | seq_step hTS ih =>
      cases hPre with
      | seq hP hQ =>
          rename_i W₁ W₂ Δ₁ Δ₂
          obtain ⟨W₁', Δ₁', hP', hSubW, hSubΔ⟩ := ih hStore hDisj hEq hEq' hP
          refine ⟨W₁' ++ W₂, Δ₁' ++ Δ₂, ?_, ?_, ?_⟩
          · exact HasTypeProcPreOut.seq hP' hQ
          · exact FootprintSubset_append_left hSubW
          · exact SEnvDomSubset_append_left_of_domsubset hSubΔ
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
  | par_left split hSlen hGlen hTS hDisjG hDisjD hDisjS ih =>
      rename_i Ssh Sown store bufs store' bufs' P P' Q G D₁ D₂ G₁_step D₁_step S₁_step nS nG
      have hTS_outer :
          TypedStep G (D₁ ++ D₂) Ssh Sown store bufs (.par nS nG P Q)
            (G₁_step ++ split.G2) (D₁_step ++ D₂)
            { right := Sown.right, left := S₁_step ++ split.S2 } store' bufs'
            (.par S₁_step.length G₁_step.length P' Q) :=
        TypedStep.par_left split hSlen hGlen hTS hDisjG hDisjD hDisjS
      have hDisjG_left_empty : DisjointG G₁ ([] : GEnv) := DisjointG_right_empty G₁
      have hDisjG_mid_empty : DisjointG G₂ ([] : GEnv) := DisjointG_right_empty G₂
      have hEq_mid : G = G₁ ++ G₂ ++ ([] : GEnv) := by
        simpa using hEq
      obtain ⟨G₂_step, W', Δ', hEqG', _, hPre', hSubW, hSubΔ⟩ :=
        HasTypeProcPreOut_preserved_sub_middle_frame
          (Gstore:=Gstore) (Gleft:=G₁) (Gmid:=G₂) (Gright:=[])
          (G:=G) (D:=D₁ ++ D₂) (Ssh:=Ssh) (Sown:=Sown)
          (store:=store) (bufs:=bufs) (P:=.par nS nG P Q)
          (Sfin:=Sfin) (Gfin:=Gfin) (W:=W) (Δ:=Δ)
          hStore hDisj hDisjG_left_empty hDisjG_mid_empty hEq_mid hTS_outer hPre
      have hG₂' : G₂' = G₂_step := by
        apply append_right_eq_of_eq
        calc
          G₁ ++ G₂' = G₁_step ++ split.G2 := by simpa using hEq'.symm
          _ = G₁ ++ G₂_step ++ [] := hEqG'
          _ = G₁ ++ G₂_step := by simp
      refine ⟨W', Δ', ?_, hSubW, hSubΔ⟩
      simpa [hG₂'] using hPre'
  | par_right split hSlen hGlen hTS hDisjG hDisjD hDisjS ih =>
      rename_i Ssh Sown store bufs store' bufs' P Q Q' G D₁ D₂ G₂_step D₂_step S₂_step nS nG
      have hTS_outer :
          TypedStep G (D₁ ++ D₂) Ssh Sown store bufs (.par nS nG P Q)
            (split.G1 ++ G₂_step) (D₁ ++ D₂_step)
            { right := Sown.right, left := split.S1 ++ S₂_step } store' bufs'
            (.par split.S1.length split.G1.length P Q') :=
        TypedStep.par_right split hSlen hGlen hTS hDisjG hDisjD hDisjS
      have hDisjG_left_empty : DisjointG G₁ ([] : GEnv) := DisjointG_right_empty G₁
      have hDisjG_mid_empty : DisjointG G₂ ([] : GEnv) := DisjointG_right_empty G₂
      have hEq_mid : G = G₁ ++ G₂ ++ ([] : GEnv) := by
        simpa using hEq
      obtain ⟨G₂_step', W', Δ', hEqG', _, hPre', hSubW, hSubΔ⟩ :=
        HasTypeProcPreOut_preserved_sub_middle_frame
          (Gstore:=Gstore) (Gleft:=G₁) (Gmid:=G₂) (Gright:=[])
          (G:=G) (D:=D₁ ++ D₂) (Ssh:=Ssh) (Sown:=Sown)
          (store:=store) (bufs:=bufs) (P:=.par nS nG P Q)
          (Sfin:=Sfin) (Gfin:=Gfin) (W:=W) (Δ:=Δ)
          hStore hDisj hDisjG_left_empty hDisjG_mid_empty hEq_mid hTS_outer hPre
      have hG₂' : G₂' = G₂_step' := by
        apply append_right_eq_of_eq
        calc
          G₁ ++ G₂' = split.G1 ++ G₂_step := by simpa using hEq'.symm
          _ = G₁ ++ G₂_step' ++ [] := hEqG'
          _ = G₁ ++ G₂_step' := by simp
      refine ⟨W', Δ', ?_, hSubW, hSubΔ⟩
      simpa [hG₂'] using hPre'
  | par_skip_left =>
      have hQ := HasTypeProcPreOut_par_skip_left hPre
      have hEqG : G₁ ++ G₂' = G₁ ++ G₂ := by
        simpa [hEq] using hEq'.symm
      have hG₂' : G₂' = G₂ := append_right_eq_of_eq hEqG
      refine ⟨W, Δ, ?_, FootprintSubset_refl, SEnvDomSubset_refl⟩
      cases hG₂'
      exact hQ
  | par_skip_right =>
      have hP := HasTypeProcPreOut_par_skip_right hPre
      have hEqG : G₁ ++ G₂' = G₁ ++ G₂ := by
        simpa [hEq] using hEq'.symm
      have hG₂' : G₂' = G₂ := append_right_eq_of_eq hEqG
      refine ⟨W, Δ, ?_, FootprintSubset_refl, SEnvDomSubset_refl⟩
      cases hG₂'
      exact hP


end
