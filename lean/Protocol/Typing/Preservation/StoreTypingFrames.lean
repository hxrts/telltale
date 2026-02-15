
import Protocol.Typing.Preservation.StoreTypingCore

/-! # Store Typing Frame Lemmas

Store typing preservation under framing and assignment operations,
maintaining `StoreTypedStrong` through typed step transitions. -/

/-
The Problem. When a typed step performs an assignment (recv or assign),
the store and SEnv are updated. We need to show `StoreTypedStrong` is
preserved through these updates in a framed context.

Solution Structure. Prove `StoreTypedStrong_frame_assign` by combining
same-domain update and value typing lift. Use SEnv rewriting to show
the framed environment has equivalent lookups.
-/

/- ## Structured Block 1 -/
set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

-- Assignment Frame Preservation

theorem StoreTypedStrong_frame_assign
    {G G₂ : GEnv} {Ssh : SEnv} {Sown : OwnedEnv} {S₂ : SEnv} {store : VarStore}
    {x : Var} {v : Value} {T : ValType} :
    StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store →
    lookupSEnv Ssh x = none →
    HasTypeVal G v T →
    StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown.updateLeft x T ++ S₂)) (updateStr store x v) := by
  intro hStore hNoSh hv
  have hvFrame : HasTypeVal (G ++ G₂) v T := by
    apply HasTypeVal_mono G (G ++ G₂) v T hv
    intro e L hLookup
    exact lookupG_append_left hLookup
  have hStrongWhole :
      StoreTypedStrong (G ++ G₂)
        (updateSEnv (SEnvAll Ssh (Sown ++ S₂)) x T) (updateStr store x v) := by
    refine ⟨?_, ?_⟩
    · exact StoreTypedStrong_sameDomain_update
        (S:=SEnvAll Ssh (Sown ++ S₂)) (store:=store) (x:=x) (T:=T) (v:=v)
          hStore.sameDomain
    · exact StoreTyped_assign_preserved
        (G:=G ++ G₂) (S:=SEnvAll Ssh (Sown ++ S₂)) (store:=store)
        (x:=x) (v:=v) (T:=T) hStore.typeCorr hvFrame
  exact StoreTypedStrong_rewriteS
    (G:=G ++ G₂)
    (S:=updateSEnv (SEnvAll Ssh (Sown ++ S₂)) x T)
    (S':=SEnvAll Ssh (Sown.updateLeft x T ++ S₂))
    (store:=updateStr store x v)
    (by
      intro y
      symm
      exact lookupSEnv_updateLeft_frame_eq_updateSEnv
        (Ssh:=Ssh) (Sown:=Sown) (S₂:=S₂) (x:=x) (T:=T) hNoSh y)
    hStrongWhole

-- Recv Frame Preservation

/-- Frame: receive updates S and G on the left under a right context. -/
theorem StoreTypedStrong_frame_recv
    {G G₂ : GEnv} {Ssh : SEnv} {Sown : OwnedEnv} {S₂ : SEnv} {store : VarStore}
    {e : Endpoint} {source : Role} {L : LocalType} {x : Var} {v : Value} {T : ValType} :
    StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store →
    lookupSEnv Ssh x = none →
    HasTypeVal G v T →
    lookupG G e = some (.recv source T L) →
    StoreTypedStrong (updateG G e L ++ G₂)
      (SEnvAll Ssh (Sown.updateLeft x T ++ S₂)) (updateStr store x v) := by
  intro hStore hNoSh hv hG
/- ## Structured Block 2 -/
  have hvFrame : HasTypeVal (G ++ G₂) v T := by
    apply HasTypeVal_mono G (G ++ G₂) v T hv
    intro ep Lt hLookup
    exact lookupG_append_left hLookup
  have hStrongWhole :
      StoreTypedStrong (updateG (G ++ G₂) e L)
        (updateSEnv (SEnvAll Ssh (Sown ++ S₂)) x T) (updateStr store x v) := by
    refine ⟨?_, ?_⟩
    · exact StoreTypedStrong_sameDomain_update
        (S:=SEnvAll Ssh (Sown ++ S₂)) (store:=store) (x:=x) (T:=T) (v:=v)
          hStore.sameDomain
    · exact StoreTyped_recv_preserved
        (G:=G ++ G₂) (S:=SEnvAll Ssh (Sown ++ S₂)) (store:=store)
        (e:=e) (L:=L) (x:=x) (v:=v) (T:=T) hStore.typeCorr hvFrame
  have hGrew :
      updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
    updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.recv source T L) (L':=L) hG
  have hStrongG :
      StoreTypedStrong (updateG G e L ++ G₂)
        (updateSEnv (SEnvAll Ssh (Sown ++ S₂)) x T) (updateStr store x v) := by
    exact StoreTypedStrong_rewriteG
      (G:=updateG (G ++ G₂) e L)
      (G':=updateG G e L ++ G₂)
      (S:=updateSEnv (SEnvAll Ssh (Sown ++ S₂)) x T)
      (store:=updateStr store x v)
      (by intro ep; simpa [hGrew])
      hStrongWhole
  exact StoreTypedStrong_rewriteS
    (G:=updateG G e L ++ G₂)
    (S:=updateSEnv (SEnvAll Ssh (Sown ++ S₂)) x T)
    (S':=SEnvAll Ssh (Sown.updateLeft x T ++ S₂))
    (store:=updateStr store x v)
    (by
      intro y
      symm
      exact lookupSEnv_updateLeft_frame_eq_updateSEnv
        (Ssh:=Ssh) (Sown:=Sown) (S₂:=S₂) (x:=x) (T:=T) hNoSh y)
    hStrongG

-- Typed-Step Preservation With Left Frame

/-- Store typing is preserved by a framed TypedStep. -/
theorem StoreTypedStrong_preserved_frame_left
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'}
    {G₂ : GEnv} {S₂ : SEnv} {Sfin Gfin W Δ} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    OwnedDisjoint Sown →
    DisjointS Sown.right Sfin.left →
    StoreTypedStrong (G' ++ G₂) (SEnvAll Ssh (Sown' ++ S₂)) store' := by
  intro hTS hStore hPre hOwnDisj hDisjRightFin
  induction hTS generalizing G₂ S₂ Sfin Gfin W Δ with
  -- # Communication Cases (Send/Recv/Select/Branch)
  | send =>
/- ## Structured Block 3 -/
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
        hk hx hG hS hv hRecvReady hEdge hGout hDout hBufsOut
      cases hPre
      · rename_i hk hG' hx
        have hStore' :
            StoreTypedStrong (updateG (G ++ G₂) e L) (SEnvAll Ssh (Sown ++ S₂)) store :=
          StoreTypedStrong_updateG (G:=G ++ G₂) (S:=SEnvAll Ssh (Sown ++ S₂))
            (store:=store) (e:=e) (L:=L) hStore
        have hGrew :
            updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
          updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.send target T L) (L':=L) hG
        simpa [hGout, hGrew] using hStore'
  -- ## Recv Case
  | recv =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
        hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut
      cases hPre with
      | recv_new hk hG' hNoSh hNoLeft =>
          have hStore' :=
            StoreTypedStrong_frame_recv (G:=G) (G₂:=G₂) (Ssh:=Ssh) (Sown:=Sown) (S₂:=S₂)
              (store:=store) (e:=e) (source:=source) (L:=L) (x:=x) (v:=v) (T:=T)
              hStore hNoSh hv hG
          simpa [hGout, hSout, hStoreOut] using hStore'
      | recv_old hk hG' hNoSh hOwn =>
          have hStore' :=
            StoreTypedStrong_frame_recv (G:=G) (G₂:=G₂) (Ssh:=Ssh) (Sown:=Sown) (S₂:=S₂)
              (store:=store) (e:=e) (source:=source) (L:=L) (x:=x) (v:=v) (T:=T)
              hStore hNoSh hv hG
          simpa [hGout, hSout, hStoreOut] using hStore'
  -- ## Select Case
  | select =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
        hk hG hFind hTargetReady hEdge hGout hDout hBufsOut
      cases hPre
      · rename_i hk hG' hFind
        have hStore' :
            StoreTypedStrong (updateG (G ++ G₂) e L) (SEnvAll Ssh (Sown ++ S₂)) store :=
          StoreTypedStrong_updateG (G:=G ++ G₂) (S:=SEnvAll Ssh (Sown ++ S₂))
            (store:=store) (e:=e) (L:=L) hStore
        have hGrew :
            updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
          updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.select target bs) (L':=L) hG
        simpa [hGout, hGrew] using hStore'
  -- ## Branch Case
  | branch =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
        hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut
      cases hPre
      · rename_i hk hG' hLen hLbl hProcs hOut hDom
        have hStore' :
            StoreTypedStrong (updateG (G ++ G₂) e L) (SEnvAll Ssh (Sown ++ S₂)) store :=
          StoreTypedStrong_updateG (G:=G ++ G₂) (S:=SEnvAll Ssh (Sown ++ S₂))
            (store:=store) (e:=e) (L:=L) hStore
/- ## Structured Block 4 -/
        have hGrew :
            updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
          updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.branch source bs) (L':=L) hG
        simpa [hGout, hGrew] using hStore'
  -- # Local Assignment and Sequencing Cases
  | assign =>
      rename_i G D Ssh Sown store bufs x v T S' store' hv hSout hStoreOut
      cases hPre with
      | assign_new hNoSh hNoOwn hvPre =>
          have hStore' :=
            StoreTypedStrong_frame_assign (G:=G) (G₂:=G₂) (Ssh:=Ssh) (Sown:=Sown) (S₂:=S₂)
              (store:=store) (x:=x) (v:=v) hStore hNoSh hv
          simpa [hSout, hStoreOut] using hStore'
      | assign_old hNoSh hOwn hvPre =>
          have hStore' :=
            StoreTypedStrong_frame_assign (G:=G) (G₂:=G₂) (Ssh:=Ssh) (Sown:=Sown) (S₂:=S₂)
              (store:=store) (x:=x) (v:=v) hStore hNoSh hv
          simpa [hSout, hStoreOut] using hStore'
  | seq_step hTS ih =>
      cases hPre with
      | seq hP hQ =>
          have hDomQ := HasTypeProcPreOut_domsubset hQ
          have hDisjRightMid := DisjointS_of_domsubset_right hDomQ hDisjRightFin
          exact ih hStore hP hOwnDisj hDisjRightMid
  | seq_skip =>
      exact hStore
  -- # Parallel Left Case
  | par_left split hSlen hTS hDisjG hDisjD hDisjS ih =>
      rename_i Ssh0 Sown0 store0 bufs0 store0' bufs0' P0 P0' Q0 G0 D₁0 D₂0 G₁0' D₁0' S₁0' nS0 nG0
      obtain ⟨pw, S₁_fin, S₂_fin, G₁_fin, G₂_fin, W₁, W₂, Δ₁, Δ₂, hSfin, hGfin, hW, hΔ,
          hDisjG_pre, hDisjS_pre, hDisjS_left_pre, hDisjS_right_pre, hDisjS_fin, hDisjW, hDisjΔ,
          hP_pre, hQ_pre⟩ :=
        HasTypeProcPreOut_par_inv_witness hPre
      let split_pre : ParSplit Sown0.left G0 := pw.split
      have hS1eq : split.S1 = split_pre.S1 := by
        simpa [split_pre] using
          (ParSplit.sides_eq_of_witness (split:=split) (pw:=pw) hSlen).1
      have hS2eq : split.S2 = split_pre.S2 := by
        simpa [split_pre] using
          (ParSplit.sides_eq_of_witness (split:=split) (pw:=pw) hSlen).2
      have hDisjS_left : DisjointS S₁_fin split.S2 := by
        simpa [hS2eq] using hDisjS_left_pre
      have hP :
          HasTypeProcPreOut Ssh0 { right := Sown0.right ++ split.S2, left := split.S1 } split_pre.G1 P0
            { right := Sown0.right ++ split.S2, left := S₁_fin } G₁_fin W₁ Δ₁ := by
        simpa [hS1eq, hS2eq] using hP_pre
      have hStore_pre :
          StoreTypedStrong (split.G1 ++ (split.G2 ++ G₂))
            (SEnvAll (Ssh0 ++ Sown0.right) ((split.S1 ++ split.S2) ++ S₂)) store0 := by
        simpa [split.hG, split.hS, SEnvAll, List.append_assoc] using hStore
      have hStore_swap :
          StoreTypedStrong (split.G1 ++ (split.G2 ++ G₂))
/- ## Structured Block 5 -/
            (SEnvAll (Ssh0 ++ Sown0.right) (split.S2 ++ (split.S1 ++ S₂))) store0 :=
        StoreTypedStrong_swap_S_left_prefix (Ssh:=Ssh0 ++ Sown0.right)
          (S₁:=split.S1) (S₂:=split.S2) (S₃:=S₂) hDisjS hStore_pre
      have hStore' :
          StoreTypedStrong (split.G1 ++ (split.G2 ++ G₂))
            (SEnvAll Ssh0 (({ right := Sown0.right ++ split.S2, left := split.S1 } : OwnedEnv) ++ S₂)) store0 := by
        simpa [SEnvAll, OwnedEnv.frameLeft, List.append_assoc] using hStore_swap
      have hStore'_ih :
          StoreTypedStrong (G0 ++ G₂)
            (SEnvAll Ssh0 (({ right := Sown0.right ++ split.S2, left := split.S1 } : OwnedEnv) ++ S₂)) store0 := by
        simpa [split.hG, List.append_assoc] using hStore'
      -- ## Left Subprocess Typing and IH Application
      have hP_full := by
        have hP_full_pre := HasTypeProcPreOut_frame_G_right_par (split:=split_pre) hDisjG_pre hP_pre
        have hP' :
            HasTypeProcPreOut Ssh0 { right := Sown0.right ++ split.S2, left := split.S1 } G0 P0
              { right := Sown0.right ++ split.S2, left := S₁_fin } (G₁_fin ++ split_pre.G2) W₁ Δ₁ := by
          simpa [hS1eq, hS2eq] using hP_full_pre
        exact hP'
      have hOwnLeftAll : DisjointS Sown0.right (split.S1 ++ split.S2) := by
        simpa [OwnedDisjoint, split.hS] using hOwnDisj
      have hDisjRightS1 : DisjointS Sown0.right split.S1 := DisjointS_split_left hOwnLeftAll
      have hOwnSubP : OwnedDisjoint ({ right := Sown0.right ++ split.S2, left := split.S1 } : OwnedEnv) :=
        DisjointS_append_left hDisjRightS1 (DisjointS_symm hDisjS)
      have hDisjRightFin' : DisjointS Sown0.right (S₁_fin ++ S₂_fin) := by
        simpa [hSfin] using hDisjRightFin
      have hDisjRightS1' : DisjointS Sown0.right S₁_fin := DisjointS_split_left hDisjRightFin'
      have hDisjOutP : DisjointS (Sown0.right ++ split.S2) S₁_fin :=
        DisjointS_append_left hDisjRightS1' (DisjointS_symm hDisjS_left)
      have hStore'' :=
        ih (G₂:=G₂) (S₂:=S₂) hStore'_ih hP_full hOwnSubP hDisjOutP
      -- ## Reassemble Framed Store Typing
      have hSubS2 : SEnvDomSubset split.S2 (Sown0.right ++ split.S2) := by
        simpa using (SEnvDomSubset_append_right (S₁:=Sown0.right) (S₂:=split.S2))
      have hDisjS' : DisjointS split.S2 S₁0' :=
        DisjointS_preserved_TypedStep_left (Sframe:=split.S2) hTS hP_full
          (DisjointS_symm hDisjS) hSubS2 hOwnSubP hDisjOutP rfl
      have hStore''_pre :
          StoreTypedStrong (G₁0' ++ (split.G2 ++ G₂))
            (SEnvAll (Ssh0 ++ Sown0.right) (split.S2 ++ (S₁0' ++ S₂))) store0' := by
        simpa [SEnvAll, OwnedEnv.frameLeft, List.append_assoc] using hStore''
      have hStore''_pre' :
          StoreTypedStrong (G₁0' ++ (split.G2 ++ G₂))
            (SEnvAll (Ssh0 ++ Sown0.right) ((split.S2 ++ S₁0') ++ S₂)) store0' := by
        simpa [List.append_assoc] using hStore''_pre
      have hStore_final :
          StoreTypedStrong (G₁0' ++ (split.G2 ++ G₂))
            (SEnvAll (Ssh0 ++ Sown0.right) (S₁0' ++ (split.S2 ++ S₂))) store0' :=
        StoreTypedStrong_swap_S_left_prefix (Ssh:=Ssh0 ++ Sown0.right)
          (S₁:=split.S2) (S₂:=S₁0') (S₃:=S₂) hDisjS' hStore''_pre'
      simpa [SEnvAll, OwnedEnv.frameLeft, List.append_assoc] using hStore_final
  -- # Parallel Right Case
  | par_right split hSlen hTS hDisjG hDisjD hDisjS ih =>
/- ## Structured Block 6 -/
      rename_i Ssh0 Sown0 store0 bufs0 store0' bufs0' P0 Q0 Q0' G0 D₁0 D₂0 G₂out0 D₂'0 S₂out0 nS0 nG0
      obtain ⟨pw, S₁_fin, S₂_fin, G₁_fin, G₂_fin, W₁, W₂, Δ₁, Δ₂, hSfin, hGfin, hW, hΔ,
          hDisjG_pre, hDisjS_pre, hDisjS_left_pre, hDisjS_right_pre, hDisjS_fin, hDisjW, hDisjΔ,
          hP_pre, hQ_pre⟩ :=
        HasTypeProcPreOut_par_inv_witness hPre
      let split_pre : ParSplit Sown0.left G0 := pw.split
      have hS1eq : split.S1 = split_pre.S1 := by
        simpa [split_pre] using
          (ParSplit.sides_eq_of_witness (split:=split) (pw:=pw) hSlen).1
      have hS2eq : split.S2 = split_pre.S2 := by
        simpa [split_pre] using
          (ParSplit.sides_eq_of_witness (split:=split) (pw:=pw) hSlen).2
      have hDisjS_right : DisjointS split.S1 S₂_fin := by
        simpa [hS1eq] using hDisjS_right_pre
      have hQ :
          HasTypeProcPreOut Ssh0 { right := Sown0.right ++ split.S1, left := split.S2 } split_pre.G2 Q0
            { right := Sown0.right ++ split.S1, left := S₂_fin } G₂_fin W₂ Δ₂ := by
        simpa [hS1eq, hS2eq] using hQ_pre
      have hStore_pre :
          StoreTypedStrong ((split.G1 ++ split.G2) ++ G₂) (SEnvAll Ssh0 (Sown0 ++ S₂)) store0 := by
        simpa [split.hG, List.append_assoc] using hStore
      have hStore'' :
          StoreTypedStrong (split.G2 ++ (split.G1 ++ G₂))
            (SEnvAll Ssh0 (({ right := Sown0.right ++ split.S1, left := split.S2 } : OwnedEnv) ++ S₂)) store0 := by
        have hStoreG :=
          StoreTypedStrong_swap_G_left (G₁:=split.G1) (G₂:=split.G2) (G₃:=G₂) hDisjG hStore_pre
        simpa [SEnvAll, OwnedEnv.frameLeft, split.hS, List.append_assoc] using hStoreG
      have hStore''_assoc :
          StoreTypedStrong ((split.G2 ++ split.G1) ++ G₂)
            (SEnvAll Ssh0 (({ right := Sown0.right ++ split.S1, left := split.S2 } : OwnedEnv) ++ S₂)) store0 := by
        simpa [List.append_assoc] using hStore''
      have hStore''_swap :
          StoreTypedStrong ((split.G1 ++ split.G2) ++ G₂)
            (SEnvAll Ssh0 (({ right := Sown0.right ++ split.S1, left := split.S2 } : OwnedEnv) ++ S₂)) store0 := by
        have hSwap :=
          StoreTypedStrong_swap_G_left (G₁:=split.G2) (G₂:=split.G1) (G₃:=G₂)
            (DisjointG_symm hDisjG) hStore''_assoc
        simpa [List.append_assoc] using hSwap
      have hStore''_ih :
          StoreTypedStrong (G0 ++ G₂)
            (SEnvAll Ssh0 (({ right := Sown0.right ++ split.S1, left := split.S2 } : OwnedEnv) ++ S₂)) store0 := by
        simpa [split.hG, List.append_assoc] using hStore''_swap
      -- ## Right Subprocess Typing and IH Application
      have hOwnLeftAll : DisjointS Sown0.right (split.S1 ++ split.S2) := by
        simpa [OwnedDisjoint, split.hS] using hOwnDisj
      have hDisjRightS2 : DisjointS Sown0.right split.S2 := DisjointS_split_right hOwnLeftAll
      have hDisjInQ : DisjointS (Sown0.right ++ split.S1) split.S2 :=
        DisjointS_append_left hDisjRightS2 hDisjS
      have hOwnSubQ : OwnedDisjoint ({ right := Sown0.right ++ split.S1, left := split.S2 } : OwnedEnv) :=
        DisjointS_append_left hDisjRightS2 hDisjS
      have hDisjRightFin' : DisjointS Sown0.right (S₁_fin ++ S₂_fin) := by
/- ## Structured Block 7 -/
        simpa [hSfin] using hDisjRightFin
      have hDisjRightS2' : DisjointS Sown0.right S₂_fin := DisjointS_split_right hDisjRightFin'
      have hDisjOutQ : DisjointS (Sown0.right ++ split.S1) S₂_fin :=
        DisjointS_append_left hDisjRightS2' hDisjS_right
      have hQ_full := by
        have hQ_full_pre := HasTypeProcPreOut_frame_G_left_par (split:=split_pre) hDisjG_pre
          (by simpa [hS1eq, hS2eq] using hDisjInQ) hQ_pre
          (by simpa [hS1eq, hS2eq] using hDisjOutQ)
        have hQ' :
            HasTypeProcPreOut Ssh0 { right := Sown0.right ++ split.S1, left := split.S2 } G0 Q0
              { right := Sown0.right ++ split.S1, left := S₂_fin } (split_pre.G1 ++ G₂_fin) W₂ Δ₂ := by
          simpa [hS1eq, hS2eq] using hQ_full_pre
        exact hQ'
      -- ## Finish Parallel Right Reconstruction
      have hStore''' :=
        ih (G₂:=G₂) (S₂:=S₂) hStore''_ih hQ_full hOwnSubQ hDisjOutQ
      simpa [SEnvAll, OwnedEnv.frameLeft, List.append_assoc] using hStore'''
  | par_skip_left =>
      exact hStore
  | par_skip_right =>
      exact hStore

-- Unframed Corollary

/-- Store typing is preserved by TypedStep. -/
theorem StoreTypedStrong_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'}
    {Sfin Gfin W Δ} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    StoreTypedStrong G (SEnvAll Ssh Sown) store →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    OwnedDisjoint Sown →
    DisjointS Sown.right Sfin.left →
    StoreTypedStrong G' (SEnvAll Ssh Sown') store' := by
  -- Use the frame lemma with empty right context.
  intro hTS hStore hPre hOwnDisj hDisjRightFin
  have hStore' :
      StoreTypedStrong (G ++ (∅ : GEnv)) (SEnvAll Ssh (Sown ++ (∅ : SEnv))) store := by
    simpa [SEnvAll, List.append_nil] using hStore
  simpa [SEnvAll, List.append_nil] using
    (StoreTypedStrong_preserved_frame_left (G₂:=(∅ : GEnv)) (S₂:=(∅ : SEnv))
      hTS hStore' hPre hOwnDisj hDisjRightFin)


end
