import Protocol.Typing.Progress.TypedStepFrames

/-! # Local Progress Cases

Per-constructor progress lemmas showing that well-typed send, recv,
select, and branch processes can step given appropriate readiness. -/

/-
The Problem. Progress requires showing that each process constructor
can produce a `TypedStep` when the configuration is well-typed and
the relevant readiness conditions hold (buffers non-empty for recv,
receivers ready for send, etc.).

Solution Structure. Prove `progress_send`, `progress_recv`,
`progress_select`, `progress_branch` by extracting the endpoint
from typing, looking up the store value, and constructing the step.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ## Send Progress -/

lemma progress_send
    {G D Ssh Sown store bufs k x Sfin Gfin W Δ} :
    HasTypeProcPreOut Ssh Sown G (.send k x) Sfin Gfin W Δ →
    StoreTypedStrong G (SEnvAll Ssh Sown) store →
    DisjointS Ssh (Sown : SEnv) →
    OwnedDisjoint Sown →
    SendReady G D →
    ∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs (.send k x)
      G' D' Sown' store' bufs' P' := by
  intro hOut hStore hDisjShAll hOwnDisj hReady
  cases hOut with
  | send hk hG hx =>
      rename_i e q T L
      obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_visible_lookup hStore hDisjShAll hOwnDisj hk
      have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
      subst hkChan
      obtain ⟨v, hxStr, hv⟩ := store_lookup_of_visible_lookup hStore hDisjShAll hOwnDisj hx
      have hxAll : lookupSEnv (SEnvAll Ssh Sown) x = some T :=
        lookupSEnv_all_of_visible (Ssh:=Ssh) (Sown:=Sown) (x:=x) (T:=T) hDisjShAll hOwnDisj hx
      have hRecvReady := hReady e q T L hG
      exact ⟨_, _, _, _, _, _, TypedStep.send hkStr hxStr hG hxAll hv hRecvReady rfl rfl rfl rfl⟩

lemma progress_recv
    {G D Ssh Sown store bufs k x Sfin Gfin W Δ} :
    HasTypeProcPreOut Ssh Sown G (.recv k x) Sfin Gfin W Δ →
    StoreTypedStrong G (SEnvAll Ssh Sown) store →
    DisjointS Ssh (Sown : SEnv) →
    OwnedDisjoint Sown →
    BuffersTyped G D bufs →
    HeadCoherent G D →
    RoleComplete G →
    (∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs (.recv k x)
      G' D' Sown' store' bufs' P') ∨
    BlockedProc store bufs (.recv k x) := by
  intro hOut hStore hDisjShAll hOwnDisj hBufs hHead hComplete
  cases hOut with
  | recv_new hk hG hNoSh hNoOwnL =>
      rename_i e p T L
      obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_visible_lookup hStore hDisjShAll hOwnDisj hk
      have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
      subst hkChan
      set recvEdge : Edge := { sid := e.sid, sender := p, receiver := e.role }
      have hActiveRecv : ActiveEdge G recvEdge := by
        have hGrecv : lookupG G { sid := recvEdge.sid, role := recvEdge.receiver } = some (.recv p T L) := by
          simpa [recvEdge] using hG
        rcases RoleComplete_recv hComplete hG with ⟨Lsender, hGsender⟩
        exact ActiveEdge_of_endpoints (e:=recvEdge) hGsender hGrecv
      cases hBuf : lookupBuf bufs recvEdge with
      | nil =>
          right
          refine ⟨e, p, hkStr, ?_⟩
          simpa [recvEdge, hBuf]
      | cons v vs =>
          left
          have hTypedEdge := hBufs recvEdge
          rcases hTypedEdge with ⟨hLen, hTyping⟩
          have h0buf : 0 < (lookupBuf bufs recvEdge).length := by
            simp [hBuf]
          have h0trace : 0 < (lookupD D recvEdge).length := by
            simpa [hLen] using h0buf
          have hTyped0 := hTyping 0 h0buf
          have hv' := by
            simpa [hBuf] using hTyped0
          cases hTrace : lookupD D recvEdge with
          | nil =>
              simp [hTrace] at h0trace
          | cons T' ts =>
              have hHeadEdge := hHead recvEdge hActiveRecv
              have hEq : T = T' := by
                simpa [HeadCoherent, hG, recvEdge, hTrace] using hHeadEdge
              have hEq' : T' = T := by
                simpa using hEq.symm
              have hv : HasTypeVal G v T := by
                simpa [hTrace, hEq'] using hv'
              have hTraceHead : (lookupD D recvEdge).head? = some T := by
                simp [hTrace, hEq]
              exact ⟨_, _, _, _, _, _, TypedStep.recv hkStr hG rfl hBuf hv hTraceHead rfl rfl rfl rfl rfl⟩
  | recv_old hk hG hNoSh hOwn =>
      rename_i e p T L T'
      obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_visible_lookup hStore hDisjShAll hOwnDisj hk
      have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
      subst hkChan
      set recvEdge : Edge := { sid := e.sid, sender := p, receiver := e.role }
      have hActiveRecv : ActiveEdge G recvEdge := by
        have hGrecv : lookupG G { sid := recvEdge.sid, role := recvEdge.receiver } = some (.recv p T L) := by
          simpa [recvEdge] using hG
        rcases RoleComplete_recv hComplete hG with ⟨Lsender, hGsender⟩
        exact ActiveEdge_of_endpoints (e:=recvEdge) hGsender hGrecv
      cases hBuf : lookupBuf bufs recvEdge with
      | nil =>
          right
          refine ⟨e, p, hkStr, ?_⟩
          simpa [recvEdge, hBuf]
      | cons v vs =>
          left
          have hTypedEdge := hBufs recvEdge
          rcases hTypedEdge with ⟨hLen, hTyping⟩
          have h0buf : 0 < (lookupBuf bufs recvEdge).length := by
            simp [hBuf]
          have h0trace : 0 < (lookupD D recvEdge).length := by
            simpa [hLen] using h0buf
          have hTyped0 := hTyping 0 h0buf
          have hv' := by
            simpa [hBuf] using hTyped0
          cases hTrace : lookupD D recvEdge with
          | nil =>
              simp [hTrace] at h0trace
          | cons T' ts =>
              have hHeadEdge := hHead recvEdge hActiveRecv
              have hEq : T = T' := by
                simpa [HeadCoherent, hG, recvEdge, hTrace] using hHeadEdge
              have hEq' : T' = T := by
                simpa using hEq.symm
              have hv : HasTypeVal G v T := by
                simpa [hTrace, hEq'] using hv'
              have hTraceHead : (lookupD D recvEdge).head? = some T := by
                simp [hTrace, hEq]
              exact ⟨_, _, _, _, _, _, TypedStep.recv hkStr hG rfl hBuf hv hTraceHead rfl rfl rfl rfl rfl⟩

lemma progress_select
    {G D Ssh Sown store bufs k ℓ Sfin Gfin W Δ} :
    HasTypeProcPreOut Ssh Sown G (.select k ℓ) Sfin Gfin W Δ →
    StoreTypedStrong G (SEnvAll Ssh Sown) store →
    DisjointS Ssh (Sown : SEnv) →
    OwnedDisjoint Sown →
    SelectReady G D →
    ∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs (.select k ℓ)
      G' D' Sown' store' bufs' P' := by
  intro hOut hStore hDisjShAll hOwnDisj hSelectReady
  cases hOut with
  | select hk hG hbs =>
      rename_i e q bs L
      obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_visible_lookup hStore hDisjShAll hOwnDisj hk
      have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
      subst hkChan
      have hTargetReady := hSelectReady e q bs ℓ L hG hbs
      exact ⟨_, _, _, _, _, _, TypedStep.select hkStr hG hbs hTargetReady rfl rfl rfl rfl⟩

lemma progress_branch
    {G D Ssh Sown store bufs k procs Sfin Gfin W Δ} :
    HasTypeProcPreOut Ssh Sown G (.branch k procs) Sfin Gfin W Δ →
    StoreTypedStrong G (SEnvAll Ssh Sown) store →
    DisjointS Ssh (Sown : SEnv) →
    OwnedDisjoint Sown →
    BuffersTyped G D bufs →
    HeadCoherent G D →
    ValidLabels G D bufs →
    RoleComplete G →
    (∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs (.branch k procs)
      G' D' Sown' store' bufs' P') ∨
    BlockedProc store bufs (.branch k procs) := by
  intro hOut hStore hDisjShAll hOwnDisj hBufs hHead hValid hComplete
  cases hOut with
  | branch hk hG hLen hLabels hBodies hOutLbl hSess hDom hRight =>
      rename_i e p bs
      obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_visible_lookup hStore hDisjShAll hOwnDisj hk
      have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
      subst hkChan
      set branchEdge : Edge := { sid := e.sid, sender := p, receiver := e.role }
      have hActiveBranch : ActiveEdge G branchEdge := by
        have hGrecv : lookupG G { sid := branchEdge.sid, role := branchEdge.receiver } =
            some (.branch p bs) := by
          simpa [branchEdge] using hG
        rcases RoleComplete_branch hComplete hG with ⟨Lsender, hGsender⟩
        exact ActiveEdge_of_endpoints (e:=branchEdge) hGsender hGrecv
      cases hBuf : lookupBuf bufs branchEdge with
      | nil =>
          right
          refine ⟨e, p, hkStr, ?_⟩
          simpa [branchEdge, hBuf]
      | cons v vs =>
          left
          have hTypedEdge := hBufs branchEdge
          rcases hTypedEdge with ⟨hLenBuf, hTyping⟩
          have h0buf : 0 < (lookupBuf bufs branchEdge).length := by
            simp [hBuf]
          have h0trace : 0 < (lookupD D branchEdge).length := by
            simpa [hLenBuf] using h0buf
          have hTyped0 := hTyping 0 h0buf
          have hv' := by
            simpa [hBuf] using hTyped0
          cases hTrace : lookupD D branchEdge with
          | nil =>
              simp [hTrace] at h0trace
          | cons T' ts =>
              have hHeadEdge := hHead branchEdge hActiveBranch
              have hEq : T' = .string := by
                simpa [HeadCoherent, hG, branchEdge, hTrace] using hHeadEdge
              have hv := by
                simpa [hTrace, hEq] using hv'
              cases hv with
              | string lbl =>
                  have hValidEdge := hValid branchEdge p bs hActiveBranch
                    (by simpa [branchEdge] using hG)
                  have hBsSome : (bs.find? (fun b => b.1 == lbl)).isSome := by
                    simpa [hBuf] using hValidEdge
                  rcases (Option.isSome_iff_exists).1 hBsSome with ⟨b, hFindBs⟩
                  cases b with
                  | mk lbl' L =>
                      have hLbl : lbl' = lbl :=
                        findLabel_eq (xs := bs) (lbl := lbl) (lbl' := lbl') (v := L) hFindBs
                      subst lbl'
                      have hMemBs : (lbl, L) ∈ bs := List.mem_of_find?_eq_some hFindBs
                      rcases (List.mem_iff_getElem).1 hMemBs with ⟨i, hi, hGetBs⟩
                      have hip : i < procs.length := by
                        simpa [hLen] using hi
                      have hLabelAt : (procs.get ⟨i, hip⟩).1 = lbl := by
                        have hLblEq := hLabels i hi hip
                        simpa [hGetBs] using hLblEq
                      have hPred : (fun b => b.1 == lbl) (procs.get ⟨i, hip⟩) := by
                        exact (beq_iff_eq).2 hLabelAt
                      have hFindPIsSome : (procs.find? (fun b => b.1 == lbl)).isSome := by
                        cases hFindP : procs.find? (fun b => b.1 == lbl) with
                        | none =>
                            have hNo : ∀ x ∈ procs, ¬ (fun b => b.1 == lbl) x := by
                              simpa [List.find?_eq_none] using hFindP
                            have hMemP : procs.get ⟨i, hip⟩ ∈ procs := List.get_mem procs ⟨i, hip⟩
                            have hContra : False := (hNo _ hMemP) hPred
                            simpa using hContra
                        | some b =>
                            simp
                      rcases (Option.isSome_iff_exists).1 hFindPIsSome with ⟨bP, hFindP⟩
                      cases bP with
                      | mk lblP P =>
                          have hLblP : lblP = lbl :=
                            findLabel_eq (xs := procs) (lbl := lbl) (lbl' := lblP) (v := P) hFindP
                          subst hLblP
                          have hTraceHead : (lookupD D branchEdge).head? = some .string := by
                            simp [hTrace, hEq]
                          exact ⟨_, _, _, _, _, _, TypedStep.branch hkStr hG rfl hBuf hFindP hFindBs hTraceHead rfl rfl rfl⟩

lemma progress_assign
    {G D Ssh Sown store bufs x v Sfin Gfin W Δ} :
    HasTypeProcPreOut Ssh Sown G (.assign x v) Sfin Gfin W Δ →
    ∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs (.assign x v)
      G' D' Sown' store' bufs' P' := by
  intro hOut
  cases hOut with
  | assign_new hNoSh hNoOwnL hv =>
      exact ⟨_, _, _, _, _, _, TypedStep.assign hv rfl rfl⟩
  | assign_old hNoSh hOwn hv =>
      exact ⟨_, _, _, _, _, _, TypedStep.assign hv rfl rfl⟩


end
