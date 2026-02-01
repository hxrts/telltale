import Protocol.Typing.Preservation

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

/-! ### Progress Helpers -/

private theorem findLabel_eq {α : Type} {lbl lbl' : Label} {xs : List (Label × α)} {v : α}
    (h : xs.find? (fun b => b.1 == lbl) = some (lbl', v)) : lbl' = lbl := by
  have hPred : (lbl' == lbl) := (List.find?_eq_some_iff_append (xs := xs)
    (p := fun b => b.1 == lbl) (b := (lbl', v))).1 h |>.1
  have hPred' : (lbl' == lbl) = true := by
    simpa using hPred
  exact (beq_iff_eq).1 hPred'

def BlockedProc (store : Store) (bufs : Buffers) : Process → Prop
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
  | .par P Q =>
      BlockedProc store bufs P ∧ BlockedProc store bufs Q
  | _ => False

private lemma DisjointS_right_empty (S : SEnv) : DisjointS S (∅ : SEnv) := by
  intro x T₁ T₂ hL1 hL2
  have : lookupSEnv (∅ : SEnv) x = none := lookupSEnv_empty x
  cases hL2

private lemma DisjointS_left_empty (S : SEnv) : DisjointS (∅ : SEnv) S := by
  intro x T₁ T₂ hL1 hL2
  have : lookupSEnv (∅ : SEnv) x = none := lookupSEnv_empty x
  cases hL1

private lemma SessionsOf_empty : SessionsOf ([] : GEnv) = ∅ := by
  ext s; constructor
  · intro h
    rcases h with ⟨e, L, hLookup, hSid⟩
    simp [lookupG] at hLookup
  · intro h
    cases h

private lemma DisjointG_right_empty (G : GEnv) : DisjointG G [] := by
  simp [DisjointG, GEnvDisjoint, SessionsOf_empty]

private lemma DisjointG_left_empty (G : GEnv) : DisjointG [] G := by
  simp [DisjointG, GEnvDisjoint, SessionsOf_empty]

private lemma DEnv_find_empty (e : Edge) : (∅ : DEnv).find? e = none := by
  rfl

private lemma SessionsOfD_empty : SessionsOfD (∅ : DEnv) = ∅ := by
  ext s; constructor
  · intro h
    rcases h with ⟨e, ts, hFind, hSid⟩
    have : (∅ : DEnv).find? e = none := DEnv_find_empty e
    cases hFind
  · intro h
    cases h

private lemma DisjointD_right_empty (D : DEnv) : DisjointD D (∅ : DEnv) := by
  simp [DisjointD, SessionsOfD_empty]

private lemma DisjointD_left_empty (D : DEnv) : DisjointD (∅ : DEnv) D := by
  simp [DisjointD, SessionsOfD_empty]

private lemma DConsistent_empty (G : GEnv) : DConsistent G (∅ : DEnv) := by
  simp [DConsistent, SessionsOfD_empty]

private theorem DEnv_append_empty_right (D : DEnv) : D ++ (∅ : DEnv) = D :=
  DEnvUnion_empty_right D

private theorem DEnv_append_empty_left (D : DEnv) : (∅ : DEnv) ++ D = D :=
  DEnvUnion_empty_left D

private lemma SEnv_append_empty_right (S : SEnv) : S ++ (∅ : SEnv) = S := by
  simpa using (List.append_nil S)

private lemma SEnv_append_empty_left (S : SEnv) : (∅ : SEnv) ++ S = S := by
  simpa using (List.nil_append S)

private theorem progress_typed_aux {G D Ssh Sown store bufs P Sfin Gfin W Δ} :
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    StoreTypedStrong G (SEnvAll Ssh Sown) store →
    BuffersTyped G D bufs →
    Coherent G D →
    HeadCoherent G D →
    ValidLabels G D bufs →
    SendReady G D →
    SelectReady G D →
    DConsistent G D →
    (P = .skip) ∨
      (∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs P
        G' D' Sown' store' bufs' P') ∨
      BlockedProc store bufs P := by
  intro hOut hStore hBufs hCoh hHead hValid hReady hSelectReady hCons
  cases P with
  | skip =>
      left; rfl
  | send k x =>
      cases hOut with
      | send hk hG hx =>
          rename_i e q T L
          right; left
          obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
          have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
          subst hkChan
          obtain ⟨v, hxStr, hv⟩ := store_lookup_of_senv_lookup hStore hx
          have hRecvReady := hReady e q T L hG
          exact ⟨_, _, _, _, _, _, TypedStep.send hkStr hxStr hG hx hv hRecvReady rfl rfl rfl rfl⟩
  | recv k x =>
      cases hOut with
      | recv_new hk hG hNoSh hNoOwn =>
          rename_i e p T L
          obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
          have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
          subst hkChan
          set recvEdge : Edge := { sid := e.sid, sender := p, receiver := e.role }
          cases hBuf : lookupBuf bufs recvEdge with
          | nil =>
              right; right
              refine ⟨e, p, hkStr, ?_⟩
              simpa [recvEdge, hBuf]
          | cons v vs =>
              right; left
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
                  have hHeadEdge := hHead recvEdge
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
          obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
          have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
          subst hkChan
          set recvEdge : Edge := { sid := e.sid, sender := p, receiver := e.role }
          cases hBuf : lookupBuf bufs recvEdge with
          | nil =>
              right; right
              refine ⟨e, p, hkStr, ?_⟩
              simpa [recvEdge, hBuf]
          | cons v vs =>
              right; left
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
                  have hHeadEdge := hHead recvEdge
                  have hEq : T = T' := by
                    simpa [HeadCoherent, hG, recvEdge, hTrace] using hHeadEdge
                  have hEq' : T' = T := by
                    simpa using hEq.symm
                  have hv : HasTypeVal G v T := by
                    simpa [hTrace, hEq'] using hv'
                  have hTraceHead : (lookupD D recvEdge).head? = some T := by
                    simp [hTrace, hEq]
                  exact ⟨_, _, _, _, _, _, TypedStep.recv hkStr hG rfl hBuf hv hTraceHead rfl rfl rfl rfl rfl⟩
  | select k ℓ =>
      cases hOut with
      | select hk hG hbs =>
          rename_i e q bs L
          right; left
          obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
          have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
          subst hkChan
          have hTargetReady := hSelectReady e q bs ℓ L hG hbs
          exact ⟨_, _, _, _, _, _, TypedStep.select hkStr hG hbs hTargetReady rfl rfl rfl rfl⟩
  | branch k procs =>
      cases hOut with
      | branch hk hG hLen hLabels hBodies hOutLbl hDom =>
          rename_i e p bs
          obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
          have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
          subst hkChan
          set branchEdge : Edge := { sid := e.sid, sender := p, receiver := e.role }
          cases hBuf : lookupBuf bufs branchEdge with
          | nil =>
              right; right
              refine ⟨e, p, hkStr, ?_⟩
              simpa [branchEdge, hBuf]
          | cons v vs =>
              right; left
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
                  have hHeadEdge := hHead branchEdge
                  have hEq : T' = .string := by
                    simpa [HeadCoherent, hG, branchEdge, hTrace] using hHeadEdge
                  have hv := by
                    simpa [hTrace, hEq] using hv'
                  cases hv with
                  | string lbl =>
                      have hValidEdge := hValid branchEdge p bs (by simpa [branchEdge] using hG)
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
  | seq P Q =>
      cases hOut with
      | seq hP hQ =>
          have hProgP :=
            progress_typed_aux hP hStore hBufs hCoh hHead hValid hReady hSelectReady hCons
          cases hProgP with
          | inl hSkip =>
              right; left
              subst hSkip
              exact ⟨_, _, _, store, bufs, Q, TypedStep.seq_skip⟩
          | inr hRest =>
              cases hRest with
              | inl hStep =>
                  rcases hStep with ⟨G', D', S', store', bufs', P', hStep⟩
                  right; left
                  exact ⟨_, _, _, _, _, _, TypedStep.seq_step hStep⟩
              | inr hBlocked =>
                  right; right
                  simpa [BlockedProc] using hBlocked
  | par P Q =>
      cases hOut with
      | par split hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS' hDisjW hDisjΔ hP hQ =>
          rename_i S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂
          have hDisjS_symm : DisjointS split.S2 split.S1 := DisjointS_symm hDisjS
          -- Frame each side to the full environment to reuse the global invariants.
          have hP_full :
              HasTypeProcPreOut Ssh Sown G P (S₁' ++ split.S2) (G₁' ++ split.G2) W₁ Δ₁ := by
            have hFrame :=
              HasTypeProcPreOut_frame_right (S₁:=split.S1) (S₂:=split.S2) (G₁:=split.G1) (G₂:=split.G2)
                (S₁':=S₁') (G₁':=G₁') (W:=W₁) (Δ:=Δ₁) hDisjS_symm (DisjointS_symm hDisjS_left) hDisjG hP
            simpa [split.hS, split.hG] using hFrame
          have hProgP :=
            progress_typed_aux hP_full hStore hBufs hCoh hHead hValid hReady hSelectReady hCons
          cases hProgP with
          | inl hSkip =>
              right; left
              subst hSkip
              exact ⟨_, _, _, store, bufs, Q, TypedStep.par_skip_left⟩
          | inr hRest =>
              cases hRest with
              | inl hStep =>
                  rcases hStep with ⟨G', D', Sown', store', bufs', P', hStep⟩
                  -- Give all resources to the left to lift the step into parallel.
                  let splitLeft : ParSplit Sown G :=
                    { S1 := Sown, S2 := (∅ : SEnv), G1 := G, G2 := ([] : GEnv),
                      hS := by
                        simpa [SEnv_append_empty_right]
                      hG := by
                        simp }
                  have hDisjG_left : DisjointG splitLeft.G1 splitLeft.G2 :=
                    DisjointG_right_empty G
                  have hDisjS_left : DisjointS splitLeft.S1 splitLeft.S2 :=
                    DisjointS_right_empty Sown
                  have hDisjD_left : DisjointD D (∅ : DEnv) :=
                    DisjointD_right_empty D
                  have hConsRight : DConsistent splitLeft.G2 (∅ : DEnv) :=
                    DConsistent_empty splitLeft.G2
                  have hStep' :
                      TypedStep splitLeft.G1 D Ssh splitLeft.S1 store bufs P
                        G' D' Sown' store' bufs' P' := by
                    simpa [splitLeft] using hStep
                  right; left
                  have hPar :=
                    TypedStep.par_left (Ssh:=Ssh) (store:=store) (bufs:=bufs) (store':=store') (bufs':=bufs')
                      (P:=P) (P':=P') (Q:=Q) (S:=Sown) (G:=G) (D₁:=D) (D₂:=(∅ : DEnv))
                      (G₁':=G') (D₁':=D') (S₁':=Sown')
                      splitLeft hStep' hDisjG_left hDisjD_left hDisjS_left hCons hConsRight
                  have hPar' :
                      TypedStep G D Ssh Sown store bufs (.par P Q)
                        (G' ++ []) (D' ++ (∅ : DEnv)) (Sown' ++ (∅ : SEnv)) store' bufs' (.par P' Q) := by
                    simpa [DEnv_append_empty_right, splitLeft] using hPar
                  exact ⟨_, _, _, _, _, _, hPar'⟩
              | inr hBlocked =>
                  -- Left is blocked; check the right side.
                  have hQ_full :
                      HasTypeProcPreOut Ssh Sown G Q (split.S1 ++ S₂') (split.G1 ++ G₂') W₂ Δ₂ := by
                    have hFrame :=
                      HasTypeProcPreOut_frame_left (S₁:=split.S1) (S₂:=split.S2) (G₁:=split.G1) (G₂:=split.G2)
                        (S₂':=S₂') (G₂':=G₂') (W:=W₂) (Δ:=Δ₂) hDisjS hDisjS_right hDisjG hQ
                    simpa [split.hS, split.hG] using hFrame
                  have hProgQ :=
                    progress_typed_aux hQ_full hStore hBufs hCoh hHead hValid hReady hSelectReady hCons
                  cases hProgQ with
                  | inl hSkipQ =>
                      right; left
                      subst hSkipQ
                      exact ⟨_, _, _, store, bufs, P, TypedStep.par_skip_right⟩
                  | inr hRestQ =>
                      cases hRestQ with
                      | inl hStepQ =>
                          rcases hStepQ with ⟨G', D', Sown', store', bufs', Q', hStep⟩
                          -- Give all resources to the right to lift the step into parallel.
                          let splitRight : ParSplit Sown G :=
                            { S1 := (∅ : SEnv), S2 := Sown, G1 := ([] : GEnv), G2 := G,
                              hS := by
                                simpa [SEnv_append_empty_left]
                              hG := by
                                simp }
                          have hDisjG_right : DisjointG splitRight.G1 splitRight.G2 :=
                            DisjointG_left_empty G
                          have hDisjS_right : DisjointS splitRight.S1 splitRight.S2 :=
                            DisjointS_left_empty Sown
                          have hDisjD_right : DisjointD (∅ : DEnv) D :=
                            DisjointD_left_empty D
                          have hConsLeft : DConsistent splitRight.G1 (∅ : DEnv) :=
                            DConsistent_empty splitRight.G1
                          have hStep' :
                              TypedStep splitRight.G2 D Ssh splitRight.S2 store bufs Q
                                G' D' Sown' store' bufs' Q' := by
                            simpa [splitRight] using hStep
                          right; left
                          have hPar :=
                            TypedStep.par_right (Ssh:=Ssh) (store:=store) (bufs:=bufs) (store':=store') (bufs':=bufs')
                              (P:=P) (Q:=Q) (Q':=Q') (S:=Sown) (G:=G) (D₁:=(∅ : DEnv)) (D₂:=D)
                              (G₂':=G') (D₂':=D') (S₂':=Sown')
                              splitRight hStep' hDisjG_right hDisjD_right hDisjS_right hConsLeft hCons
                          have hPar' :
                              TypedStep G D Ssh Sown store bufs (.par P Q)
                                ([] ++ G') ((∅ : DEnv) ++ D') ((∅ : SEnv) ++ Sown') store' bufs' (.par P Q') := by
                            simpa [DEnv_append_empty_left, splitRight] using hPar
                          exact ⟨_, _, _, _, _, _, hPar'⟩
                      | inr hBlockedQ =>
                          right; right
                          exact ⟨hBlocked, hBlockedQ⟩
  | newSession roles f P =>
      cases hOut
  | assign x v =>
      cases hOut with
      | assign_new hNoSh hNoOwn hv =>
          rename_i T
          right; left
          exact ⟨_, _, _, _, _, _, TypedStep.assign hv rfl rfl⟩
      | assign_old hNoSh hOwn hv =>
          rename_i T
          right; left
          exact ⟨_, _, _, _, _, _, TypedStep.assign hv rfl rfl⟩

/-- Progress theorem: A well-formed process can either step or is in a final/blocked state.

    **Proof strategy**: Case analysis on process P:
    - `skip`: Terminates
    - `send k x`: Derive TypedStep.send from lookupG via HasTypeProcPre inversion
    - `recv k x`: Check buffer - if non-empty, derive TypedStep.recv; else blocked
    - `seq P Q`: Use IH on P or skip elimination
    - `par P Q`: Use IH on P or Q or skip elimination -/
theorem progress_typed {G D Ssh Sown store bufs P} :
    LocalTypeR.WellFormed G D Ssh Sown store bufs P →
    (P = .skip) ∨
    (∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs P
      G' D' Sown' store' bufs' P') ∨
    BlockedProc store bufs P := by
  intro hWF
  unfold LocalTypeR.WellFormed at hWF
  obtain ⟨hStore, hBufs, hCoh, hHead, hValid, hCompat, hDisjS, hCons, hPreOut⟩ := hWF
  obtain ⟨Sfin, Gfin, Wfin, Δfin, hOut⟩ := hPreOut
  have hReady : SendReady G D := Compatible_to_SendReady hCompat
  have hSelectReady : SelectReady G D := Compatible_to_SelectReady hCompat
  exact progress_typed_aux hOut hStore hBufs hCoh hHead hValid hReady hSelectReady hCons

/-  Subject reduction (soundness) theorem moved to Protocol.Preservation
    to avoid circular dependency (Step is defined in Semantics which imports Typing).

    **Theorem**: TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
                 Step ⟨P, store, bufs, G, D, n⟩ ⟨P', store', bufs', G', D', n⟩

    This will be proven in Preservation.lean after TypedStep is available. -/

end
