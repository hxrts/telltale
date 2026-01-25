import Effects.Process
import Effects.Coherence

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

private def BlockedProc (store : Store) (bufs : Buffers) : Process → Prop
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

private theorem progress_typed_aux {G D Ssh Sown store bufs P Sfin Gfin W Δ} :
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    StoreTypedStrong G (SEnvAll Ssh Sown) store →
    BuffersTyped G D bufs →
    Coherent G D →
    HeadCoherent G D →
    ValidLabels G D bufs →
    SendReady G D →
    SelectReady G D →
    (P = .skip) ∨
      (∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs P
        G' D' Sown' store' bufs' P') ∨
      BlockedProc store bufs P := by
  intro hOut hStore hBufs hCoh hHead hValid hReady hSelectReady
  induction hOut with
  | skip =>
      left; rfl
  | send hk hG hx =>
      rename_i G k x e q T L
      -- Have: lookupSEnv S k = some (.chan e.sid e.role), lookupG G e = some (.send q T L), lookupSEnv S x = some T
      -- Need: Construct TypedStep.send with all preconditions
      --   - lookupStr store k = some (.chan e) from StoreTyped + hk
      --   - lookupStr store x = some v from StoreTyped + hx
      --   - HasTypeVal G v T from StoreTyped
      --   - hRecvReady from Coherent (receiver can consume message)
      right; left
      -- Use strong store typing to extract channel/value from store.
      obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
      have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
      subst hkChan
      obtain ⟨v, hxStr, hv⟩ := store_lookup_of_senv_lookup hStore hx
      -- Need receiver readiness to build TypedStep.send
      have hRecvReady := hReady e q T L hG
      exact ⟨_, _, _, _, _, _, TypedStep.send hkStr hxStr hG hx hv hRecvReady rfl rfl rfl rfl⟩
  | recv_new hk hG hNoSh hNoOwn =>
      rename_i G k x e p T L
      -- Have: lookupSEnv S k = some (.chan e.sid e.role), lookupG G e = some (.recv p T L)
      -- Need: Check if buffer is non-empty at edge
      --   - If lookupBuf bufs edge = v :: vs, construct TypedStep.recv
      --   - Else blocked (third alternative in progress conclusion)
      -- Derive the channel value from the store.
      obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
      have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
      subst hkChan
      -- Inspect the buffer at the receive edge.
      set recvEdge : Edge := { sid := e.sid, sender := p, receiver := e.role }
      cases hBuf : lookupBuf bufs recvEdge with
      | nil =>
          -- Blocked receive: buffer empty.
          right; right
          refine ⟨e, p, hkStr, ?_⟩
          simpa [recvEdge, hBuf]
      | cons v vs =>
          -- Buffer non-empty: can receive.
          right; left
          -- Use BuffersTyped to get value type from trace head.
          have hTypedEdge := hBufs recvEdge
          rcases hTypedEdge with ⟨hLen, hTyping⟩
          have h0buf : 0 < (lookupBuf bufs recvEdge).length := by
            simp [hBuf]
          have h0trace : 0 < (lookupD D recvEdge).length := by
            simpa [hLen] using h0buf
          have hTyped0 := hTyping 0 h0buf
          have hv' := by
            simpa [hBuf] using hTyped0
          -- Use HeadCoherent to align the trace head with T.
          cases hTrace : lookupD D recvEdge with
          | nil =>
              -- Contradiction: trace must be non-empty if buffer is non-empty.
              simp [hTrace] at h0trace
          | cons T' ts =>
              have hHeadEdge := hHead recvEdge
              -- HeadCoherent gives T = T' for recv types.
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
      rename_i G k x e p T L T'
      -- same proof as recv_new
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
  | select hk hG hbs =>
      rename_i G k ℓ e q bs L
      -- Similar to send - select sends a label
      right; left
      obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
      have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
      subst hkChan
      have hTargetReady := hSelectReady e q bs ℓ L hG hbs
      exact ⟨_, _, _, _, _, _, TypedStep.select hkStr hG hbs hTargetReady rfl rfl rfl rfl⟩
  | branch hk hG hLen hLabels hBodies hOutLbl hDom ih =>
      rename_i G k procs e p bs S' G' W Δ
      -- Similar to recv - branch receives a label
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
          -- Buffer non-empty: should step by selecting a label
          right; left
          -- Use BuffersTyped to get value type from trace head.
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
              -- Contradiction: trace must be non-empty if buffer is non-empty.
              simp [hTrace] at h0trace
          | cons T' ts =>
              have hHeadEdge := hHead branchEdge
              have hEq : T' = .string := by
                simpa [HeadCoherent, hG, branchEdge, hTrace] using hHeadEdge
              have hv := by
                simpa [hTrace, hEq] using hv'
              cases hv with
              | string lbl =>
                  -- ValidLabels: label is one of the branch options
                  have hValidEdge := hValid branchEdge p bs (by simpa [branchEdge] using hG)
                  have hBsSome : (bs.find? (fun b => b.1 == lbl)).isSome := by
                    simpa [hBuf] using hValidEdge
                  rcases (Option.isSome_iff_exists).1 hBsSome with ⟨b, hFindBs⟩
                  cases b with
                  | mk lbl' L =>
                      have hLbl : lbl' = lbl :=
                        findLabel_eq (xs := bs) (lbl := lbl) (lbl' := lbl') (v := L) hFindBs
                      subst lbl'
                      -- Show the corresponding process branch exists
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
  | seq hP hQ ihP ihQ =>
      rename_i P Q S₁ G₁ S₂ G₂ W₁ W₂ Δ₁ Δ₂
      have hProgP := ihP hStore hBufs hCoh hHead hValid hReady hSelectReady
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
  | par split hSplitSfin hSplitGfin hSplitW hSplitΔ
        hDisjG hDisjS hDisjS_left hDisjS_right hDisjS' hDisjW hDisjΔ hP hQ ihP ihQ =>
      rename_i S₁ S₂ G₁ G₂ P Q S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂
      -- Need to split WellFormed across disjoint environments.
      sorry
  | assign_new hNoSh hNoOwn hv =>
      rename_i x v T
      right; left
      exact ⟨_, _, _, _, _, _, TypedStep.assign hv rfl rfl⟩
  | assign_old hNoSh hOwn hv =>
      rename_i x v T
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
    WellFormed G D Ssh Sown store bufs P →
    (P = .skip) ∨
    (∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs P
      G' D' Sown' store' bufs' P') ∨
    BlockedProc store bufs P := by
  intro hWF
  unfold WellFormed at hWF
  obtain ⟨hStore, hBufs, hCoh, hHead, hValid, hReady, hSelectReady, hDisjS, hCons, hPreOut⟩ := hWF
  obtain ⟨Sfin, Gfin, Wfin, Δfin, hOut⟩ := hPreOut
  exact progress_typed_aux hOut hStore hBufs hCoh hHead hValid hReady hSelectReady

/-  Subject reduction (soundness) theorem moved to Effects.Preservation
    to avoid circular dependency (Step is defined in Semantics which imports Typing).

    **Theorem**: TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
                 Step ⟨P, store, bufs, G, D, n⟩ ⟨P', store', bufs', G', D', n⟩

    This will be proven in Preservation.lean after TypedStep is available. -/

end
