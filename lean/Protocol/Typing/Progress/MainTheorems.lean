import Protocol.Typing.Progress.LocalProgressCases

/-! # Main Progress Theorems

Top-level progress theorem showing well-typed configurations either
terminate, step, or are blocked waiting for external input. -/

/-
The Problem. Progress requires showing that every well-typed non-skip
process can either take a step or is blocked on an empty buffer. This
combines all per-constructor progress lemmas with the global readiness
conditions.

Solution Structure. Prove `progress_typed_aux` by case analysis on
process form. Each constructor case invokes its local progress lemma.
Parallel and sequential cases recurse on subprocesses.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

-- Main Progress Theorem

theorem progress_typed_aux {G D Ssh Sown store bufs P Sfin Gfin W Δ} :
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    StoreTypedStrong G (SEnvAll Ssh Sown) store →
    DisjointS Ssh (Sown : SEnv) →
    OwnedDisjoint Sown →
    DisjointS Sown.right Sfin.left →
    BuffersTyped G D bufs →
    Coherent G D →
    HeadCoherent G D →
    ValidLabels G D bufs →
    RoleComplete G →
    SendReady G D →
    SelectReady G D →
    DConsistent G D →
    (P = .skip) ∨
      (∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs P
        G' D' Sown' store' bufs' P') ∨
      BlockedProc store bufs P := by
  intro hOut hStore hDisjShAll hOwnDisj hDisjRightFin hBufs hCoh hHead hValid hComplete hReady hSelectReady hCons
  cases P with
  | skip =>
      left; rfl
  -- progress_typed_aux: Send Case
  | send k x =>
      right; left
      exact progress_send hOut hStore hDisjShAll hOwnDisj hReady
  -- progress_typed_aux: Receive Case
  | recv k x =>
      have hProg := progress_recv hOut hStore hDisjShAll hOwnDisj hBufs hHead hComplete
      cases hProg with
      | inl hStep =>
          right; left; exact hStep
      | inr hBlocked =>
          right; right; exact hBlocked
  -- progress_typed_aux: Select Case
  | select k ℓ =>
      right; left
      exact progress_select hOut hStore hDisjShAll hOwnDisj hSelectReady
  -- progress_typed_aux: Branch Case
  | branch k procs =>
      have hProg := progress_branch hOut hStore hDisjShAll hOwnDisj hBufs hHead hValid hComplete
      cases hProg with
      | inl hStep =>
          right; left; exact hStep
      | inr hBlocked =>
          right; right; exact hBlocked
  -- progress_typed_aux: Sequential Composition
  | seq P Q =>
      cases hOut with
      | seq hP hQ =>
          have hDomQ := HasTypeProcPreOut_domsubset hQ
          have hDisjRightMid := DisjointS_of_domsubset_right hDomQ hDisjRightFin
          have hProgP :=
            progress_typed_aux hP hStore hDisjShAll hOwnDisj hDisjRightMid
              hBufs hCoh hHead hValid hComplete hReady hSelectReady hCons
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
  -- progress_typed_aux: Parallel Composition
  | par nS nG P Q =>
      cases hOut with
      | par split hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
          hDisjW hDisjΔ hP hQ =>
          rename_i S₁_fin S₂_fin G₁_fin G₂_fin W₁_fin W₂_fin Δ₁_fin Δ₂_fin
          -- Parallel Case: Reframe Store Typing for Split Contexts
          have hStoreBase :
              StoreTypedStrong G (SEnvAll (Ssh ++ Sown.right) ((split.S1 ++ split.S2) ++ (∅ : SEnv))) store := by
            simpa [SEnvAll, split.hS, List.append_assoc] using hStore
          have hStoreSwap :
              StoreTypedStrong G (SEnvAll (Ssh ++ Sown.right) (split.S2 ++ (split.S1 ++ (∅ : SEnv)))) store :=
            StoreTypedStrong_swap_S_left_prefix (Ssh:=Ssh ++ Sown.right)
              (S₁:=split.S1) (S₂:=split.S2) (S₃:=∅) hDisjS
              (by simpa [List.append_assoc] using hStoreBase)
          have hStoreL :
              StoreTypedStrong G (SEnvAll Ssh { right := Sown.right ++ split.S2, left := split.S1 }) store := by
            simpa [SEnvAll, List.append_assoc] using hStoreSwap
          have hStoreR :
              StoreTypedStrong G (SEnvAll Ssh { right := Sown.right ++ split.S1, left := split.S2 }) store := by
            simpa [SEnvAll, split.hS, List.append_assoc] using hStore
          have hDisjShRight : DisjointS Ssh Sown.right := DisjointS_owned_right hDisjShAll
          have hDisjShSplit : DisjointS Ssh split.S1 ∧ DisjointS Ssh split.S2 :=
            DisjointS_split_from_owned_left split hDisjShAll
          have hDisjShL :
              DisjointS Ssh ({ right := Sown.right ++ split.S2, left := split.S1 } : OwnedEnv) :=
            DisjointS_owned_repack hDisjShRight hDisjShSplit.1 hDisjShSplit.2
          have hDisjShR :
              DisjointS Ssh ({ right := Sown.right ++ split.S1, left := split.S2 } : OwnedEnv) :=
            DisjointS_owned_repack hDisjShRight hDisjShSplit.2 hDisjShSplit.1
          have hOwnL :
              OwnedDisjoint ({ right := Sown.right ++ split.S2, left := split.S1 } : OwnedEnv) :=
            OwnedDisjoint_sub_left (Sown:=Sown) (split:=split) hOwnDisj hDisjS
          have hOwnR :
              OwnedDisjoint ({ right := Sown.right ++ split.S1, left := split.S2 } : OwnedEnv) :=
            OwnedDisjoint_sub_right (Sown:=Sown) (split:=split) hOwnDisj hDisjS
          have hDisjRightFin' : DisjointS Sown.right (S₁_fin ++ S₂_fin) := by
            simpa [hSfin] using hDisjRightFin
          have hDisjRightS1' : DisjointS Sown.right S₁_fin := DisjointS_split_left hDisjRightFin'
          have hDisjRightS2' : DisjointS Sown.right S₂_fin := DisjointS_split_right hDisjRightFin'
          have hDisjOutP : DisjointS (Sown.right ++ split.S2) S₁_fin :=
            DisjointS_append_left hDisjRightS1' (DisjointS_symm hDisjS_left)
          have hDisjOutQ : DisjointS (Sown.right ++ split.S1) S₂_fin :=
            DisjointS_append_left hDisjRightS2' hDisjS_right

          -- Frame pre-out typing to full G.
          have hP_full :=
            HasTypeProcPreOut_frame_G_right (Ssh:=Ssh)
              (Sown:={ right := Sown.right ++ split.S2, left := split.S1 })
              (G:=split.G1) (Gfr:=split.G2) hDisjG hP
          have hQ_full :=
            HasTypeProcPreOut_frame_G_left (Ssh:=Ssh)
              (Sown:={ right := Sown.right ++ split.S1, left := split.S2 })
              (Gfr:=split.G1) (G:=split.G2) hDisjG hOwnR hQ hDisjOutQ
          simp only [← split.hG] at hP_full hQ_full

          -- Parallel Case: Drive Progress on Left Process
          have hProgP :=
            progress_typed_aux hP_full hStoreL hDisjShL hOwnL hDisjOutP
              hBufs hCoh hHead hValid hComplete hReady hSelectReady hCons
          cases hProgP with
          | inl hSkipP =>
              subst hSkipP
              by_cases hS1Nil : split.S1 = []
              · right; left
                exact ⟨_, _, _, store, bufs, Q, TypedStep.par_skip_left split hSlen hS1Nil⟩
              · -- Left skip cannot be eliminated; rely on right progress.
                have hProgQ :=
                  progress_typed_aux hQ_full hStoreR hDisjShR hOwnR hDisjOutQ
                    hBufs hCoh hHead hValid hComplete hReady hSelectReady hCons
                cases hProgQ with
                | inl hSkipQ =>
                    right; right
                    subst hSkipQ
                    exact And.intro (Or.inl rfl) (Or.inl rfl)
                | inr hRestQ =>
                    cases hRestQ with
                    | inl hStepQ =>
                        rcases hStepQ with ⟨G', D', S', store', bufs', Q', hStep⟩
                        -- Parallel Case: Left Skip, Right Steps
                        have hGshape : ∃ G₂', G' = split.G1 ++ G₂' := by
                          have hShape :=
                            TypedStep_preserves_frames (Gleft:=split.G1) (Gmid:=split.G2) (Gright:=[])
                              (by simpa [split.hG])
                              hDisjG (DisjointG_right_empty split.G1) (DisjointG_right_empty split.G2)
                              hStoreR hDisjShR hOwnR hQ hStep
                          rcases hShape with ⟨G₂', hShape⟩
                          refine ⟨G₂', ?_⟩
                          simpa [List.append_assoc] using hShape
                        rcases hGshape with ⟨G₂', hGshape⟩
                        have hRightEq : S'.right = Sown.right ++ split.S1 :=
                          TypedStep_preserves_right hStep hQ_full
                            (by
                              intro x T hLookup
                              exact ⟨T, by simpa using hLookup⟩)
                        have hStep' :
                            TypedStep G ((∅ : DEnv) ++ D) Ssh { right := Sown.right ++ split.S1, left := split.S2 }
                              store bufs Q
                              (split.G1 ++ G₂') ((∅ : DEnv) ++ D')
                              { right := Sown.right ++ split.S1, left := S'.left }
                              store' bufs' Q' := by
                          cases hGshape
                          cases S' with
                          | mk right left =>
                              have hRightEq' : right = Sown.right ++ split.S1 := by
                                simpa using hRightEq
                              cases hRightEq'
                              simpa [DEnv_append_empty_left] using hStep
                        right; left
                        refine ⟨split.G1 ++ G₂', (∅ : DEnv) ++ D',
                            { right := Sown.right, left := split.S1 ++ S'.left },
                            store', bufs', .par split.S1.length nG .skip Q', ?_⟩
                        simpa [List.append_assoc, DEnv_append_empty_left] using
                          (TypedStep.par_right (split:=split) (D₁:=∅) (D₂:=D) (G₂':=G₂') (D₂':=D') (S₂':=S'.left)
                            (P:=.skip) (Q:=Q)
                            hSlen hStep' hDisjG (DisjointD_left_empty D) hDisjS)
                    | inr hBlockedQ =>
                        right; right
                        exact And.intro (Or.inl rfl) (Or.inr (by simpa using hBlockedQ))
          | inr hRestP =>
              cases hRestP with
              | inl hStepP =>
                  rcases hStepP with ⟨G', D', S', store', bufs', P', hStep⟩
                  -- Parallel Case: Left Steps
                  have hGshape : ∃ G₁', G' = G₁' ++ split.G2 := by
                    have hShape :=
                      TypedStep_preserves_frames (Gleft:=[]) (Gmid:=split.G1) (Gright:=split.G2)
                        (by simpa [split.hG])
                        (DisjointG_left_empty split.G1) (DisjointG_left_empty split.G2) hDisjG
                        hStoreL hDisjShL hOwnL hP hStep
                    rcases hShape with ⟨G₁', hShape⟩
                    refine ⟨G₁', ?_⟩
                    simpa [List.append_assoc] using hShape
                  rcases hGshape with ⟨G₁', hGshape⟩
                  have hRightEq : S'.right = Sown.right ++ split.S2 :=
                    TypedStep_preserves_right hStep hP_full
                      (by
                        intro x T hLookup
                        exact ⟨T, by simpa using hLookup⟩)
                  have hStep' :
                      TypedStep G (D ++ (∅ : DEnv)) Ssh { right := Sown.right ++ split.S2, left := split.S1 }
                        store bufs P
                        (G₁' ++ split.G2) (D' ++ (∅ : DEnv))
                        { right := Sown.right ++ split.S2, left := S'.left }
                        store' bufs' P' := by
                    cases hGshape
                    cases S' with
                    | mk right left =>
                        have hRightEq' : right = Sown.right ++ split.S2 := by
                          simpa using hRightEq
                        cases hRightEq'
                        simpa [DEnv_append_empty_right] using hStep
                  right; left
                  refine ⟨G₁' ++ split.G2, D' ++ (∅ : DEnv),
                      { right := Sown.right, left := S'.left ++ split.S2 },
                      store', bufs', .par S'.left.length nG P' Q, ?_⟩
                  simpa [List.append_assoc, DEnv_append_empty_right] using
                    (TypedStep.par_left (split:=split) (D₁:=D) (D₂:=∅) (G₁':=G₁') (D₁':=D') (S₁':=S'.left)
                      (P:=P) (Q:=Q)
                      hSlen hStep' hDisjG (DisjointD_right_empty D) hDisjS)
              | inr hBlockedP =>
                  -- Parallel Case: Left Blocked, Drive Right Progress
                  have hProgQ :=
                    progress_typed_aux hQ_full hStoreR hDisjShR hOwnR hDisjOutQ
                      hBufs hCoh hHead hValid hComplete hReady hSelectReady hCons
                  cases hProgQ with
                  | inl hSkipQ =>
                      subst hSkipQ
                      by_cases hS2Nil : split.S2 = []
                      · right; left
                        exact ⟨_, _, _, store, bufs, P, TypedStep.par_skip_right split hSlen hS2Nil⟩
                      · right; right
                        exact And.intro (Or.inr (by simpa using hBlockedP)) (Or.inl rfl)
                  | inr hRestQ =>
                      cases hRestQ with
                      | inl hStepQ =>
                          rcases hStepQ with ⟨G', D', S', store', bufs', Q', hStep⟩
                          -- Parallel Case: Right Steps Under Left Block
                          have hGshape : ∃ G₂', G' = split.G1 ++ G₂' := by
                            have hShape :=
                              TypedStep_preserves_frames (Gleft:=split.G1) (Gmid:=split.G2) (Gright:=[])
                                (by simpa [split.hG])
                                hDisjG (DisjointG_right_empty split.G1) (DisjointG_right_empty split.G2)
                                hStoreR hDisjShR hOwnR hQ hStep
                            rcases hShape with ⟨G₂', hShape⟩
                            refine ⟨G₂', ?_⟩
                            simpa [List.append_assoc] using hShape
                          rcases hGshape with ⟨G₂', hGshape⟩
                          have hRightEq : S'.right = Sown.right ++ split.S1 :=
                            TypedStep_preserves_right hStep hQ_full
                              (by
                                intro x T hLookup
                                exact ⟨T, by simpa using hLookup⟩)
                          have hStep' :
                              TypedStep G ((∅ : DEnv) ++ D) Ssh { right := Sown.right ++ split.S1, left := split.S2 }
                                store bufs Q
                                (split.G1 ++ G₂') ((∅ : DEnv) ++ D')
                                { right := Sown.right ++ split.S1, left := S'.left }
                                store' bufs' Q' := by
                            cases hGshape
                            cases S' with
                            | mk right left =>
                                have hRightEq' : right = Sown.right ++ split.S1 := by
                                  simpa using hRightEq
                                cases hRightEq'
                                simpa [DEnv_append_empty_left] using hStep
                          right; left
                          refine ⟨split.G1 ++ G₂', (∅ : DEnv) ++ D',
                              { right := Sown.right, left := split.S1 ++ S'.left },
                              store', bufs', .par split.S1.length nG P Q', ?_⟩
                          simpa [List.append_assoc, DEnv_append_empty_left] using
                            (TypedStep.par_right (split:=split) (D₁:=∅) (D₂:=D) (G₂':=G₂') (D₂':=D') (S₂':=S'.left)
                              (P:=P) (Q:=Q)
                              hSlen hStep' hDisjG (DisjointD_left_empty D) hDisjS)
                      | inr hBlockedQ =>
                          right; right
                          exact And.intro (Or.inr (by simpa using hBlockedP))
                            (Or.inr (by simpa using hBlockedQ))
  | newSession roles f P =>
      cases hOut
  -- progress_typed_aux: Assign Case
  | assign x v =>
      right; left
      exact progress_assign hOut

-- Top-Level Progress Packaging

/-- Progress theorem: A complete well-formed process can either step or is in a final/blocked state.

    **Proof strategy**: Case analysis on process P:
    - `skip`: Terminates
    - `send k x`: Derive TypedStep.send from lookupG via HasTypeProcPre inversion
    - `recv k x`: Check buffer - if non-empty, derive TypedStep.recv; else blocked
    - `seq P Q`: Use IH on P or skip elimination
    - `par P Q`: Use IH on P or Q or skip elimination -/
theorem progress_typed {G D Ssh Sown store bufs P} :
    WellFormedComplete G D Ssh Sown store bufs P →
    (P = .skip) ∨
    (∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs P
      G' D' Sown' store' bufs' P') ∨
    BlockedProc store bufs P := by
  intro hWF
  rcases hWF with ⟨hWF, hComplete⟩
  unfold LocalTypeR.WellFormed at hWF
  obtain ⟨hStore, hBufs, hCoh, hHead, hValid, hCompat, hDisjS, hCons, hDCons, hPreOut⟩ := hWF
  obtain ⟨Sfin, Gfin, Wfin, Δfin, hOut, hDisjRightFin⟩ := hPreOut
  have hReady : SendReady G D := Compatible_to_SendReady hCompat
  have hSelectReady : SelectReady G D := Compatible_to_SelectReady hCompat
  exact progress_typed_aux hOut hStore hDisjS hCons hDisjRightFin
    hBufs hCoh hHead hValid hComplete hReady hSelectReady hDCons

-- Convenience Wrapper

/-- Progress with explicit RoleComplete (keeps the old WellFormed ergonomics). -/
theorem progress_typed_with_rolecomplete {G D Ssh Sown store bufs P} :
    LocalTypeR.WellFormed G D Ssh Sown store bufs P →
    RoleComplete G →
    (P = .skip) ∨
    (∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs P
      G' D' Sown' store' bufs' P') ∨
    BlockedProc store bufs P := by
  intro hWF hComplete
  exact progress_typed (G:=G) (D:=D) (Ssh:=Ssh) (Sown:=Sown) (store:=store) (bufs:=bufs) (P:=P)
    ⟨hWF, hComplete⟩

/-  Subject reduction (soundness) theorem moved to Protocol.Preservation
    to avoid circular dependency (Step is defined in Semantics which imports Typing).

    **Theorem**: TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
                 Step ⟨P, store, bufs, G, D, n⟩ ⟨P', store', bufs', G', D', n⟩

    This will be proven in Preservation.lean after TypedStep is available. -/


end
