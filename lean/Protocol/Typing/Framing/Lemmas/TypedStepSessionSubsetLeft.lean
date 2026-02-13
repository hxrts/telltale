import Protocol.Typing.Framing.Lemmas.MiddleFrameMain

/-! # TypedStep Session Subset (Left Frame)

Session-set monotonicity for the left segment of a framed `TypedStep`.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

-- Left-Frame Session Subset
/-! ## Left Frame Subset -/

theorem SessionsOf_subset_of_TypedStep_left_frame
    {G₁ G₂ G G' D Ssh Sown store bufs P G₁' D' Sown' store' bufs' P'} :
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    G' = G₁' ++ G₂ →
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    SessionsOf G₁' ⊆ SessionsOf G₁ := by
  intro hDisj hEq hEq' hTS
  induction hTS with
  -- Communication Cases
  | send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
      have hLookup : lookupG (G₁ ++ G₂) e = some (.send target T L) := by
        simpa [hEq] using hG
      have hUpd : updateG (G₁ ++ G₂) e L = G₁' ++ G₂ := by
        simpa [hEq, hEq'] using hGout.symm
      exact SessionsOf_left_subset_of_update hLookup hUpd
  | recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
      have hLookup : lookupG (G₁ ++ G₂) e = some (.recv source T L) := by
        simpa [hEq] using hG
      have hUpd : updateG (G₁ ++ G₂) e L = G₁' ++ G₂ := by
        simpa [hEq, hEq'] using hGout.symm
      exact SessionsOf_left_subset_of_update hLookup hUpd
  | select hk hG hFind hReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
      have hLookup : lookupG (G₁ ++ G₂) e = some (.select target bs) := by
        simpa [hEq] using hG
      have hUpd : updateG (G₁ ++ G₂) e L = G₁' ++ G₂ := by
        simpa [hEq, hEq'] using hGout.symm
      exact SessionsOf_left_subset_of_update hLookup hUpd
  | branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
      have hLookup : lookupG (G₁ ++ G₂) e = some (.branch source bs) := by
        simpa [hEq] using hG
      have hUpd : updateG (G₁ ++ G₂) e L = G₁' ++ G₂ := by
        simpa [hEq, hEq'] using hGout.symm
      exact SessionsOf_left_subset_of_update hLookup hUpd
  -- Structural Cases
  | assign =>
      intro s hs
      have hEqG : G₁' ++ G₂ = G₁ ++ G₂ :=
        hEq'.symm.trans hEq
      have hG₁' : G₁' = G₁ := append_left_eq_of_eq hEqG
      simpa [hG₁'] using hs
  | seq_step _ ih =>
/- ## Structured Block 1 -/
      exact ih hEq hEq'
  | seq_skip =>
      intro s hs
      have hEqG : G₁' ++ G₂ = G₁ ++ G₂ :=
        hEq'.symm.trans hEq
      have hG₁' : G₁' = G₁ := append_left_eq_of_eq hEqG
      simpa [hG₁'] using hs
  | par_left split hSlen hTS hDisjG hDisjD hDisjS ih =>
      -- Right frame unchanged; reuse IH on the inner step.
      exact ih hEq hEq'
  | par_right split hSlen hTS hDisjG hDisjD hDisjS ih =>
      exact ih hEq hEq'
  | par_skip_left =>
      intro s hs
      have hEqG : G₁' ++ G₂ = G₁ ++ G₂ :=
        hEq'.symm.trans hEq
      have hG₁' : G₁' = G₁ := append_left_eq_of_eq hEqG
      simpa [hG₁'] using hs
  | par_skip_right =>
      intro s hs
      have hEqG : G₁' ++ G₂ = G₁ ++ G₂ :=
        hEq'.symm.trans hEq
      have hG₁' : G₁' = G₁ := append_left_eq_of_eq hEqG
      simpa [hG₁'] using hs


end
