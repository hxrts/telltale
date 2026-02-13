import Runtime.Proofs.VM.InstrSpec.ConfigEquivSendRecv

/-! # ConfigEquiv: Select and Branch Instructions

Session renaming equivariance for choice instructions: select (sender
picks label) and branch (receiver matches on label). -/

/-
The Problem. Select and branch instructions involve label lookup in
branch lists. For configuration equivalence, we need to show the
renamed specs preserve label matching and type updates.

Solution Structure. Prove `SelectSpec_respects_renaming` and
`BranchSpec_respects_renaming` using `find_renameBranches` to show
label lookup commutes with branch list renaming.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Classical

section

-- Select Renaming Equivariance

theorem SelectSpec_respects_renaming (ρ : SessionRenaming)
    {G G' : GEnv} {D D' : DEnv} {ep : Endpoint} {r : Role} {chosen : Label}
    (hSpec : SelectSpec G G' D D' ep r chosen) :
    SelectSpec (renameGEnv ρ G) (renameGEnv ρ G') (renameDEnv ρ D) (renameDEnv ρ D')
               (renameEndpoint ρ ep) r chosen where
  sender_type := by
    obtain ⟨branches, L', hSender, hFind⟩ := hSpec.sender_type
    use renameBranches ρ branches, renameLocalType ρ L'
    constructor
    · rw [lookupG_rename, hSender]
      simp only [Option.map_some, renameLocalType]
    · rw [find_renameBranches, hFind]
      simp
  type_updated := by
    intro branches_renamed L'_renamed hSender_renamed hFind_renamed
    rw [lookupG_rename] at hSender_renamed
    obtain ⟨branches, L', hSender, hFind⟩ := hSpec.sender_type
    rw [hSender] at hSender_renamed
    simp only [Option.map_some, renameLocalType] at hSender_renamed
    have hBranches_eq : branches_renamed = renameBranches ρ branches := by
      cases hSender_renamed
      rfl
    have hL'_eq : L'_renamed = renameLocalType ρ L' := by
      rw [hBranches_eq, find_renameBranches, hFind] at hFind_renamed
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hFind_renamed
      exact hFind_renamed.2.symm
    have hG' := hSpec.type_updated branches L' hSender hFind
    rw [hG', renameGEnv_updateG, hL'_eq]

  -- Select Renaming Equivariance: Trace and Frame Clauses

  trace_extended := by
    have hD' := hSpec.trace_extended
    simp only at hD'
    simp only [renameEndpoint]
    rw [hD', renameDEnv_updateD]
    simp only [renameEdge]
    congr 1
    have hLookup := lookupD_rename (ρ := ρ) (D := D) (e := { sid := ep.sid, sender := ep.role, receiver := r })
    simp only [renameEdge] at hLookup
    rw [List.map_append, List.map, hLookup, renameValType]
    simp
  frame_G := by
    intro ep' hne
    obtain ⟨branches, L', hSender, hFind⟩ := hSpec.sender_type
    have hG' := hSpec.type_updated branches L' hSender hFind
    rw [hG', renameGEnv_updateG]
    exact lookupG_update_neq (renameGEnv ρ G) (renameEndpoint ρ ep) ep'
      (renameLocalType ρ L') hne.symm
  frame_D := by
    intro e hne
    have hD' := hSpec.trace_extended
    simp only at hD'
    simp only [renameEndpoint] at hne ⊢
    rw [hD', renameDEnv_updateD]
    simp only [renameEdge]
    exact lookupD_update_neq (renameDEnv ρ D)
      { sid := ρ.f ep.sid, sender := ep.role, receiver := r } e
      ((lookupD D { sid := ep.sid, sender := ep.role, receiver := r } ++ [ValType.string]).map (renameValType ρ))
      hne.symm

-- Select ConfigEquiv Preservation

/-- Select respects ConfigEquiv. -/
theorem SelectSpec_respects_ConfigEquiv
    {G₁ G₁' G₂ G₂' : GEnv} {D₁ D₁' D₂ D₂' : DEnv}
    {ep : Endpoint} {r : Role} {chosen : Label}
    (hEquiv : ConfigEquiv ⟨G₁, D₁⟩ ⟨G₂, D₂⟩)
    (hSpec₁ : SelectSpec G₁ G₁' D₁ D₁' ep r chosen)
    (hSpec₂ : SelectSpec G₂ G₂' D₂ D₂'
              (renameEndpoint (hEquiv.choose.toRenaming) ep) r chosen) :
    ConfigEquiv ⟨G₁', D₁'⟩ ⟨G₂', D₂'⟩ := by

  -- Select ConfigEquiv Preservation: Shared Setup

  -- Use the same SessionIso that witnesses the input equivalence.
  let σ := hEquiv.choose
  let ρ := σ.toRenaming
  obtain ⟨hG_equiv, hD_equiv⟩ := hEquiv.choose_spec
  refine ⟨σ, ?_, ?_⟩

  -- Select ConfigEquiv Preservation: GEnv Component

  -- G condition
  · intro e'
    by_cases he : e' = ep
    · -- Case: e' = ep (the updated endpoint)
      obtain ⟨branches₁, L'₁, hSender₁, hFind₁⟩ := hSpec₁.sender_type
      have hG₁' := hSpec₁.type_updated branches₁ L'₁ hSender₁ hFind₁
      obtain ⟨branches₂, L'₂, hSender₂, hFind₂⟩ := hSpec₂.sender_type
      have hG₂' := hSpec₂.type_updated branches₂ L'₂ hSender₂ hFind₂
      -- Determine L'₂ from input equivalence
      have hSender₂_raw := hG_equiv ep
      rw [hSender₁] at hSender₂_raw
      simp only [Option.map_some, renameLocalType] at hSender₂_raw
      rw [hSender₂_raw] at hSender₂
      simp only [Option.some.injEq, LocalType.select.injEq] at hSender₂
      obtain ⟨_, hBranches₂_eq⟩ := hSender₂
      -- Get L'₂ = renameLocalType ρ L'₁ from find correspondence
      have hL'₂_eq : L'₂ = renameLocalType ρ L'₁ := by
        subst hBranches₂_eq
        rw [find_renameBranches, hFind₁] at hFind₂
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hFind₂
        exact hFind₂.2.symm
      -- Compute both sides
      calc lookupG G₂' (renameEndpoint ρ e')
          = lookupG G₂' (renameEndpoint ρ ep) := by rw [he]
        _ = lookupG (updateG G₂ (renameEndpoint ρ ep) L'₂) (renameEndpoint ρ ep) := by rw [hG₂']
        _ = some L'₂ := lookupG_update_eq _ _ _
        _ = some (renameLocalType ρ L'₁) := by rw [hL'₂_eq]
        _ = (some L'₁).map (renameLocalType ρ) := by simp only [Option.map_some]
        _ = (lookupG (updateG G₁ ep L'₁) ep).map (renameLocalType ρ) := by rw [lookupG_update_eq]
        _ = (lookupG G₁' ep).map (renameLocalType ρ) := by rw [← hG₁']
        _ = (lookupG G₁' e').map (renameLocalType ρ) := by rw [← he]
    · -- Case: e' ≠ ep (frame)
      have hne₂ : renameEndpoint ρ e' ≠ renameEndpoint ρ ep := by
        intro heq; exact he (renameEndpoint_inj ρ e' ep heq)
      rw [hSpec₁.frame_G e' he, hSpec₂.frame_G (renameEndpoint ρ e') hne₂]
      exact hG_equiv e'

  -- Select ConfigEquiv Preservation: DEnv Component

  -- D condition
  · intro e'
    let sendEdge : Edge := { sid := ep.sid, sender := ep.role, receiver := r }
    by_cases he : e' = sendEdge
    · -- Case: e' = sendEdge (the updated edge)
      have hD₁' := hSpec₁.trace_extended
      have hD₂' := hSpec₂.trace_extended
      simp only [renameEndpoint] at hD₂'
      have hTrace := hD_equiv sendEdge
      simp only [renameEdge] at hTrace
      -- Rewrite goal: lookupD D₂' (renameEdge ρ e') = (lookupD D₁' e').map (renameValType ρ)
      rw [he]
      simp only [renameEdge]
      rw [hD₁', hD₂', lookupD_update_eq, lookupD_update_eq]
      -- Goal: lookupD D₂ (...) ++ [string] = (lookupD D₁ sendEdge ++ [string]).map (renameValType ρ)
      rw [List.map_append, List.map_singleton, renameValType, hTrace]
    · -- Case: e' ≠ sendEdge (frame)
      have hne₂ : renameEdge ρ e' ≠ renameEdge ρ sendEdge := by
        intro heq; exact he (renameEdge_inj ρ e' sendEdge heq)
      simp only [renameEdge] at hne₂
      rw [hSpec₁.frame_D e' he, hSpec₂.frame_D (renameEdge ρ e') hne₂]
      exact hD_equiv e'

-- Branch Renaming Equivariance

/-- Branch is equivariant under session renaming. -/
theorem BranchSpec_respects_renaming (ρ : SessionRenaming)
    {G G' : GEnv} {D D' : DEnv} {ep : Endpoint} {r : Role} {received : Label}
    (hSpec : BranchSpec G G' D D' ep r received) :
    BranchSpec (renameGEnv ρ G) (renameGEnv ρ G') (renameDEnv ρ D) (renameDEnv ρ D')
               (renameEndpoint ρ ep) r received where
  receiver_type := by
    obtain ⟨branches, L', hRecv, hFind⟩ := hSpec.receiver_type
    use renameBranches ρ branches, renameLocalType ρ L'
    constructor
    · rw [lookupG_rename, hRecv]
      simp only [Option.map_some, renameLocalType]
    · rw [find_renameBranches, hFind]
      simp
  buffer_has_label := by
    obtain ⟨rest, hBuffer⟩ := hSpec.buffer_has_label
    use rest.map (renameValType ρ)
    simp only [renameEndpoint]
    have hLookup := lookupD_rename (ρ := ρ) (D := D) (e := { sid := ep.sid, sender := r, receiver := ep.role })
    simp only [renameEdge] at hLookup
    rw [hLookup, hBuffer]
    simp only [List.map_cons, renameValType]
  type_updated := by
    intro branches_renamed L'_renamed hRecv_renamed hFind_renamed
    rw [lookupG_rename] at hRecv_renamed
    obtain ⟨branches, L', hRecv, hFind⟩ := hSpec.receiver_type
    rw [hRecv] at hRecv_renamed
    simp only [Option.map_some, renameLocalType] at hRecv_renamed
    have hBranches_eq : branches_renamed = renameBranches ρ branches := by
      cases hRecv_renamed
      rfl
    have hL'_eq : L'_renamed = renameLocalType ρ L' := by
      rw [hBranches_eq, find_renameBranches, hFind] at hFind_renamed
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hFind_renamed
      exact hFind_renamed.2.symm
    have hG' := hSpec.type_updated branches L' hRecv hFind
    rw [hG', renameGEnv_updateG, hL'_eq]

  -- Branch Renaming Equivariance: Trace and Frame Clauses

  trace_consumed := by
    obtain ⟨rest, hBuffer, hD'⟩ := hSpec.trace_consumed
    use rest.map (renameValType ρ)
    simp only [renameEndpoint]
    have hLookup := lookupD_rename (ρ := ρ) (D := D) (e := { sid := ep.sid, sender := r, receiver := ep.role })
    simp only [renameEdge] at hLookup
    constructor
    · rw [hLookup, hBuffer]
      simp only [List.map_cons, renameValType]
    · rw [hD', renameDEnv_updateD]
      simp only [renameEdge]
  frame_G := by
    intro ep' hne
    obtain ⟨branches, L', hRecv, hFind⟩ := hSpec.receiver_type
    have hG' := hSpec.type_updated branches L' hRecv hFind
    rw [hG', renameGEnv_updateG]
    exact lookupG_update_neq (renameGEnv ρ G) (renameEndpoint ρ ep) ep'
      (renameLocalType ρ L') hne.symm
  frame_D := by
    intro e hne
    obtain ⟨rest, _, hD'⟩ := hSpec.trace_consumed
    simp only [renameEndpoint] at hne ⊢
    rw [hD', renameDEnv_updateD]
    simp only [renameEdge]
    exact lookupD_update_neq (renameDEnv ρ D)
      { sid := ρ.f ep.sid, sender := r, receiver := ep.role } e
      (rest.map (renameValType ρ)) hne.symm

-- Branch ConfigEquiv Preservation

/-- Branch respects ConfigEquiv. -/
theorem BranchSpec_respects_ConfigEquiv
    {G₁ G₁' G₂ G₂' : GEnv} {D₁ D₁' D₂ D₂' : DEnv}
    {ep : Endpoint} {r : Role} {received : Label}
    (hEquiv : ConfigEquiv ⟨G₁, D₁⟩ ⟨G₂, D₂⟩)
    (hSpec₁ : BranchSpec G₁ G₁' D₁ D₁' ep r received)
    (hSpec₂ : BranchSpec G₂ G₂' D₂ D₂'
              (renameEndpoint (hEquiv.choose.toRenaming) ep) r received) :
    ConfigEquiv ⟨G₁', D₁'⟩ ⟨G₂', D₂'⟩ := by

  -- Branch ConfigEquiv Preservation: Shared Setup

  -- Use the same SessionIso that witnesses the input equivalence.
  let σ := hEquiv.choose
  let ρ := σ.toRenaming
  obtain ⟨hG_equiv, hD_equiv⟩ := hEquiv.choose_spec
  refine ⟨σ, ?_, ?_⟩

  -- Branch ConfigEquiv Preservation: GEnv Component

  -- G condition
  · intro e'
    by_cases he : e' = ep
    · -- Case: e' = ep (the updated endpoint)
      obtain ⟨branches₁, L'₁, hRecv₁, hFind₁⟩ := hSpec₁.receiver_type
      have hG₁' := hSpec₁.type_updated branches₁ L'₁ hRecv₁ hFind₁
      obtain ⟨branches₂, L'₂, hRecv₂, hFind₂⟩ := hSpec₂.receiver_type
      have hG₂' := hSpec₂.type_updated branches₂ L'₂ hRecv₂ hFind₂
      -- Determine L'₂ from input equivalence
      have hRecv₂_raw := hG_equiv ep
      rw [hRecv₁] at hRecv₂_raw
      simp only [Option.map_some, renameLocalType] at hRecv₂_raw
      rw [hRecv₂_raw] at hRecv₂
      simp only [Option.some.injEq, LocalType.branch.injEq] at hRecv₂
      obtain ⟨_, hBranches₂_eq⟩ := hRecv₂
      -- Get L'₂ = renameLocalType ρ L'₁ from find correspondence
      have hL'₂_eq : L'₂ = renameLocalType ρ L'₁ := by
        subst hBranches₂_eq
        rw [find_renameBranches, hFind₁] at hFind₂
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hFind₂
        exact hFind₂.2.symm
      -- Compute both sides
      calc lookupG G₂' (renameEndpoint ρ e')
          = lookupG G₂' (renameEndpoint ρ ep) := by rw [he]
        _ = lookupG (updateG G₂ (renameEndpoint ρ ep) L'₂) (renameEndpoint ρ ep) := by rw [hG₂']
        _ = some L'₂ := lookupG_update_eq _ _ _
        _ = some (renameLocalType ρ L'₁) := by rw [hL'₂_eq]
        _ = (some L'₁).map (renameLocalType ρ) := by simp only [Option.map_some]
        _ = (lookupG (updateG G₁ ep L'₁) ep).map (renameLocalType ρ) := by rw [lookupG_update_eq]
        _ = (lookupG G₁' ep).map (renameLocalType ρ) := by rw [← hG₁']
        _ = (lookupG G₁' e').map (renameLocalType ρ) := by rw [← he]
    · -- Case: e' ≠ ep (frame)
      have hne₂ : renameEndpoint ρ e' ≠ renameEndpoint ρ ep := by
        intro heq; exact he (renameEndpoint_inj ρ e' ep heq)
      rw [hSpec₁.frame_G e' he, hSpec₂.frame_G (renameEndpoint ρ e') hne₂]
      exact hG_equiv e'

  -- Branch ConfigEquiv Preservation: DEnv Component

  -- D condition
  · intro e'
    let recvEdge : Edge := { sid := ep.sid, sender := r, receiver := ep.role }
    by_cases he : e' = recvEdge
    · -- Case: e' = recvEdge (the updated edge)
      obtain ⟨rest₁, hBuf₁, hD₁'⟩ := hSpec₁.trace_consumed
      obtain ⟨rest₂, hBuf₂, hD₂'⟩ := hSpec₂.trace_consumed
      simp only [renameEndpoint] at hD₂' hBuf₂
      have hTrace := hD_equiv recvEdge
      simp only [renameEdge] at hTrace
      -- Rewrite goal
      rw [he]
      simp only [renameEdge]
      rw [hD₁', hD₂', lookupD_update_eq, lookupD_update_eq]
      -- rest₁ and rest₂ are the tails after consuming the label
      -- From hBuf₁: lookupD D₁ recvEdge = label :: rest₁
      -- From hTrace: lookupD D₂ (rename recvEdge) = (lookupD D₁ recvEdge).map rename
      --            = (label :: rest₁).map rename = label' :: rest₁.map rename
      -- From hBuf₂: lookupD D₂ (rename recvEdge) = label' :: rest₂
      -- So rest₂ = rest₁.map rename
      rw [hBuf₁, List.map_cons] at hTrace
      rw [hBuf₂] at hTrace
      simp only [List.cons.injEq] at hTrace
      rw [hTrace.2]
    · -- Case: e' ≠ recvEdge (frame)
      have hne₂ : renameEdge ρ e' ≠ renameEdge ρ recvEdge := by
        intro heq; exact he (renameEdge_inj ρ e' recvEdge heq)
      simp only [renameEdge] at hne₂
      rw [hSpec₁.frame_D e' he, hSpec₂.frame_D (renameEdge ρ e') hne₂]
      exact hD_equiv e'

end
