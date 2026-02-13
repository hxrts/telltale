import Runtime.Proofs.VM.InstrSpec.ConfigEquivSelectBranch

/-! # ConfigEquiv: Open, Close, Transfer Instructions

Session renaming equivariance for session lifecycle instructions:
open (create session), close (end session), and transfer (move endpoint). -/

/-
The Problem. Session lifecycle instructions modify the GEnv by adding
or removing endpoints. For configuration equivalence, we need to show
these specs are equivariant under session renaming.

Solution Structure. Prove `OpenSpec_respects_renaming`, `CloseSpec_
respects_renaming`, `TransferSpec_respects_renaming` by showing
freshness, endpoint addition, and frame preservation transform correctly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Classical

section

-- Open Renaming Equivariance

theorem OpenSpec_respects_renaming (ρ : SessionRenaming)
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {roles : List Role}
    (hSpec : OpenSpec G G' D D' s roles) :
    OpenSpec (renameGEnv ρ G) (renameGEnv ρ G') (renameDEnv ρ D) (renameDEnv ρ D')
             (ρ.f s) roles where
  fresh := by
    intro ep hSome hEq
    -- If ep.sid = ρ.f s, need to derive contradiction from freshness
    -- lookupG (renameGEnv ρ G) ep = some _ means there's a preimage
    rw [Option.isSome_iff_exists] at hSome
    obtain ⟨L, hL⟩ := hSome
    obtain ⟨ep', L', hEp, hL'_eq, hLookup⟩ := lookupG_rename_inv ρ G ep L hL
    have hPreimage : ep'.sid = s := by
      have hSidEq : ep.sid = ρ.f ep'.sid := by
        rw [hEp]
        simp only [renameEndpoint]
      rw [hEq] at hSidEq
      exact ρ.inj _ _ hSidEq.symm
    have hSome' : (lookupG G ep').isSome := by
      rw [Option.isSome_iff_exists]
      exact ⟨L', hLookup⟩
    exact hSpec.fresh ep' hSome' hPreimage

  -- Open Renaming Equivariance: Endpoint Additions

  endpoints_added := by
    intro r hr
    have hAdded := hSpec.endpoints_added r hr
    rw [Option.isSome_iff_exists] at hAdded ⊢
    obtain ⟨L, hL⟩ := hAdded
    use renameLocalType ρ L
    have hEp : { sid := ρ.f s, role := r : Endpoint } = renameEndpoint ρ { sid := s, role := r } := by
      simp only [renameEndpoint]
    rw [hEp, lookupG_rename, hL]
    simp only [Option.map_some]

  -- Open Renaming Equivariance: GEnv Frame

  frame_G := by
    intro ep hSidNe
    have hSidNe' : ep.sid ≠ ρ.f s := hSidNe
    -- If ep.sid ≠ ρ.f s, check if ep is in the renamed image
    by_cases hPre : ∃ ep', renameEndpoint ρ ep' = ep
    case pos =>
      obtain ⟨ep', hEp⟩ := hPre
      have hSidNe'' : ep'.sid ≠ s := by
        intro hEq
        have hSid : ep.sid = ρ.f ep'.sid := by
          rw [← hEp]
          simp only [renameEndpoint]
        rw [hEq] at hSid
        exact hSidNe' hSid
      have hFrame := hSpec.frame_G ep' hSidNe''
      rw [← hEp, lookupG_rename, lookupG_rename, hFrame]
    case neg =>
      -- ep not in renamed image, so lookupG is none on both sides
      have hNone : lookupG (renameGEnv ρ G) ep = none := by
        by_contra hSome
        rw [← ne_eq, Option.ne_none_iff_exists'] at hSome
        obtain ⟨L, hL⟩ := hSome
        obtain ⟨ep', _, hEp, _, _⟩ := lookupG_rename_inv ρ G ep L hL
        exact hPre ⟨ep', hEp.symm⟩
      have hNone' : lookupG (renameGEnv ρ G') ep = none := by
        by_contra hSome
        rw [← ne_eq, Option.ne_none_iff_exists'] at hSome
        obtain ⟨L, hL⟩ := hSome
        obtain ⟨ep', _, hEp, _, _⟩ := lookupG_rename_inv ρ G' ep L hL
        exact hPre ⟨ep', hEp.symm⟩
      rw [hNone, hNone']

  -- Open Renaming Equivariance: Trace Clauses

  traces_empty := by
    intro e hSidEq
    -- e.sid = ρ.f s, need to find preimage edge
    -- The trace should be empty because original trace was empty
    by_cases hPre : ∃ e', renameEdge ρ e' = e
    case pos =>
      obtain ⟨e', hE⟩ := hPre
      have hSidEq' : e'.sid = s := by
        have hSid : e.sid = ρ.f e'.sid := by
          rw [← hE]
          simp only [renameEdge]
        rw [hSidEq] at hSid
        exact ρ.inj _ _ hSid.symm
      have hEmpty := hSpec.traces_empty e' hSidEq'
      rw [← hE, lookupD_rename, hEmpty]
      simp only [List.map_nil]
    case neg =>
      -- Not in preimage, so lookup returns empty by default
      by_contra hNe
      obtain ⟨e', hE, _⟩ := lookupD_rename_inv ρ D' e hNe
      exact hPre ⟨e', hE.symm⟩

  -- Open Renaming Equivariance: DEnv Frame

  frame_D := by
    intro e hSidNe
    by_cases hPre : ∃ e', renameEdge ρ e' = e
    case pos =>
      obtain ⟨e', hE⟩ := hPre
      have hSidNe' : e'.sid ≠ s := by
        intro hEq
        have hSid : e.sid = ρ.f e'.sid := by
          rw [← hE]
          simp only [renameEdge]
        rw [hEq] at hSid
        exact hSidNe hSid
      have hFrame := hSpec.frame_D e' hSidNe'
      rw [← hE, lookupD_rename, lookupD_rename, hFrame]
    case neg =>
      -- Not in preimage, lookup returns empty on both
      have hEmpty : lookupD (renameDEnv ρ D) e = [] := by
        by_contra hNe
        obtain ⟨e', hE, _⟩ := lookupD_rename_inv ρ D e hNe
        exact hPre ⟨e', hE.symm⟩
      have hEmpty' : lookupD (renameDEnv ρ D') e = [] := by
        by_contra hNe
        obtain ⟨e', hE, _⟩ := lookupD_rename_inv ρ D' e hNe
        exact hPre ⟨e', hE.symm⟩
      rw [hEmpty, hEmpty']

-- Open ConfigEquiv Preservation

/-- Open respects ConfigEquiv.

    Note: This proof requires additional specification constraints on OpenSpec.
    Specifically, OpenSpec needs to constrain:
    1. What types are assigned to new endpoints (must be projections of global type)
    2. What happens to non-role endpoints in the new session (should remain None)

    These constraints would ensure that two Opens with related session IDs
    produce ConfigEquiv outputs. For now, the core structure is in place
    with sorries for the parts needing specification enhancement. -/
theorem OpenSpec_respects_ConfigEquiv
    {G₁ G₁' G₂ G₂' : GEnv} {D₁ D₁' D₂ D₂' : DEnv}
    {s : SessionId} {roles : List Role}
    (hEquiv : ConfigEquiv ⟨G₁, D₁⟩ ⟨G₂, D₂⟩)
    (hSpec₁ : OpenSpec G₁ G₁' D₁ D₁' s roles)
    (hSpec₂ : OpenSpec G₂ G₂' D₂ D₂' (hEquiv.choose.fwd s) roles)
    (hNewRoles :
      ∀ r, r ∈ roles →
        ∃ L, lookupG G₁' { sid := s, role := r } = some L ∧
          lookupG G₂' { sid := hEquiv.choose.fwd s, role := r } =
            some (renameLocalType (hEquiv.choose.toRenaming) L))
    (hNoExtra₁ : ∀ r, r ∉ roles → lookupG G₁' { sid := s, role := r } = none)
    (hNoExtra₂ : ∀ r, r ∉ roles →
      lookupG G₂' { sid := hEquiv.choose.fwd s, role := r } = none) :
    ConfigEquiv ⟨G₁', D₁'⟩ ⟨G₂', D₂'⟩ := by

  -- Open ConfigEquiv Preservation: Shared Setup

  let σ := hEquiv.choose
  let ρ := σ.toRenaming
  obtain ⟨hG, hD⟩ := hEquiv.choose_spec
  refine ⟨σ, ?_, ?_⟩

  -- Open ConfigEquiv Preservation: GEnv Component

  · intro e
    cases e with
    | mk sid role =>
      by_cases hSid : sid = s
      · subst hSid
        by_cases hIn : role ∈ roles
        · rcases hNewRoles role hIn with ⟨L, hL₁, hL₂⟩
          simpa [σ, ρ, renameEndpoint, hL₁, hL₂]
        · have hNone₁ : lookupG G₁' { sid := sid, role := role } = none := hNoExtra₁ role hIn
          have hNone₂ : lookupG G₂' { sid := σ.fwd sid, role := role } = none := hNoExtra₂ role hIn
          simpa [σ, ρ, renameEndpoint, hNone₁, hNone₂]
      · have hSidNe₂ : (renameEndpoint ρ { sid := sid, role := role }).sid ≠ σ.fwd s := by
          change ρ.f sid ≠ ρ.f s
          intro hEq
          exact hSid (ρ.inj _ _ hEq)
        have hFrame₁ : lookupG G₁' { sid := sid, role := role } = lookupG G₁ { sid := sid, role := role } :=
          hSpec₁.frame_G { sid := sid, role := role } hSid
        have hFrame₂ :
            lookupG G₂' (renameEndpoint ρ { sid := sid, role := role }) =
              lookupG G₂ (renameEndpoint ρ { sid := sid, role := role }) :=
          hSpec₂.frame_G (renameEndpoint ρ { sid := sid, role := role }) hSidNe₂
        calc
          lookupG G₂' (renameEndpoint ρ { sid := sid, role := role })
              = lookupG G₂ (renameEndpoint ρ { sid := sid, role := role }) := hFrame₂
          _ = (lookupG G₁ { sid := sid, role := role }).map (renameLocalType ρ) :=
                hG { sid := sid, role := role }
          _ = (lookupG G₁' { sid := sid, role := role }).map (renameLocalType ρ) := by
                rw [hFrame₁]

  -- Open ConfigEquiv Preservation: DEnv Component

  · intro e
    cases e with
    | mk sid sender receiver =>
      by_cases hSid : sid = s
      · subst hSid
        have hEmpty₁ : lookupD D₁' { sid := sid, sender := sender, receiver := receiver } = [] :=
          hSpec₁.traces_empty { sid := sid, sender := sender, receiver := receiver } rfl
        have hEmpty₂ :
            lookupD D₂' (renameEdge ρ { sid := sid, sender := sender, receiver := receiver }) = [] := by
          have hSidRen :
              (renameEdge ρ { sid := sid, sender := sender, receiver := receiver }).sid = σ.fwd sid := by
            change ρ.f sid = σ.fwd sid
            rfl
          exact hSpec₂.traces_empty (renameEdge ρ { sid := sid, sender := sender, receiver := receiver }) hSidRen
        rw [hEmpty₁, hEmpty₂]
        simp
      · have hSidNe₂ : (renameEdge ρ { sid := sid, sender := sender, receiver := receiver }).sid ≠ σ.fwd s := by
          change ρ.f sid ≠ ρ.f s
          intro hEq
          exact hSid (ρ.inj _ _ hEq)
        have hFrame₁ :
            lookupD D₁' { sid := sid, sender := sender, receiver := receiver } =
              lookupD D₁ { sid := sid, sender := sender, receiver := receiver } :=
          hSpec₁.frame_D { sid := sid, sender := sender, receiver := receiver } hSid
        have hFrame₂ :
            lookupD D₂' (renameEdge ρ { sid := sid, sender := sender, receiver := receiver }) =
              lookupD D₂ (renameEdge ρ { sid := sid, sender := sender, receiver := receiver }) :=
          hSpec₂.frame_D (renameEdge ρ { sid := sid, sender := sender, receiver := receiver }) hSidNe₂
        calc
          lookupD D₂' (renameEdge ρ { sid := sid, sender := sender, receiver := receiver })
              = lookupD D₂ (renameEdge ρ { sid := sid, sender := sender, receiver := receiver }) := hFrame₂
          _ = (lookupD D₁ { sid := sid, sender := sender, receiver := receiver }).map (renameValType ρ) :=
                hD { sid := sid, sender := sender, receiver := receiver }
          _ = (lookupD D₁' { sid := sid, sender := sender, receiver := receiver }).map (renameValType ρ) := by
                rw [hFrame₁]

-- Close Renaming Equivariance

/-- Close is equivariant under session renaming. -/
theorem CloseSpec_respects_renaming (ρ : SessionRenaming)
    {G G' : GEnv} {D : DEnv} {ep : Endpoint}
    (hSpec : CloseSpec G G' D ep) :
    CloseSpec (renameGEnv ρ G) (renameGEnv ρ G') (renameDEnv ρ D)
              (renameEndpoint ρ ep) where
  endpoint_at_end := by
    rw [lookupG_rename, hSpec.endpoint_at_end]
    simp only [Option.map_some, renameLocalType]
  outgoing_empty := by
    intro other
    have hEmpty := hSpec.outgoing_empty other
    simp only [renameEndpoint]
    have hLookup := lookupD_rename (ρ := ρ) (D := D) (e := { sid := ep.sid, sender := ep.role, receiver := other })
    simp only [renameEdge] at hLookup
    rw [hLookup, hEmpty]
    simp only [List.map_nil]
  incoming_empty := by
    intro other
    have hEmpty := hSpec.incoming_empty other
    simp only [renameEndpoint]
    have hLookup := lookupD_rename (ρ := ρ) (D := D) (e := { sid := ep.sid, sender := other, receiver := ep.role })
    simp only [renameEdge] at hLookup
    rw [hLookup, hEmpty]
    simp only [List.map_nil]
  endpoint_removed := by
    rw [lookupG_rename, hSpec.endpoint_removed]
    simp only [Option.map_none]

  -- Close Renaming Equivariance: GEnv Frame

  frame_G := by
    intro ep' hne
    by_cases hPre : ∃ ep'', renameEndpoint ρ ep'' = ep'
    case pos =>
      obtain ⟨ep'', hEp⟩ := hPre
      have hne'' : ep'' ≠ ep := by
        intro hEq
        subst hEq
        exact hne hEp.symm
      have hFrame := hSpec.frame_G ep'' hne''
      rw [← hEp, lookupG_rename, lookupG_rename, hFrame]
    case neg =>
      -- ep' not in renamed image
      have hNone : lookupG (renameGEnv ρ G) ep' = none := by
        by_contra hSome
        rw [← ne_eq, Option.ne_none_iff_exists'] at hSome
        obtain ⟨L, hL⟩ := hSome
        obtain ⟨ep'', _, hEp, _, _⟩ := lookupG_rename_inv ρ G ep' L hL
        exact hPre ⟨ep'', hEp.symm⟩
      have hNone' : lookupG (renameGEnv ρ G') ep' = none := by
        by_contra hSome
        rw [← ne_eq, Option.ne_none_iff_exists'] at hSome
        obtain ⟨L, hL⟩ := hSome
        obtain ⟨ep'', _, hEp, _, _⟩ := lookupG_rename_inv ρ G' ep' L hL
        exact hPre ⟨ep'', hEp.symm⟩
      rw [hNone, hNone']

-- Close ConfigEquiv Preservation

/-- Close respects ConfigEquiv.
    Note: Close doesn't modify D, so D₁ = D₁' and D₂ = D₂'. -/
theorem CloseSpec_respects_ConfigEquiv
    {G₁ G₁' G₂ G₂' : GEnv} {D₁ D₂ : DEnv}
    {ep : Endpoint}
    (hEquiv : ConfigEquiv ⟨G₁, D₁⟩ ⟨G₂, D₂⟩)
    (hSpec₁ : CloseSpec G₁ G₁' D₁ ep)
    (hSpec₂ : CloseSpec G₂ G₂' D₂ (renameEndpoint (hEquiv.choose.toRenaming) ep)) :
    ConfigEquiv ⟨G₁', D₁⟩ ⟨G₂', D₂⟩ := by
  -- Use the same SessionIso that witnesses the input equivalence.
  let σ := hEquiv.choose
  let ρ := σ.toRenaming
  obtain ⟨hG_equiv, hD_equiv⟩ := hEquiv.choose_spec
  refine ⟨σ, ?_, ?_⟩
  -- G condition
  · intro e'
    by_cases he : e' = ep
    · -- Case: e' = ep (the removed endpoint)
      calc lookupG G₂' (renameEndpoint ρ e')
          = lookupG G₂' (renameEndpoint ρ ep) := by rw [he]
        _ = none := hSpec₂.endpoint_removed
        _ = Option.map (renameLocalType ρ) none := by simp only [Option.map_none]
        _ = (lookupG G₁' ep).map (renameLocalType ρ) := by rw [hSpec₁.endpoint_removed]
        _ = (lookupG G₁' e').map (renameLocalType ρ) := by rw [← he]
    · -- Case: e' ≠ ep (frame)
      have hne₂ : renameEndpoint ρ e' ≠ renameEndpoint ρ ep := by
        intro heq; exact he (renameEndpoint_inj ρ e' ep heq)
      rw [hSpec₁.frame_G e' he, hSpec₂.frame_G (renameEndpoint ρ e') hne₂]
      exact hG_equiv e'
  -- D condition: unchanged
  · exact hD_equiv

-- Transfer Renaming Equivariance

/-- Transfer is equivariant under session renaming. -/
theorem TransferSpec_respects_renaming (ρ : SessionRenaming)
    {G G' : GEnv} {D D' : DEnv}
    {ep : Endpoint} {r : Role} {delegatedSession : SessionId} {delegatedRole : Role}
    (hSpec : TransferSpec G G' D D' ep r delegatedSession delegatedRole) :
    TransferSpec (renameGEnv ρ G) (renameGEnv ρ G') (renameDEnv ρ D) (renameDEnv ρ D')
                 (renameEndpoint ρ ep) r (ρ.f delegatedSession) delegatedRole where
  sender_type := by
    obtain ⟨L', hSender⟩ := hSpec.sender_type
    use renameLocalType ρ L'
    rw [lookupG_rename]
    simp only [hSender, Option.map_some, renameLocalType, renameValType]
  type_updated := by
    intro L'_renamed hSender_renamed
    rw [lookupG_rename] at hSender_renamed
    obtain ⟨L', hSender⟩ := hSpec.sender_type
    rw [hSender] at hSender_renamed
    simp only [Option.map_some, renameLocalType, renameValType] at hSender_renamed
    have hL'_eq : L'_renamed = renameLocalType ρ L' := by
      cases hSender_renamed
      rfl
    have hG' := hSpec.type_updated L' hSender
    rw [hG', renameGEnv_updateG, hL'_eq]

  -- Transfer Renaming Equivariance: Trace and Frames

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
    obtain ⟨L', hSender⟩ := hSpec.sender_type
    have hG' := hSpec.type_updated L' hSender
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
      ((lookupD D { sid := ep.sid, sender := ep.role, receiver := r } ++ [ValType.chan delegatedSession delegatedRole]).map (renameValType ρ))
      hne.symm

-- Transfer ConfigEquiv Preservation

/-- Transfer respects ConfigEquiv. -/
theorem TransferSpec_respects_ConfigEquiv
    {G₁ G₁' G₂ G₂' : GEnv} {D₁ D₁' D₂ D₂' : DEnv}
    {ep : Endpoint} {r : Role} {delegatedSession : SessionId} {delegatedRole : Role}
    (hEquiv : ConfigEquiv ⟨G₁, D₁⟩ ⟨G₂, D₂⟩)
    (hSpec₁ : TransferSpec G₁ G₁' D₁ D₁' ep r delegatedSession delegatedRole)
    (hSpec₂ : TransferSpec G₂ G₂' D₂ D₂'
              (renameEndpoint (hEquiv.choose.toRenaming) ep) r
              (hEquiv.choose.fwd delegatedSession) delegatedRole) :
    ConfigEquiv ⟨G₁', D₁'⟩ ⟨G₂', D₂'⟩ := by
  -- Use the same SessionIso that witnesses the input equivalence.
  let σ := hEquiv.choose
  let ρ := σ.toRenaming
  obtain ⟨hG_equiv, hD_equiv⟩ := hEquiv.choose_spec
  refine ⟨σ, ?_, ?_⟩

  -- Transfer ConfigEquiv Preservation: GEnv Component

  -- G condition
  · intro e'
    by_cases he : e' = ep
    · -- Case: e' = ep (the updated endpoint)
      obtain ⟨L'₁, hSender₁⟩ := hSpec₁.sender_type
      have hG₁' := hSpec₁.type_updated L'₁ hSender₁
      obtain ⟨L'₂, hSender₂⟩ := hSpec₂.sender_type
      have hG₂' := hSpec₂.type_updated L'₂ hSender₂
      -- Determine L'₂ from input equivalence
      have hSender₂_raw := hG_equiv ep
      rw [hSender₁] at hSender₂_raw
      simp only [Option.map_some, renameLocalType, renameValType] at hSender₂_raw
      rw [hSender₂_raw] at hSender₂
      simp only [Option.some.injEq, LocalType.send.injEq] at hSender₂
      -- send has 3 fields: role, valtype, continuation
      obtain ⟨_, _, hL'₂_eq⟩ := hSender₂
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

  -- Transfer ConfigEquiv Preservation: DEnv Component

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
      -- Goal: lookupD D₂ (...) ++ [chan...] = (lookupD D₁ sendEdge ++ [chan...]).map (renameValType ρ)
      rw [List.map_append, List.map_singleton, renameValType, hTrace]
      -- The remaining goal equates σ.fwd with σ.toRenaming.f which are definitionally equal
      rfl
    · -- Case: e' ≠ sendEdge (frame)
      have hne₂ : renameEdge ρ e' ≠ renameEdge ρ sendEdge := by
        intro heq; exact he (renameEdge_inj ρ e' sendEdge heq)
      simp only [renameEdge] at hne₂
      rw [hSpec₁.frame_D e' he, hSpec₂.frame_D (renameEdge ρ e') hne₂]
      exact hD_equiv e'

end
