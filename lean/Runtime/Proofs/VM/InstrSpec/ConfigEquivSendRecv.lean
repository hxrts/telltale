import Runtime.Proofs.VM.InstrSpec.Preservation

/-! # ConfigEquiv: Send and Recv Instructions

Session renaming equivariance for communication instructions, showing
that send/recv specs are true morphisms on the quotient space S/G. -/

/-
The Problem. Instructions must be equivariant under session renaming
so that ConfigEquiv (configurations equal up to session ID choice) is
preserved. If C₁ ≈ C₂ and we apply the same instruction, then C₁' ≈ C₂'.

Solution Structure. Prove `SendSpec_respects_renaming` and `RecvSpec_
respects_renaming` by showing each spec component (sender_type,
type_updated, trace_extended) transforms correctly under renaming.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Classical

section

/-! ## Quotient-Respecting Theorems (ConfigEquiv)

Each instruction spec is equivariant under session renaming. This ensures that
instructions are true morphisms on the quotient space S/G (configurations
modulo session ID renaming).

The pattern: if Spec holds for (G, D, ep, params...), then the renamed spec
holds for (renameGEnv ρ G, renameDEnv ρ D, renameEndpoint ρ ep, renameParams ρ params...).

From this equivariance, ConfigEquiv preservation follows:
if C₁ ≈ C₂ and we apply the same instruction to both, then C₁' ≈ C₂'.

**Note:** These theorems require "update commutes with renaming" lemmas
(renameGEnv_updateG, renameDEnv_updateD) which are infrastructure gaps. -/

/-- Send is equivariant under session renaming.

    If a send spec holds, then the same spec holds on renamed environments
    with renamed operands. -/
theorem SendSpec_respects_renaming (ρ : SessionRenaming)
    {G G' : GEnv} {D D' : DEnv} {ep : Endpoint} {r : Role} {T : ValType}
    (hSpec : SendSpec G G' D D' ep r T) :
    SendSpec (renameGEnv ρ G) (renameGEnv ρ G') (renameDEnv ρ D) (renameDEnv ρ D')
             (renameEndpoint ρ ep) r (renameValType ρ T) where
  sender_type := by
    obtain ⟨L', hSender⟩ := hSpec.sender_type
    use renameLocalType ρ L'
    rw [lookupG_rename, hSender]
    simp only [Option.map_some, renameLocalType]
  type_updated := by
    intro L'_renamed hSender_renamed
    rw [lookupG_rename] at hSender_renamed
    obtain ⟨L', hSender⟩ := hSpec.sender_type
    rw [hSender] at hSender_renamed
    simp only [Option.map_some, renameLocalType] at hSender_renamed
    have hL'_eq : L'_renamed = renameLocalType ρ L' := by
      cases hSender_renamed
      rfl
    have hG' := hSpec.type_updated L' hSender
    rw [hG', renameGEnv_updateG, hL'_eq]

  -- Send Renaming Equivariance: Trace and Frame Clauses

  trace_extended := by
    have hD' := hSpec.trace_extended
    simp only at hD'
    simp only [renameEndpoint]
    rw [hD', renameDEnv_updateD]
    simp only [renameEdge]
    congr 1
    have hLookup := lookupD_rename (ρ := ρ) (D := D) (e := { sid := ep.sid, sender := ep.role, receiver := r })
    simp only [renameEdge] at hLookup
    rw [List.map_append, List.map, hLookup]
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
      ((lookupD D { sid := ep.sid, sender := ep.role, receiver := r } ++ [T]).map (renameValType ρ))
      hne.symm

-- Send ConfigEquiv Preservation

/-- Send respects ConfigEquiv: equivalent configs produce equivalent results. -/
/- ## Structured Block 1 -/
theorem SendSpec_respects_ConfigEquiv
    {G₁ G₁' G₂ G₂' : GEnv} {D₁ D₁' D₂ D₂' : DEnv}
    {ep : Endpoint} {r : Role} {T : ValType}
    (hEquiv : ConfigEquiv ⟨G₁, D₁⟩ ⟨G₂, D₂⟩)
    (hSpec₁ : SendSpec G₁ G₁' D₁ D₁' ep r T)
    (hSpec₂ : SendSpec G₂ G₂' D₂ D₂'
              (renameEndpoint (hEquiv.choose.toRenaming) ep) r
              (renameValType hEquiv.choose.toRenaming T)) :
    ConfigEquiv ⟨G₁', D₁'⟩ ⟨G₂', D₂'⟩ := by

  -- Send ConfigEquiv Preservation: Shared Setup

  -- Use the same SessionIso that witnesses the input equivalence.
  let σ := hEquiv.choose
  let ρ := σ.toRenaming
  obtain ⟨hG_equiv, hD_equiv⟩ := hEquiv.choose_spec
  -- Witness: the same σ works for the output.
  refine ⟨σ, ?_, ?_⟩

  -- Send ConfigEquiv Preservation: GEnv Component

  -- G condition: lookupG G₂' (rename e') = (lookupG G₁' e').map rename
  · intro e'
    by_cases he : e' = ep
    · -- Case: e' = ep (the updated endpoint)
      obtain ⟨L', hSender₁⟩ := hSpec₁.sender_type
      have hG₁' := hSpec₁.type_updated L' hSender₁
      obtain ⟨L'₂, hSender₂⟩ := hSpec₂.sender_type
      have hG₂' := hSpec₂.type_updated L'₂ hSender₂
      -- Get the renamed sender type in G₂ to determine L'₂
      have hSender₂_raw := hG_equiv ep
      rw [hSender₁] at hSender₂_raw
      simp only [Option.map_some, renameLocalType] at hSender₂_raw
      rw [hSender₂_raw] at hSender₂
      simp only [Option.some.injEq, LocalType.send.injEq] at hSender₂
      obtain ⟨_, _, hL'₂_eq⟩ := hSender₂
      -- Compute both sides using he : e' = ep
      calc lookupG G₂' (renameEndpoint ρ e')
          = lookupG G₂' (renameEndpoint ρ ep) := by rw [he]
        _ = lookupG (updateG G₂ (renameEndpoint ρ ep) L'₂) (renameEndpoint ρ ep) := by rw [hG₂']
        _ = some L'₂ := lookupG_update_eq _ _ _
        _ = some (renameLocalType ρ L') := by rw [hL'₂_eq]
        _ = (some L').map (renameLocalType ρ) := by simp only [Option.map_some]
        _ = (lookupG (updateG G₁ ep L') ep).map (renameLocalType ρ) := by
            rw [lookupG_update_eq]
        _ = (lookupG G₁' ep).map (renameLocalType ρ) := by rw [← hG₁']
        _ = (lookupG G₁' e').map (renameLocalType ρ) := by rw [← he]
    · -- Case: e' ≠ ep (frame)
      have hne₂ : renameEndpoint ρ e' ≠ renameEndpoint ρ ep := by
        intro heq
        exact he (renameEndpoint_inj ρ e' ep heq)
      rw [hSpec₁.frame_G e' he, hSpec₂.frame_G (renameEndpoint ρ e') hne₂]
      exact hG_equiv e'

  -- Send ConfigEquiv Preservation: DEnv Component

  -- D condition: lookupD D₂' (rename e') = (lookupD D₁' e').map rename
  · intro e'
    let sendEdge : Edge := { sid := ep.sid, sender := ep.role, receiver := r }
    by_cases he : e' = sendEdge
    · -- Case: e' = sendEdge (the updated edge)
      have hD₁' := hSpec₁.trace_extended
      have hD₂' := hSpec₂.trace_extended
      simp only at hD₁' hD₂'
      simp only [renameEndpoint] at hD₂'
/- ## Structured Block 2 -/
      have hTrace := hD_equiv sendEdge
      simp only [renameEdge] at hTrace
      -- Rewrite goal with he, then use the update equations
      rw [he]
      simp only [renameEdge]
      rw [hD₁', hD₂', lookupD_update_eq, lookupD_update_eq]
      -- Now show: (trace ++ [T]).map rename = (trace.map rename) ++ [rename T]
      simp only [List.map_append, List.map_cons, List.map_nil]
      -- Apply hTrace to match the trace lookups
      rw [hTrace]
    · -- Case: e' ≠ sendEdge (frame)
      have hne₂ : renameEdge ρ e' ≠ renameEdge ρ sendEdge := by
        intro heq
        exact he (renameEdge_inj ρ e' sendEdge heq)
      simp only [renameEdge] at hne₂
      rw [hSpec₁.frame_D e' he, hSpec₂.frame_D (renameEdge ρ e') hne₂]
      exact hD_equiv e'

-- Recv Renaming Equivariance

/-- Receive is equivariant under session renaming. -/
theorem RecvSpec_respects_renaming (ρ : SessionRenaming)
    {G G' : GEnv} {D D' : DEnv} {ep : Endpoint} {r : Role} {T : ValType}
    (hSpec : RecvSpec G G' D D' ep r T) :
    RecvSpec (renameGEnv ρ G) (renameGEnv ρ G') (renameDEnv ρ D) (renameDEnv ρ D')
             (renameEndpoint ρ ep) r (renameValType ρ T) where
  receiver_type := by
    obtain ⟨L', hRecv⟩ := hSpec.receiver_type
    use renameLocalType ρ L'
    rw [lookupG_rename, hRecv]
    simp only [Option.map_some, renameLocalType]
  buffer_has_data := by
    obtain ⟨rest, hBuffer⟩ := hSpec.buffer_has_data
    use rest.map (renameValType ρ)
    simp only [renameEndpoint]
    have hLookup := lookupD_rename (ρ := ρ) (D := D) (e := { sid := ep.sid, sender := r, receiver := ep.role })
    simp only [renameEdge] at hLookup
    rw [hLookup, hBuffer]
    simp only [List.map_cons]
  type_updated := by
    intro L'_renamed hRecv_renamed
    rw [lookupG_rename] at hRecv_renamed
    obtain ⟨L', hRecv⟩ := hSpec.receiver_type
    rw [hRecv] at hRecv_renamed
    simp only [Option.map_some, renameLocalType] at hRecv_renamed
    have hL'_eq : L'_renamed = renameLocalType ρ L' := by
      cases hRecv_renamed
      rfl
    have hG' := hSpec.type_updated L' hRecv
    rw [hG', renameGEnv_updateG, hL'_eq]

  -- Recv Renaming Equivariance: Trace and Frame Clauses

  trace_consumed := by
    obtain ⟨rest, hBuffer, hD'⟩ := hSpec.trace_consumed
    use rest.map (renameValType ρ)
    simp only [renameEndpoint]
    have hLookup := lookupD_rename (ρ := ρ) (D := D) (e := { sid := ep.sid, sender := r, receiver := ep.role })
    simp only [renameEdge] at hLookup
    constructor
/- ## Structured Block 3 -/
    · rw [hLookup, hBuffer]
      simp only [List.map_cons]
    · rw [hD', renameDEnv_updateD]
      simp only [renameEdge]
  frame_G := by
    intro ep' hne
    obtain ⟨L', hRecv⟩ := hSpec.receiver_type
    have hG' := hSpec.type_updated L' hRecv
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

-- Recv ConfigEquiv Preservation

/-- Receive respects ConfigEquiv. -/
theorem RecvSpec_respects_ConfigEquiv
    {G₁ G₁' G₂ G₂' : GEnv} {D₁ D₁' D₂ D₂' : DEnv}
    {ep : Endpoint} {r : Role} {T : ValType}
    (hEquiv : ConfigEquiv ⟨G₁, D₁⟩ ⟨G₂, D₂⟩)
    (hSpec₁ : RecvSpec G₁ G₁' D₁ D₁' ep r T)
    (hSpec₂ : RecvSpec G₂ G₂' D₂ D₂'
              (renameEndpoint (hEquiv.choose.toRenaming) ep) r
              (renameValType hEquiv.choose.toRenaming T)) :
    ConfigEquiv ⟨G₁', D₁'⟩ ⟨G₂', D₂'⟩ := by

  -- Recv ConfigEquiv Preservation: Shared Setup

  -- Use the same SessionIso that witnesses the input equivalence.
  let σ := hEquiv.choose
  let ρ := σ.toRenaming
  obtain ⟨hG_equiv, hD_equiv⟩ := hEquiv.choose_spec
  refine ⟨σ, ?_, ?_⟩

  -- Recv ConfigEquiv Preservation: GEnv Component

  -- G condition
  · intro e'
    by_cases he : e' = ep
    · -- Case: e' = ep (the updated endpoint)
      obtain ⟨L', hRecv₁⟩ := hSpec₁.receiver_type
      have hG₁' := hSpec₁.type_updated L' hRecv₁
      obtain ⟨L'₂, hRecv₂⟩ := hSpec₂.receiver_type
      have hG₂' := hSpec₂.type_updated L'₂ hRecv₂
      -- Determine L'₂ from input equivalence
      have hRecv₂_raw := hG_equiv ep
      rw [hRecv₁] at hRecv₂_raw
      simp only [Option.map_some, renameLocalType] at hRecv₂_raw
      rw [hRecv₂_raw] at hRecv₂
      simp only [Option.some.injEq, LocalType.recv.injEq] at hRecv₂
      obtain ⟨_, _, hL'₂_eq⟩ := hRecv₂
      -- Compute both sides
      calc lookupG G₂' (renameEndpoint ρ e')
          = lookupG G₂' (renameEndpoint ρ ep) := by rw [he]
        _ = lookupG (updateG G₂ (renameEndpoint ρ ep) L'₂) (renameEndpoint ρ ep) := by rw [hG₂']
        _ = some L'₂ := lookupG_update_eq _ _ _
/- ## Structured Block 4 -/
        _ = some (renameLocalType ρ L') := by rw [hL'₂_eq]
        _ = (some L').map (renameLocalType ρ) := by simp only [Option.map_some]
        _ = (lookupG (updateG G₁ ep L') ep).map (renameLocalType ρ) := by rw [lookupG_update_eq]
        _ = (lookupG G₁' ep).map (renameLocalType ρ) := by rw [← hG₁']
        _ = (lookupG G₁' e').map (renameLocalType ρ) := by rw [← he]
    · -- Case: e' ≠ ep (frame)
      have hne₂ : renameEndpoint ρ e' ≠ renameEndpoint ρ ep := by
        intro heq; exact he (renameEndpoint_inj ρ e' ep heq)
      rw [hSpec₁.frame_G e' he, hSpec₂.frame_G (renameEndpoint ρ e') hne₂]
      exact hG_equiv e'

  -- Recv ConfigEquiv Preservation: DEnv Component

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
      -- rest₁ and rest₂ are the tails after consuming T
      -- From hBuf₁: lookupD D₁ recvEdge = T :: rest₁
      -- From hTrace: lookupD D₂ (rename recvEdge) = (lookupD D₁ recvEdge).map rename
      --            = (T :: rest₁).map rename = renameT :: rest₁.map rename
      -- From hBuf₂: lookupD D₂ (rename recvEdge) = renameT :: rest₂
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
