import Runtime.Proofs.VM.InstrSpec.ConfigEquivOpenCloseTransfer

/-! # ConfigEquiv: Acquire Instruction

Session renaming equivariance for the acquire instruction, showing
that capability delegation respects configuration equivalence. -/

/-
The Problem. The acquire instruction delegates a capability from one
session to another. For configuration equivalence, we need to show
that if AcquireSpec holds, it still holds after renaming all session
IDs consistently.

Solution Structure. Prove `AcquireSpec_respects_renaming` by showing
each spec component (receiver_type, buffer_has_capability, type_updated)
transforms correctly under session renaming.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Classical

section

-- Acquire Renaming Equivariance

-- AcquireSpec Renaming Preservation

def AcquireSpec_respects_renaming (ρ : SessionRenaming)
    {G G' : GEnv} {D D' : DEnv}
    {ep : Endpoint} {r : Role} {delegatedSession : SessionId} {delegatedRole : Role}
    (hSpec : AcquireSpec G G' D D' ep r delegatedSession delegatedRole) :
    AcquireSpec (renameGEnv ρ G) (renameGEnv ρ G') (renameDEnv ρ D) (renameDEnv ρ D')
                (renameEndpoint ρ ep) r (ρ.f delegatedSession) delegatedRole where
  receiver_type := by
    obtain ⟨L', hLookup⟩ := hSpec.receiver_type
    refine ⟨renameLocalType ρ L', ?_⟩
    rw [lookupG_rename]
    simp only [hLookup, Option.map_some, renameLocalType, renameValType]
  buffer_has_capability := by
    obtain ⟨rest, hLookup⟩ := hSpec.buffer_has_capability
    refine ⟨rest.map (renameValType ρ), ?_⟩
    -- The edge in the renamed spec is { sid := (renameEndpoint ρ ep).sid, sender := r, receiver := (renameEndpoint ρ ep).role }
    -- which equals renameEdge ρ { sid := ep.sid, sender := r, receiver := ep.role }
    have hEdge : { sid := (renameEndpoint ρ ep).sid, sender := r, receiver := (renameEndpoint ρ ep).role } =
                 renameEdge ρ { sid := ep.sid, sender := r, receiver := ep.role } := by
      simp only [renameEndpoint, renameEdge]
    rw [hEdge, lookupD_rename, hLookup]
    simp only [List.map_cons, renameValType]

  -- AcquireSpec Renaming: Type-Update Case

  type_updated := by
    intro L' hLookup'
    -- L' is the continuation in the renamed space
    -- We need to find the original continuation and apply type_updated
    rw [lookupG_rename] at hLookup'
    cases hOrig : lookupG G ep with
    | none => simp [hOrig] at hLookup'
    | some Lorig =>
      simp only [hOrig, Option.map_some] at hLookup'
      have hEq := Option.some.inj hLookup'
      -- Lorig should be .recv r (.chan delegatedSession delegatedRole) L'_orig
      -- where L' = renameLocalType ρ L'_orig
      cases Lorig with
      | recv r' T' L'_orig =>
        simp only [renameLocalType] at hEq
        have ⟨hr, hT, hL⟩ := LocalType.recv.inj hEq
        -- T' must be a chan for hT to be valid
        cases T' with
        | chan sid role =>
          simp only [renameValType] at hT
          have hT' := ValType.chan.inj hT
          have hSid := ρ.inj _ _ hT'.1.symm
          -- Apply type_updated with the original L'_orig
          have hLookupOrig : lookupG G ep = some (.recv r (.chan delegatedSession delegatedRole) L'_orig) := by
            simp only [hOrig, ← hr, ← hSid, ← hT'.2]
          have hUpd := hSpec.type_updated L'_orig hLookupOrig
          rw [hUpd, renameGEnv_updateG]
          simp only [← hL]
        | unit => simp only [renameValType] at hT; nomatch hT
        | bool => simp only [renameValType] at hT; nomatch hT
        | nat => simp only [renameValType] at hT; nomatch hT
        | string => simp only [renameValType] at hT; nomatch hT
        | prod _ _ => simp only [renameValType] at hT; nomatch hT
      | send _ _ _ => simp only [renameLocalType] at hEq; nomatch hEq
      | select _ _ => simp only [renameLocalType] at hEq; nomatch hEq
      | branch _ _ => simp only [renameLocalType] at hEq; nomatch hEq
      | end_ => simp only [renameLocalType] at hEq; nomatch hEq
      | var _ => simp only [renameLocalType] at hEq; nomatch hEq
      | mu _ => simp only [renameLocalType] at hEq; nomatch hEq

  -- AcquireSpec Renaming: Delegation Step

  delegation_applied :=
    DelegationStep_respects_renaming ρ hSpec.delegation_applied

/-- Acquire respects `ConfigEquiv` constructively. -/
theorem AcquireSpec_respects_ConfigEquiv
    {G₁ G₁' G₂ G₂' : GEnv} {D₁ D₁' D₂ D₂' : DEnv}
    {ep : Endpoint} {r : Role} {delegatedSession : SessionId} {delegatedRole : Role}
    (hEquiv : ConfigEquiv ⟨G₁, D₁⟩ ⟨G₂, D₂⟩)
    (hSpec₁ : AcquireSpec G₁ G₁' D₁ D₁' ep r delegatedSession delegatedRole)
    (hSpec₂ : AcquireSpec G₂ G₂' D₂ D₂'
              (renameEndpoint (hEquiv.choose.toRenaming) ep) r
              (hEquiv.choose.fwd delegatedSession) delegatedRole) :
    ConfigEquiv ⟨G₁', D₁'⟩ ⟨G₂', D₂'⟩ := by

  -- ConfigEquiv Preservation: Shared Setup

  let σ := hEquiv.choose
  let ρ := σ.toRenaming
  obtain ⟨hG, hD⟩ := hEquiv.choose_spec
  let hDeleg₁ := hSpec₁.delegation_applied
  let hDeleg₂ := hSpec₂.delegation_applied
  have hATypeEq : hDeleg₂.A_type = renameLocalType ρ hDeleg₁.A_type := by
    have hAlookup₂ : lookupG G₂ { sid := ρ.f delegatedSession, role := r } = some hDeleg₂.A_type := by
      simpa [ρ] using hDeleg₂.A_lookup
    have hLookupEq :
        lookupG G₂ { sid := ρ.f delegatedSession, role := r } =
          (lookupG G₁ { sid := delegatedSession, role := r }).map (renameLocalType ρ) := by
      simpa [ρ] using hG { sid := delegatedSession, role := r }
    have hLookupEq' : some hDeleg₂.A_type = (some hDeleg₁.A_type).map (renameLocalType ρ) := by
      rw [← hAlookup₂, hLookupEq, hDeleg₁.A_lookup]
    simpa using Option.some.inj hLookupEq'

  -- ConfigEquiv Preservation: GEnv Component

  refine ⟨σ, ?_, ?_⟩
  · intro e
    by_cases hSid : e.sid = delegatedSession
    · by_cases hA : e.role = r
      · have hA' : e = { sid := delegatedSession, role := r } := by
          cases e
          simp only [Endpoint.mk.injEq]
          exact ⟨hSid, hA⟩
        rw [hA']
        simp only [renameEndpoint]
        have hAremoved₂ : lookupG G₂' { sid := ρ.f delegatedSession, role := r } = none := by
          simpa [ρ] using hDeleg₂.A_removed
        rw [hDeleg₁.A_removed, hAremoved₂]
        simp
      · by_cases hB : e.role = ep.role
        · have hB' : e = { sid := delegatedSession, role := ep.role } := by
            cases e
            simp only [Endpoint.mk.injEq]
            exact ⟨hSid, hB⟩
          rw [hB']
          simp only [renameEndpoint]
          have hBadded₂ :
              lookupG G₂' { sid := ρ.f delegatedSession, role := ep.role } =
                some (renameLocalTypeRole (ρ.f delegatedSession) r ep.role hDeleg₂.A_type) := by
            simpa [ρ] using hDeleg₂.B_added
          rw [hDeleg₁.B_added, hBadded₂]
          simp only [Option.map_some]
          rw [hATypeEq]
          congr 1
          exact (renameLocalType_renameLocalTypeRole_comm ρ delegatedSession r ep.role hDeleg₁.A_type).symm
        · have hOther₁ := hDeleg₁.other_roles_G e hSid hA hB
          have hSidRen : (renameEndpoint ρ e).sid = ρ.f delegatedSession := by
            simp only [renameEndpoint, hSid]
          have hOther₂ := hDeleg₂.other_roles_G (renameEndpoint ρ e) hSidRen hA hB
          rw [hOther₁, hOther₂, hG]
          simp only [Option.map_map]
          congr 1
          funext L
          exact (renameLocalType_renameLocalTypeRole_comm ρ delegatedSession r ep.role L).symm
    · have hSidRen : (renameEndpoint ρ e).sid ≠ ρ.f delegatedSession := by
        simp only [renameEndpoint]
        intro hEq
        exact hSid (ρ.inj _ _ hEq)
      rw [hDeleg₁.other_sessions_G e hSid, hDeleg₂.other_sessions_G (renameEndpoint ρ e) hSidRen]
      exact hG e

  -- ConfigEquiv Preservation: DEnv Component

  · intro e
    by_cases hSid : e.sid = delegatedSession
    · by_cases hInc : e.sender = r ∨ e.receiver = r
      · have hEmpty₁ : lookupD D₁' e = [] := hDeleg₁.A_incident_empty e hSid hInc
        have hSidRen : (renameEdge ρ e).sid = ρ.f delegatedSession := by
          simp only [renameEdge, hSid]
        have hIncRen : (renameEdge ρ e).sender = r ∨ (renameEdge ρ e).receiver = r := by
          simpa [renameEdge] using hInc
        have hEmpty₂ : lookupD D₂' (renameEdge ρ e) = [] :=
          hDeleg₂.A_incident_empty (renameEdge ρ e) hSidRen hIncRen
        rw [hEmpty₁, hEmpty₂]
        simp

      -- ConfigEquiv Preservation: DEnv Non-Incident Edge Case

      · have hSenderNe : e.sender ≠ r := by
          intro hEq
          exact hInc (Or.inl hEq)
        have hReceiverNe : e.receiver ≠ r := by
          intro hEq
          exact hInc (Or.inr hEq)
        have hRedir₁ : IsRedirectedEdge e e delegatedSession r ep.role := by
          rw [IsRedirectedEdge]
          exact (redirectEdge_no_A e delegatedSession r ep.role hSid hSenderNe hReceiverNe).symm
        have hD₁' :
            lookupD D₁' e =
              (lookupD D₁ e).map (renameValTypeRole delegatedSession r ep.role) :=
          hDeleg₁.trace_preserved e e hRedir₁
        have hSidRen : (renameEdge ρ e).sid = ρ.f delegatedSession := by
          simp only [renameEdge, hSid]
        have hSenderNeRen : (renameEdge ρ e).sender ≠ r := by
          simpa [renameEdge] using hSenderNe
        have hReceiverNeRen : (renameEdge ρ e).receiver ≠ r := by
          simpa [renameEdge] using hReceiverNe
        have hRedir₂ :
            IsRedirectedEdge (renameEdge ρ e) (renameEdge ρ e) (ρ.f delegatedSession) r ep.role := by
          rw [IsRedirectedEdge]
          exact (redirectEdge_no_A (renameEdge ρ e) (ρ.f delegatedSession) r ep.role
            hSidRen hSenderNeRen hReceiverNeRen).symm
        have hD₂' :
            lookupD D₂' (renameEdge ρ e) =
              (lookupD D₂ (renameEdge ρ e)).map (renameValTypeRole (ρ.f delegatedSession) r ep.role) :=
          hDeleg₂.trace_preserved (renameEdge ρ e) (renameEdge ρ e) hRedir₂
        rw [hD₂', hD e, hD₁']
        simp only [List.map_map]
        congr 1
        funext T
        exact (renameValType_renameValTypeRole_comm ρ delegatedSession r ep.role T).symm
    · have hSidRen : (renameEdge ρ e).sid ≠ ρ.f delegatedSession := by
        simp only [renameEdge]
        intro hEq
        exact hSid (ρ.inj _ _ hEq)
      rw [hDeleg₂.other_sessions_D (renameEdge ρ e) hSidRen, hDeleg₁.other_sessions_D e hSid]
      exact hD e

-- Instruction-Basis Exactness Interfaces

end
