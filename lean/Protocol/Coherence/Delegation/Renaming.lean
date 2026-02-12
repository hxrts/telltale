import Protocol.Coherence.Delegation.Preservation

/-! # Protocol.Coherence.Delegation.Renaming

Delegation-step renaming-respect lemmas.
-/

/-
The Problem. Delegation preservation must commute with session renaming to be
usable in symmetry/refactoring proofs.

Solution Structure. Isolates renaming-respect lemmas for delegation steps.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ## Modular Delegation Renaming Proofs -/

theorem DelegationStep_A_lookup_renaming (ρ : SessionRenaming)
    {G : GEnv} {s : SessionId} {A : Role} {A_type : LocalType}
    (hLookup : lookupG G ⟨s, A⟩ = some A_type) :
    lookupG (renameGEnv ρ G) ⟨ρ.f s, A⟩ = some (renameLocalType ρ A_type) := by
  have hEq : ({ sid := ρ.f s, role := A } : Endpoint) = renameEndpoint ρ { sid := s, role := A } := by
    simp only [renameEndpoint]
  rw [hEq, lookupG_rename, hLookup]
  simp only [Option.map_some]

theorem DelegationStep_A_removed_renaming (ρ : SessionRenaming)
    {G' : GEnv} {s : SessionId} {A : Role}
    (hRemoved : lookupG G' ⟨s, A⟩ = none) :
    lookupG (renameGEnv ρ G') ⟨ρ.f s, A⟩ = none := by
  have hEq : ({ sid := ρ.f s, role := A } : Endpoint) = renameEndpoint ρ { sid := s, role := A } := by
    simp only [renameEndpoint]
  rw [hEq, lookupG_rename, hRemoved]
  simp only [Option.map_none]

theorem DelegationStep_B_added_renaming (ρ : SessionRenaming)
    {G' : GEnv} {s : SessionId} {A B : Role} {A_type : LocalType}
    (hAdded : lookupG G' ⟨s, B⟩ = some (renameLocalTypeRole s A B A_type)) :
    lookupG (renameGEnv ρ G') ⟨ρ.f s, B⟩ =
      some (renameLocalTypeRole (ρ.f s) A B (renameLocalType ρ A_type)) := by
  have hEq : ({ sid := ρ.f s, role := B } : Endpoint) = renameEndpoint ρ { sid := s, role := B } := by
    simp only [renameEndpoint]
  rw [hEq, lookupG_rename, hAdded]
  simp only [Option.map_some]
  congr 1
  exact renameLocalType_renameLocalTypeRole_comm ρ s A B A_type

/-! ## Renaming Transport for `other_roles_G` / `other_sessions_G` -/

theorem DelegationStep_other_roles_G_renaming (ρ : SessionRenaming)
    {G G' : GEnv} {s : SessionId} {A B : Role}
    (hOrig : ∀ ep, ep.sid = s → ep.role ≠ A → ep.role ≠ B →
      lookupG G' ep = (lookupG G ep).map (renameLocalTypeRole s A B))
    (ep : Endpoint) (hSid : ep.sid = ρ.f s) (hNeA : ep.role ≠ A) (hNeB : ep.role ≠ B) :
    lookupG (renameGEnv ρ G') ep =
      (lookupG (renameGEnv ρ G) ep).map (renameLocalTypeRole (ρ.f s) A B) := by
  let ep' : Endpoint := { sid := s, role := ep.role }
  have hEpEq : ep = renameEndpoint ρ ep' := by
    simp only [renameEndpoint, ep']
    cases ep with
    | mk sid role =>
      simp only [Endpoint.mk.injEq]
      simp only at hSid
      simp [hSid]
  rw [hEpEq, lookupG_rename, lookupG_rename]
  have hOther := hOrig ep' rfl hNeA hNeB
  rw [hOther]
  simp only [Option.map_map]
  congr 1
  funext L
  exact renameLocalType_renameLocalTypeRole_comm ρ s A B L

/-! ## Renaming Transport for `other_sessions_G` -/

theorem DelegationStep_other_sessions_G_renaming (ρ : SessionRenaming)
    {G G' : GEnv} {s : SessionId}
    (hOrig : ∀ ep, ep.sid ≠ s → lookupG G' ep = lookupG G ep)
    (ep : Endpoint) (hSid : ep.sid ≠ ρ.f s) :
    lookupG (renameGEnv ρ G') ep = lookupG (renameGEnv ρ G) ep := by
  cases hLookup : lookupG (renameGEnv ρ G) ep with
  | none =>
    cases hLookup' : lookupG (renameGEnv ρ G') ep with
    | none => rfl
    | some L' =>
      obtain ⟨ep', _, hEpEq, _, hLookupG'⟩ := lookupG_rename_inv ρ G' ep L' hLookup'
      have hSid' : ep'.sid ≠ s := endpoint_preimage_sid_ne ρ ep ep' s hSid hEpEq
      have hOther := hOrig ep' hSid'
      rw [hOther] at hLookupG'
      have hContra : lookupG (renameGEnv ρ G) ep = (lookupG G ep').map (renameLocalType ρ) := by
        rw [hEpEq, lookupG_rename]
      rw [hLookupG'] at hContra
      simp only [Option.map_some] at hContra
      rw [hLookup] at hContra
      exact Option.noConfusion hContra
  | some L =>
    obtain ⟨ep', _, hEpEq, hL, hLookupG⟩ := lookupG_rename_inv ρ G ep L hLookup
    have hSid' : ep'.sid ≠ s := endpoint_preimage_sid_ne ρ ep ep' s hSid hEpEq
    have hOther := hOrig ep' hSid'
    have hResult : lookupG (renameGEnv ρ G') ep = (lookupG G' ep').map (renameLocalType ρ) := by
      rw [hEpEq, lookupG_rename]
    rw [hOther, hLookupG] at hResult
    simp only [Option.map_some] at hResult
    rw [hResult, hL]

/-! ## Renaming Transport for `other_sessions_D` / `A_incident_empty` -/

theorem DelegationStep_other_sessions_D_renaming (ρ : SessionRenaming)
    {D D' : DEnv} {s : SessionId}
    (hOrig : ∀ e, e.sid ≠ s → lookupD D' e = lookupD D e)
    (e : Edge) (hSid : e.sid ≠ ρ.f s) :
    lookupD (renameDEnv ρ D') e = lookupD (renameDEnv ρ D) e := by
  by_cases hEmpty : lookupD (renameDEnv ρ D) e = []
  · by_cases hEmpty' : lookupD (renameDEnv ρ D') e = []
    · simp only [hEmpty, hEmpty']
    · obtain ⟨e₀, hEeq, hLookupD'⟩ := lookupD_rename_inv ρ D' e hEmpty'
      have hSid' : e₀.sid ≠ s := preimage_sid_ne ρ e e₀ s hSid hEeq
      have hOther := hOrig e₀ hSid'
      have hContra : lookupD (renameDEnv ρ D) e = (lookupD D e₀).map (renameValType ρ) := by
        rw [hEeq, lookupD_rename]
      -- From hEmpty and hContra: (lookupD D e₀).map (renameValType ρ) = []
      have hMapEmpty : (lookupD D e₀).map (renameValType ρ) = [] := by
        rw [← hContra, hEmpty]
      -- From hOther and hLookupD': lookupD (renameDEnv ρ D') e = (lookupD D e₀).map (renameValType ρ)
      rw [hOther] at hLookupD'
      -- So lookupD (renameDEnv ρ D') e = [], contradicting hEmpty'
      have hD'Empty : lookupD (renameDEnv ρ D') e = [] := by
        rw [hLookupD', hMapEmpty]
      exact (hEmpty' hD'Empty).elim
  · obtain ⟨e₀, hEeq, hLookupD⟩ := lookupD_rename_inv ρ D e hEmpty
    have hSid' : e₀.sid ≠ s := preimage_sid_ne ρ e e₀ s hSid hEeq
    have hOther := hOrig e₀ hSid'
    have hResult : lookupD (renameDEnv ρ D') e = (lookupD D' e₀).map (renameValType ρ) := by
      rw [hEeq, lookupD_rename]
    rw [hOther] at hResult
    rw [hLookupD, hResult]

theorem DelegationStep_A_incident_empty_renaming (ρ : SessionRenaming)
    {D' : DEnv} {s : SessionId} {A : Role}
    (hOrig : ∀ e, e.sid = s → (e.sender = A ∨ e.receiver = A) → lookupD D' e = [])
    (e : Edge) (hSid : e.sid = ρ.f s) (hInc : e.sender = A ∨ e.receiver = A) :
    lookupD (renameDEnv ρ D') e = [] := by
  let e₀ : Edge := { sid := s, sender := e.sender, receiver := e.receiver }
  have hEeq : e = renameEdge ρ e₀ := by
    simp only [renameEdge, e₀]
    cases e with
    | mk sid sender receiver =>
      simp only [Edge.mk.injEq, and_self, and_true]
      simpa using hSid
  have hOrigEmpty : lookupD D' e₀ = [] := hOrig e₀ rfl hInc
  rw [hEeq, lookupD_rename, hOrigEmpty]
  simp

/-! ## Renaming Transport for `trace_preserved` (Other Session) -/

/-- Helper for trace_preserved when edge is NOT in the renamed session. -/
theorem DelegationStep_trace_preserved_other_session (ρ : SessionRenaming)
    {D D' : DEnv} {s : SessionId} {A B : Role}
    (hOrigTrace : ∀ e e', IsRedirectedEdge e e' s A B →
      lookupD D' e' = (lookupD D e).map (renameValTypeRole s A B))
    (e : Edge) (hSid : e.sid ≠ ρ.f s) :
    lookupD (renameDEnv ρ D') e = (lookupD (renameDEnv ρ D) e).map (renameValTypeRole (ρ.f s) A B) := by
  -- When e.sid ≠ ρ.f s, redirection is identity in the renamed space
  by_cases hEmpty : lookupD (renameDEnv ρ D) e = []
  · by_cases hEmpty' : lookupD (renameDEnv ρ D') e = []
    · simp only [hEmpty, hEmpty', List.map_nil]
    · obtain ⟨e₀, hEeq, _⟩ := lookupD_rename_inv ρ D' e hEmpty'
      have hSid' : e₀.sid ≠ s := preimage_sid_ne ρ e e₀ s hSid hEeq
      have hRedir₀ : IsRedirectedEdge e₀ e₀ s A B := by
        simp only [IsRedirectedEdge, redirectEdge]
        have hBeq : (e₀.sid == s) = false := beq_eq_false_iff_ne.mpr hSid'
        simp only [hBeq, Bool.false_eq_true, ↓reduceIte]
      have hOrig := hOrigTrace e₀ e₀ hRedir₀
      rw [hEeq, lookupD_rename, lookupD_rename, hOrig]
      simp only [List.map_map]
      congr 1
      funext T
      exact renameValType_renameValTypeRole_comm ρ s A B T
  · obtain ⟨e₀, hEeq, hLookupD⟩ := lookupD_rename_inv ρ D e hEmpty
    have hSid' : e₀.sid ≠ s := preimage_sid_ne ρ e e₀ s hSid hEeq
    have hRedir₀ : IsRedirectedEdge e₀ e₀ s A B := by
      simp only [IsRedirectedEdge, redirectEdge]
      have hBeq : (e₀.sid == s) = false := beq_eq_false_iff_ne.mpr hSid'
      simp only [hBeq, Bool.false_eq_true, ↓reduceIte]
    have hOrig := hOrigTrace e₀ e₀ hRedir₀
    rw [hEeq, lookupD_rename, lookupD_rename, hOrig]
    simp only [List.map_map]
    congr 1
    funext T
    exact renameValType_renameValTypeRole_comm ρ s A B T

/-! ## Renaming Transport for `trace_preserved` (In Session) -/

/-- Helper for trace_preserved when edge IS in the renamed session. -/
theorem DelegationStep_trace_preserved_in_session (ρ : SessionRenaming)
    {D D' : DEnv} {s : SessionId} {A B : Role}
    (hOrigTrace : ∀ e e', IsRedirectedEdge e e' s A B →
      lookupD D' e' = (lookupD D e).map (renameValTypeRole s A B))
    (e e' : Edge) (hRedir : e' = redirectEdge e (ρ.f s) A B) (hSid : e.sid = ρ.f s) :
    lookupD (renameDEnv ρ D') e' = (lookupD (renameDEnv ρ D) e).map (renameValTypeRole (ρ.f s) A B) := by
  -- Construct preimages with sid = s
  let e₀ : Edge := { sid := s, sender := e.sender, receiver := e.receiver }
  have hEeq : e = renameEdge ρ e₀ := edge_preimage_of_sid_eq ρ e s hSid
  have hE'sid : e'.sid = ρ.f s := by
    simp only [hRedir, redirectEdge, hSid, beq_self_eq_true, ↓reduceIte]
  let e₀' : Edge := { sid := s, sender := e'.sender, receiver := e'.receiver }
  have hE'eq : e' = renameEdge ρ e₀' := edge_preimage_of_sid_eq ρ e' s hE'sid
  -- Show IsRedirectedEdge e₀ e₀' s A B
  have hRedir' : IsRedirectedEdge e₀ e₀' s A B := by
    simp only [IsRedirectedEdge, redirectEdge, beq_self_eq_true, ↓reduceIte, e₀, e₀']
    simp only [hRedir, redirectEdge, hSid, beq_self_eq_true, ↓reduceIte]
  have hOrig := hOrigTrace e₀ e₀' hRedir'
  rw [hEeq, hE'eq, lookupD_rename, lookupD_rename, hOrig]
  simp only [List.map_map]
  congr 1
  funext T
  exact renameValType_renameValTypeRole_comm ρ s A B T

/-! ## Renaming Equivariance of `DelegationStep` -/

/-- DelegationStep is equivariant under session renaming. -/
def DelegationStep_respects_renaming (ρ : SessionRenaming)
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role}
    (hDeleg : DelegationStep G G' D D' s A B) :
    DelegationStep (renameGEnv ρ G) (renameGEnv ρ G') (renameDEnv ρ D) (renameDEnv ρ D')
                   (ρ.f s) A B where
  wf := DelegationWF_respects_renaming ρ hDeleg.wf
  A_type := renameLocalType ρ hDeleg.A_type
  A_lookup := DelegationStep_A_lookup_renaming ρ hDeleg.A_lookup
  A_removed := DelegationStep_A_removed_renaming ρ hDeleg.A_removed
  B_added := DelegationStep_B_added_renaming ρ hDeleg.B_added
  other_roles_G := DelegationStep_other_roles_G_renaming ρ hDeleg.other_roles_G
  other_sessions_G := DelegationStep_other_sessions_G_renaming ρ hDeleg.other_sessions_G
  trace_preserved := by
    intro e e' hRedir
    simp only [IsRedirectedEdge] at hRedir
    by_cases hSid : e.sid = ρ.f s
    · exact DelegationStep_trace_preserved_in_session ρ hDeleg.trace_preserved e e' hRedir hSid
    · have hE'eq : e' = e := by
        simp only [hRedir, redirectEdge]
        have hBeq : (e.sid == ρ.f s) = false := beq_eq_false_iff_ne.mpr hSid
        simp only [hBeq, Bool.false_eq_true, ↓reduceIte]
      rw [hE'eq]
      exact DelegationStep_trace_preserved_other_session ρ hDeleg.trace_preserved e hSid
  other_sessions_D := DelegationStep_other_sessions_D_renaming ρ hDeleg.other_sessions_D
  A_incident_empty := by
    intro e hSid hInc
    exact DelegationStep_A_incident_empty_renaming ρ hDeleg.A_incident_empty e hSid hInc


end
