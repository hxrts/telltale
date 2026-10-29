import Protocol.CrashToleranceCore
import Runtime.ProtocolMachine.Runtime.Failure

/-! # Crash Tolerance for the Protocol Machine

Connects the graph-level crash-tolerance theory of `Protocol.CrashToleranceCore`
to `ProtocolMachineState` and the failure-aware step relation `FStep`.
-/

/-
The Problem. Lift residual-graph crash tolerance to protocol machine states and
show which failure steps preserve it.

Solution Structure. Project sites to crashed roles, extract session graphs,
prove graph invariance under topology-only steps and close-on-crash, and
preserve tolerance across `FStep` with explicit per-case side conditions.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section

universe u

/-! ## Connection to FStep and ProtocolMachineState -/

section ProtocolMachineConnection

variable {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
  [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
  [AuthTree ν] [AccumulatedSet ν]
  [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
  [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
  [IdentityVerificationBridge ι ν]

/-! ## Site-to-Role Crash Projection -/

/-- A role is crashed iff it is hosted by at least one crashed site and every
    site hosting it has crashed. A role mapped to no site is never crashed. -/
def RoleCrashedBySites (siteToRoles : IdentityModel.SiteId ι → List Role)
    (crashedSites : List (IdentityModel.SiteId ι)) (r : Role) : Prop :=
  (∃ s ∈ crashedSites, r ∈ siteToRoles s) ∧ ∀ s, r ∈ siteToRoles s → s ∈ crashedSites

/-- An unmapped role is not crashed. -/
theorem not_role_crashed_of_unmapped (siteToRoles : IdentityModel.SiteId ι → List Role)
    (crashedSites : List (IdentityModel.SiteId ι)) (r : Role)
    (hUnmapped : ∀ s, r ∉ siteToRoles s) : ¬ RoleCrashedBySites siteToRoles crashedSites r := by
  rintro ⟨⟨s, _, hs⟩, _⟩
  exact hUnmapped s hs

/-- With no crashed sites, no role is crashed. -/
theorem not_role_crashed_of_no_crashes (siteToRoles : IdentityModel.SiteId ι → List Role)
    (r : Role) : ¬ RoleCrashedBySites siteToRoles [] r := by
  rintro ⟨⟨s, hs, _⟩, _⟩
  cases hs

/-- Extract roles that are effectively crashed given a site-to-role mapping
    (classical: crash status quantifies over all sites). -/
noncomputable def crashedRolesOfSites (siteToRoles : IdentityModel.SiteId ι → List Role)
    (allRoles : List Role) (crashedSites : List (IdentityModel.SiteId ι)) : List Role :=
  allRoles.filter (fun r => decide (RoleCrashedBySites siteToRoles crashedSites r))

private def mkEdge (roles : RoleSet) (src dst : Role) : Option (Role × Role) :=
  if hSrc : src ∈ roles then
    if hDst : dst ∈ roles then some (src, dst) else none
  else none

private theorem mk_edge_eq_some {roles : RoleSet} {src dst : Role} {e : Role × Role}
    (h : mkEdge roles src dst = some e) : src ∈ roles ∧ dst ∈ roles ∧ (src, dst) = e := by
  by_cases hSrc : src ∈ roles
  · by_cases hDst : dst ∈ roles
    · simpa [mkEdge, hSrc, hDst] using h
    · simp [mkEdge, hSrc, hDst] at h
  · simp [mkEdge, hSrc] at h

/-! ## Session Graph Extraction -/

/-- Extract the communication graph from a session in ProtocolMachineState.
    Uses the session's roles and builds edges from local type structure. -/
def commGraphOfSession (roles : RoleSet) (localTypes : List (Endpoint × LocalType)) : CommGraph where
  participants := roles
  -- Build edges from sender/receiver pairs found in local types
  edges := localTypes.filterMap (fun (ep, lt) =>
    match lt with
    | .send r _ _ => mkEdge roles ep.role r
    | .recv r _ _ => mkEdge roles r ep.role
    | .select r _ => mkEdge roles ep.role r
    | .branch r _ => mkEdge roles r ep.role
    | _ => none)
  edges_in_participants := by
    intro e hmem
    simp only [List.mem_filterMap] at hmem
    obtain ⟨⟨ep, lt⟩, _hLocal, he⟩ := hmem
    cases lt with
    | send r T L =>
        rcases mk_edge_eq_some he with ⟨hSrc, hDst, hEq⟩
        cases hEq
        exact ⟨hSrc, hDst⟩
    | recv r T L =>
        rcases mk_edge_eq_some he with ⟨hSrc, hDst, hEq⟩
        cases hEq
        exact ⟨hSrc, hDst⟩
    | select r bs =>
        rcases mk_edge_eq_some he with ⟨hSrc, hDst, hEq⟩
        cases hEq
        exact ⟨hSrc, hDst⟩
    | branch r bs =>
        rcases mk_edge_eq_some he with ⟨hSrc, hDst, hEq⟩
        cases hEq
        exact ⟨hSrc, hDst⟩
    | end_ => cases he
    | var n => cases he
    | mu L => cases he

/-- Graph-relevant shape of a session: its roles and endpoint types. -/
def sessionShapes (st : ProtocolMachineState ι γ π ε ν) :
    List (RoleSet × List (Endpoint × LocalType)) :=
  st.sessions.map fun p => (p.2.roles, p.2.localTypes)

/-- Aggregate communication graph of a list of session shapes. -/
def commGraphOfShapes (shapes : List (RoleSet × List (Endpoint × LocalType))) : CommGraph where
  participants := shapes.flatMap Prod.fst
  edges := shapes.flatMap fun x => (commGraphOfSession x.1 x.2).edges
  edges_in_participants := by
    intro e hmem
    rcases List.mem_flatMap.mp hmem with ⟨x, hx, he⟩
    have hIn := (commGraphOfSession x.1 x.2).edges_in_participants e he
    exact ⟨List.mem_flatMap.mpr ⟨x, hx, hIn.1⟩, List.mem_flatMap.mpr ⟨x, hx, hIn.2⟩⟩

/-- Extract communication graph from ProtocolMachineState by aggregating all session graphs. -/
def commGraphOfVMState (st : ProtocolMachineState ι γ π ε ν) : CommGraph :=
  commGraphOfShapes (sessionShapes st)

/-! ## protocol machine-Level Crash Tolerance Predicate -/

/-- protocol machine-level crash tolerance: a ProtocolMachineState tolerates a set of crashed sites
    if the residual communication graph remains connected. -/
def ProtocolMachineCrashTolerant (siteToRoles : IdentityModel.SiteId ι → List Role)
    (st : ProtocolMachineState ι γ π ε ν) : Prop :=
  let roles := (commGraphOfVMState st).participants
  let crashedRoles := crashedRolesOfSites siteToRoles roles st.crashedSites
  CrashTolerant (commGraphOfVMState st) crashedRoles

/-! ## Graph and Crash-Set Invariance Lemmas -/

/-- After a site crash, the crashed sites list grows. -/
theorem crash_site_extends_crashed (st : ProtocolMachineState ι γ π ε ν) (site : IdentityModel.SiteId ι) :
    (crashSite st site).crashedSites = st.crashedSites ∨
    (crashSite st site).crashedSites = site :: st.crashedSites := by
  unfold crashSite
  simp only
  split_ifs with h
  · left; rfl
  · right; rfl

/-- The communication graph is preserved by site crashes
    (crashes don't change session structure, only mark sites as failed). -/
theorem comm_graph_preserved_by_crash_site (st : ProtocolMachineState ι γ π ε ν) (site : IdentityModel.SiteId ι) :
    commGraphOfVMState (crashSite st site) = commGraphOfVMState st := by
  unfold commGraphOfVMState crashSite
  simp only
  split_ifs <;> rfl

/-- Disconnecting edges does not change the communication graph. -/
theorem comm_graph_preserved_by_disconnect_edges (st : ProtocolMachineState ι γ π ε ν) (edges : List Edge) :
    commGraphOfVMState (disconnectEdges st edges) = commGraphOfVMState st :=
  rfl

/-- Reconnecting edges does not change the communication graph. -/
theorem comm_graph_preserved_by_reconnect_edges (st : ProtocolMachineState ι γ π ε ν) (edges : List Edge) :
    commGraphOfVMState (reconnectEdges st edges) = commGraphOfVMState st :=
  rfl

/-- Closing a session changes only phase/buffers/traces, never session shapes. -/
theorem close_store_shapes (st : ProtocolMachineState ι γ π ε ν) (sid : SessionId) :
    ∀ ss : SessionStore ν,
      sessionShapes (closeSession { st with sessions := ss } sid) =
        sessionShapes { st with sessions := ss } := by
  intro ss
  induction ss with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨sid', s⟩ := p
      unfold sessionShapes closeSession at ih ⊢
      simp only [closeSession.closeStore] at ih ⊢
      split_ifs
      · simp
      · simp only [List.map_cons, ih]

/-- Closing a session does not change the communication graph. -/
theorem comm_graph_preserved_by_close_session (st : ProtocolMachineState ι γ π ε ν)
    (sid : SessionId) : commGraphOfVMState (closeSession st sid) = commGraphOfVMState st := by
  have h : sessionShapes (closeSession st sid) = sessionShapes st :=
    close_store_shapes st sid st.sessions
  unfold commGraphOfVMState
  rw [h]

/-! ## Tolerance Transport and Preservation -/

/-- Crash tolerance is preserved when graph and crash set are unchanged. -/
theorem protocol_machine_crash_tolerant_of_same_graph
    (siteToRoles : IdentityModel.SiteId ι → List Role)
    (st st' : ProtocolMachineState ι γ π ε ν)
    (hGraph : commGraphOfVMState st' = commGraphOfVMState st)
    (hCrashed : st'.crashedSites = st.crashedSites)
    (hTol : ProtocolMachineCrashTolerant siteToRoles st) :
    ProtocolMachineCrashTolerant siteToRoles st' := by
  unfold ProtocolMachineCrashTolerant at hTol ⊢
  simp [hGraph, hCrashed] at hTol ⊢
  exact hTol

/-- If a crash doesn't add any newly crashed roles, tolerance is preserved. -/
theorem crash_tolerant_preserved_of_no_new_role_crash
    (siteToRoles : IdentityModel.SiteId ι → List Role)
    (st : ProtocolMachineState ι γ π ε ν) (site : IdentityModel.SiteId ι)
    (hEqCrashed :
      crashedRolesOfSites siteToRoles (commGraphOfVMState st).participants (crashSite st site).crashedSites =
      crashedRolesOfSites siteToRoles (commGraphOfVMState st).participants st.crashedSites)
    (hTol : ProtocolMachineCrashTolerant siteToRoles st) :
    ProtocolMachineCrashTolerant siteToRoles (crashSite st site) := by
  unfold ProtocolMachineCrashTolerant at hTol ⊢
  rw [comm_graph_preserved_by_crash_site]
  simpa [hEqCrashed] using hTol

/-- Paths in a larger-crashed residual graph lift to smaller-crashed residual graphs. -/
theorem comm_path_lift_residual {G : CommGraph} {crashed₁ crashed₂ : List Role}
    (hEq : crashed₁ = crashed₂) {r₁ r₂ : Role}
    (hp : CommPath (residualGraph G crashed₁) r₁ r₂) :
    CommPath (residualGraph G crashed₂) r₁ r₂ := by
  simpa [hEq] using hp

/-- Crash tolerance preserved by a site crash when no new roles become fully crashed. -/
theorem crash_site_preserves_tolerance
    (siteToRoles : IdentityModel.SiteId ι → List Role)
    (st : ProtocolMachineState ι γ π ε ν) (site : IdentityModel.SiteId ι)
    (hEqCrashed :
      crashedRolesOfSites siteToRoles (commGraphOfVMState st).participants (crashSite st site).crashedSites =
      crashedRolesOfSites siteToRoles (commGraphOfVMState st).participants st.crashedSites)
    (hTol : ProtocolMachineCrashTolerant siteToRoles st) :
    ProtocolMachineCrashTolerant siteToRoles (crashSite st site) := by
  exact crash_tolerant_preserved_of_no_new_role_crash siteToRoles st site hEqCrashed hTol

/-! ## Topology-Preserving Operations -/

/-- Partition steps preserve crash tolerance (no change to crash set). -/
theorem disconnect_edges_preserves_tolerance
    (siteToRoles : IdentityModel.SiteId ι → List Role)
    (st : ProtocolMachineState ι γ π ε ν) (edges : List Edge)
    (hTol : ProtocolMachineCrashTolerant siteToRoles st) :
    ProtocolMachineCrashTolerant siteToRoles (disconnectEdges st edges) := by
  apply protocol_machine_crash_tolerant_of_same_graph siteToRoles _ _ ?_ rfl hTol
  exact comm_graph_preserved_by_disconnect_edges st edges

/-- Heal steps preserve crash tolerance (no change to crash set). -/
theorem reconnect_edges_preserves_tolerance
    (siteToRoles : IdentityModel.SiteId ι → List Role)
    (st : ProtocolMachineState ι γ π ε ν) (edges : List Edge)
    (hTol : ProtocolMachineCrashTolerant siteToRoles st) :
    ProtocolMachineCrashTolerant siteToRoles (reconnectEdges st edges) := by
  apply protocol_machine_crash_tolerant_of_same_graph siteToRoles _ _ ?_ rfl hTol
  exact comm_graph_preserved_by_reconnect_edges st edges

/-- Close-on-crash preserves crash tolerance (graph and crashed sites unchanged). -/
theorem close_session_preserves_tolerance
    (siteToRoles : IdentityModel.SiteId ι → List Role)
    (st : ProtocolMachineState ι γ π ε ν) (sid : SessionId)
    (hTol : ProtocolMachineCrashTolerant siteToRoles st) :
    ProtocolMachineCrashTolerant siteToRoles (closeSession st sid) :=
  protocol_machine_crash_tolerant_of_same_graph siteToRoles _ _
    (comm_graph_preserved_by_close_session st sid) rfl hTol

/-! ## Failure-Step Preservation -/

/-- Failure-aware steps preserve crash tolerance. Partition, heal and
    close-on-crash steps are proved unconditionally. Site crashes can genuinely
    disconnect the residual graph, so they require that no new role becomes
    fully crashed; scheduler steps can rewrite local types (hence edges), so they
    require that the step leaves the graph and the crashed sites unchanged. -/
theorem f_step_preserves_tolerance
    (siteToRoles : IdentityModel.SiteId ι → List Role)
    (st st' : ProtocolMachineState ι γ π ε ν) (hStep : FStep st st')
    (hNormal : ∀ st₁, schedStep st = some st₁ →
      commGraphOfVMState st₁ = commGraphOfVMState st ∧ st₁.crashedSites = st.crashedSites)
    (hCrash : ∀ site,
      crashedRolesOfSites siteToRoles (commGraphOfVMState st).participants
          (crashSite st site).crashedSites =
        crashedRolesOfSites siteToRoles (commGraphOfVMState st).participants st.crashedSites)
    (hTol : ProtocolMachineCrashTolerant siteToRoles st) :
    ProtocolMachineCrashTolerant siteToRoles st' := by
  cases hStep with
  | normal _ h =>
      obtain ⟨hG, hC⟩ := hNormal _ h
      exact protocol_machine_crash_tolerant_of_same_graph siteToRoles _ _ hG hC hTol
  | siteCrash site => exact crash_site_preserves_tolerance siteToRoles st site (hCrash site) hTol
  | partition es => exact disconnect_edges_preserves_tolerance siteToRoles st es hTol
  | heal es => exact reconnect_edges_preserves_tolerance siteToRoles st es hTol
  | closeOnCrash sid => exact close_session_preserves_tolerance siteToRoles st sid hTol

/-! ## Active Session Integration -/

/-- A session is active if it is present and not closed. -/
def SessionActive (st : ProtocolMachineState ι γ π ε ν) (sid : SessionId) : Prop :=
  ∃ sess, (sid, sess) ∈ st.sessions ∧ sess.phase ≠ .closed

/-- The executable failure-coherence check implies the session is active. -/
theorem failure_session_coherent_implies_active (st : ProtocolMachineState ι γ π ε ν)
    (sid : SessionId) (h : failureSessionCoherentB st sid = true) : SessionActive st sid := by
  unfold failureSessionCoherentB at h
  cases hs : sessionState? st.sessions sid with
  | none => rw [hs] at h; simp at h
  | some sess =>
      rw [hs] at h
      have hph : sess.phase ≠ .closed := by
        intro hc; simp [hc] at h
      unfold sessionState? at hs
      obtain ⟨⟨sid', sess'⟩, hp, hEq⟩ := Option.map_eq_some_iff.mp hs
      have hkey := List.find?_some hp
      simp only [decide_eq_true_eq] at hkey
      subst hkey
      cases hEq
      exact ⟨_, List.mem_of_find?_eq_some hp, hph⟩

/-- A session tolerates the current crashes if its own residual graph is connected. -/
def SessionCrashTolerant (siteToRoles : IdentityModel.SiteId ι → List Role)
    (st : ProtocolMachineState ι γ π ε ν) (sid : SessionId) : Prop :=
  ∀ sess, (sid, sess) ∈ st.sessions →
    CrashTolerant (commGraphOfSession sess.roles sess.localTypes)
      (crashedRolesOfSites siteToRoles sess.roles st.crashedSites)

/-- A protocol machine state is fully crash tolerant if every active session
    tolerates the current crashed sites on its own communication graph. -/
def ProtocolMachineFullyCrashTolerant (siteToRoles : IdentityModel.SiteId ι → List Role)
    (st : ProtocolMachineState ι γ π ε ν) : Prop :=
  ∀ sid, SessionActive st sid → SessionCrashTolerant siteToRoles st sid

/-- Partitions preserve full crash tolerance (sessions and crashed sites unchanged). -/
theorem disconnect_edges_preserves_full_tolerance
    (siteToRoles : IdentityModel.SiteId ι → List Role)
    (st : ProtocolMachineState ι γ π ε ν) (edges : List Edge)
    (h : ProtocolMachineFullyCrashTolerant siteToRoles st) :
    ProtocolMachineFullyCrashTolerant siteToRoles (disconnectEdges st edges) :=
  h

/-- Heals preserve full crash tolerance (sessions and crashed sites unchanged). -/
theorem reconnect_edges_preserves_full_tolerance
    (siteToRoles : IdentityModel.SiteId ι → List Role)
    (st : ProtocolMachineState ι γ π ε ν) (edges : List Edge)
    (h : ProtocolMachineFullyCrashTolerant siteToRoles st) :
    ProtocolMachineFullyCrashTolerant siteToRoles (reconnectEdges st edges) :=
  h

end ProtocolMachineConnection

end


/-! ## Summary

This module establishes crash tolerance for MPST:

1. **CommGraph**: Communication graph of a session
2. **residualGraph**: Graph after removing crashed participants
3. **CrashTolerant**: Crash set is tolerable iff residual connected
4. **Critical/NonCritical**: Participants whose crash matters
5. **MaxCrashSet**: Largest tolerable crash set
6. **crash_tolerance_iff**: Exact characterization theorem

The key insight is that crash tolerance is equivalent to graph connectivity
of the residual communication graph. This provides a computable criterion
for determining which participants can fail.

Also: `crashTolerantDec` is an executable reachability-closure check, proved
sound and complete (`crash_tolerant_dec_sound`/`_complete`).
-/
