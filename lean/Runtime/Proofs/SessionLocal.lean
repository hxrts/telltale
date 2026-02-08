import Runtime.Proofs.Delegation
import Protocol.Coherence.EdgeCoherence
import Protocol.Coherence.RoleSwap

/-!
# Session-Local State for Protocol Coherence

This module defines per-session slicing of Protocol state and proves that coherence
decomposes as a separating conjunction over sessions. This is the foundation for
the frame rule and cross-session diamond proofs at the VM level.

## Key Definitions

- `SessionCoherent s`: Coherence restricted to edges within session `s`
- `SessionFootprint`: The set of sessions a coroutine can affect (abstract)

## Key Theorems

- `VMCoherent_iff_forall_SessionCoherent`: Global coherence decomposes per-session
- `footprint_grows_on_delegation`: Receiving delegated endpoint adds to footprint
- `session_local_op_preserves_other`: Frame property for session-local operations

## Proof Strategy

The insight is that Coherence is defined per-edge, and edges are session-local.
Therefore:
1. Global coherence = conjunction of per-edge coherence
2. Per-edge coherence only involves one session
3. Hence global coherence = conjunction over sessions of per-session coherence

This decomposition enables the frame rule: an instruction that only affects
session `s` preserves `SessionCoherent s'` for all `s' ≠ s`.

## Connection to Paper 3

Delegation provides the mechanism for coroutines to dynamically participate in
multiple sessions. The `delegation_preserves_coherent` theorem (from Delegation.lean)
is used here to prove that receiving a delegated endpoint safely extends the
coroutine's footprint.

See `work/vm_instructions.md` for the full specification.

Note: This module is kept at the Protocol level (GEnv, DEnv, Coherent) to avoid
the Iris import collision. VM-level integration requires resolving the Store
name collision between Protocol.Environments.Core and Iris.Std.Heap.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Classical

noncomputable section

universe u

/-! ## Per-Session Coherence -/

/-- Coherence restricted to a single session.
    An edge belongs to session s iff edge.sid = s, and only active edges matter. -/
def SessionCoherent (G : GEnv) (D : DEnv) (s : SessionId) : Prop :=
  ∀ e : Edge, e.sid = s → ActiveEdge G e → EdgeCoherent G D e

/-- Global coherence implies per-session coherence. -/
theorem Coherent_implies_SessionCoherent {G : GEnv} {D : DEnv} {s : SessionId}
    (hCoh : Coherent G D) : SessionCoherent G D s := by
  intro e _ hActive
  exact hCoh e hActive

/-- Per-session coherence for all sessions implies global coherence. -/
theorem SessionCoherent_forall_implies_Coherent {G : GEnv} {D : DEnv}
    (h : ∀ s, SessionCoherent G D s) : Coherent G D := by
  intro e hActive
  exact h e.sid e rfl hActive

/-- **Global coherence decomposes as conjunction over sessions.**
    This is the key structural lemma enabling the frame rule. -/
theorem VMCoherent_iff_forall_SessionCoherent {G : GEnv} {D : DEnv} :
    Coherent G D ↔ ∀ s, SessionCoherent G D s := by
  constructor
  · intro hCoh s
    exact Coherent_implies_SessionCoherent hCoh
  · intro h
    exact SessionCoherent_forall_implies_Coherent h

/-! ## Abstract SessionFootprint

A footprint is the set of sessions an entity (coroutine, instruction) can affect.
This includes:
- A "native" session (the session it was created for)
- Any delegated sessions (endpoints received via higher-order messages)

With higher-order sessions (Paper 3), delegated endpoints carry their LocalType
to govern permitted operations.
-/

/-- An abstract footprint: native session plus delegated sessions with their types.
    The delegated list contains (SessionId, LocalType) pairs where the LocalType
    governs what operations are permitted on the delegated endpoint.

    Note: At the VM level, this will be computed from CoroutineState.ownedEndpoints.
    Here we define the abstract structure to enable Protocol-level reasoning. -/
structure SessionFootprint where
  /-- The primary session -/
  nativeSession : SessionId
  /-- Delegated sessions: (session, delegated local type) pairs.
      The local type governs what operations are permitted on the delegated endpoint. -/
  delegated : List (SessionId × LocalType)

/-- Compute the set of sessions in a footprint. -/
def SessionFootprint.sessions (fp : SessionFootprint) : List SessionId :=
  fp.nativeSession :: fp.delegated.map Prod.fst

/-- Check if a session is in a footprint. -/
def SessionFootprint.contains (fp : SessionFootprint) (s : SessionId) : Bool :=
  s = fp.nativeSession || fp.delegated.any (·.1 = s)

/-- A footprint as a set. -/
def SessionFootprint.toSet (fp : SessionFootprint) : Set SessionId :=
  {s | fp.contains s}

/-! ## SessionFootprint Dynamics -/

/-- Receiving a delegated endpoint extends the footprint.
    When a coroutine receives a message containing `chan s L` (a delegated endpoint),
    session `s` is added to its footprint with delegated type `L`. -/
def footprint_extend (fp : SessionFootprint) (s : SessionId) (L : LocalType) :
    SessionFootprint :=
  { fp with delegated := (s, L) :: fp.delegated }

/-- SessionFootprint grows when receiving delegation. -/
theorem footprint_extend_contains (fp : SessionFootprint) (s : SessionId) (L : LocalType) :
    (footprint_extend fp s L).contains s := by
  simp [footprint_extend, SessionFootprint.contains]

/-- Completing a delegated protocol shrinks the footprint.
    When a delegated endpoint's type reaches `end`, the delegation is consumed
    and the session is removed from the footprint. -/
def footprint_remove (fp : SessionFootprint) (s : SessionId) : SessionFootprint :=
  { fp with delegated := fp.delegated.filter (·.1 ≠ s) }

/-- Native session always remains in footprint. -/
theorem footprint_remove_preserves_native (fp : SessionFootprint) (s : SessionId) :
    (footprint_remove fp s).nativeSession = fp.nativeSession := by
  simp [footprint_remove]

/-- Removing delegated session `s` clears `s` from delegated containment
    whenever `s` is not the native session. -/
theorem footprint_remove_clears_delegated
    (fp : SessionFootprint) (s : SessionId)
    (hNative : fp.nativeSession ≠ s) :
    (footprint_remove fp s).contains s = false := by
  have hNative' : s ≠ fp.nativeSession := by
    intro hEq
    exact hNative hEq.symm
  simp [footprint_remove, SessionFootprint.contains, hNative']

/-- Completing a delegated protocol shrinks the footprint:
    native ownership is preserved and delegated session `s` is removed. -/
theorem footprint_shrinks_on_delegation_completion
    (fp : SessionFootprint) (s : SessionId)
    (hNative : fp.nativeSession ≠ s) :
    let fp' := footprint_remove fp s
    fp'.nativeSession = fp.nativeSession ∧ fp'.contains s = false := by
  constructor
  · exact footprint_remove_preserves_native fp s
  · exact footprint_remove_clears_delegated fp s hNative

/-! ## Session Disjointness -/

/-- Two sessions are disjoint if they share no edges.
    Since edges are identified by session ID, this is trivially true for s ≠ s'. -/
def SessionsDisjoint (s s' : SessionId) : Prop := s ≠ s'

/-- Disjoint sessions have no edge overlap. -/
theorem disjoint_sessions_no_edge_overlap {s s' : SessionId} (h : SessionsDisjoint s s') :
    ∀ e : Edge, e.sid = s → e.sid ≠ s' := by
  intro e hEs
  rw [hEs]
  exact h

/-! ## SessionFootprint Disjointness -/

/-- Two footprints are disjoint if they share no sessions. -/
def SessionFootprintsDisjoint (fp₁ fp₂ : SessionFootprint) : Prop :=
  ∀ s, ¬(fp₁.contains s ∧ fp₂.contains s)

/-- Disjoint footprints imply operations on different sessions. -/
theorem disjoint_footprints_different_sessions {fp₁ fp₂ : SessionFootprint}
    (h : SessionFootprintsDisjoint fp₁ fp₂)
    {s₁ s₂ : SessionId} (h₁ : fp₁.contains s₁) (h₂ : fp₂.contains s₂) :
    s₁ ≠ s₂ := by
  intro hEq
  subst hEq
  exact h s₁ ⟨h₁, h₂⟩

/-! ## Delegation Preservation -/

/-- Receiving a delegated endpoint preserves session coherence for other sessions.

    This is the key lemma connecting Protocol-level delegation preservation to
    VM-level reasoning. It uses the `delegation_preserves_coherent` theorem.

    **Intuition:** Delegation is message passing where the payload includes a channel.
    The sender's type changes (endpoint sent away), the receiver's type changes
    (endpoint received), but only edges involving the sender/receiver change.
    Edges in other sessions are unaffected. -/
theorem delegation_recv_preserves_other_sessions
    {G G' : GEnv} {D D' : DEnv} {s sOther : SessionId} {A B : Role}
    (hCoh : Coherent G D)
    (hDeleg : DelegationStep G G' D D' s A B)
    (_hDiff : sOther ≠ s) :
    SessionCoherent G' D' sOther := by
  -- Use the theorem to get global coherence after delegation
  have hCoh' : Coherent G' D' := delegation_preserves_coherent G G' D D' s A B hCoh hDeleg
  -- Extract per-session coherence
  exact Coherent_implies_SessionCoherent hCoh'

/-- Blindness for delegation at the session boundary:
    endpoints in sessions other than the delegated one are unchanged. -/
theorem delegation_blind_endpoint_lookup
    {G G' : GEnv} {D D' : DEnv} {s sOther : SessionId} {A B : Role}
    (hDeleg : DelegationStep G G' D D' s A B)
    (hDiff : sOther ≠ s)
    (ep : Endpoint) (hSid : ep.sid = sOther) :
    lookupG G' ep = lookupG G ep := by
  have hSidNe : ep.sid ≠ s := by
    intro hEq
    apply hDiff
    calc
      sOther = ep.sid := hSid.symm
      _ = s := hEq
  exact hDeleg.other_sessions_G ep hSidNe

/-- Blindness for delegation at the session boundary:
    traces in sessions other than the delegated one are unchanged. -/
theorem delegation_blind_trace_lookup
    {G G' : GEnv} {D D' : DEnv} {s sOther : SessionId} {A B : Role}
    (hDeleg : DelegationStep G G' D D' s A B)
    (hDiff : sOther ≠ s)
    (e : Edge) (hSid : e.sid = sOther) :
    lookupD D' e = lookupD D e := by
  have hSidNe : e.sid ≠ s := by
    intro hEq
    apply hDiff
    calc
      sOther = e.sid := hSid.symm
      _ = s := hEq
  exact hDeleg.other_sessions_D e hSidNe

/-- For non-delegated sessions, active-edge membership is unchanged by delegation. -/
theorem delegation_blind_activeEdge_iff
    {G G' : GEnv} {D D' : DEnv} {s sOther : SessionId} {A B : Role}
    (hDeleg : DelegationStep G G' D D' s A B)
    (hDiff : sOther ≠ s)
    (e : Edge) (hSid : e.sid = sOther) :
    ActiveEdge G' e ↔ ActiveEdge G e := by
  constructor
  · intro hActive
    constructor
    · have hLookup :=
        delegation_blind_endpoint_lookup (hDeleg:=hDeleg) (hDiff:=hDiff)
          (ep:=⟨e.sid, e.sender⟩) hSid
      simpa [hLookup] using hActive.1
    · have hLookup :=
        delegation_blind_endpoint_lookup (hDeleg:=hDeleg) (hDiff:=hDiff)
          (ep:=⟨e.sid, e.receiver⟩) hSid
      simpa [hLookup] using hActive.2
  · intro hActive
    constructor
    · have hLookup :=
        delegation_blind_endpoint_lookup (hDeleg:=hDeleg) (hDiff:=hDiff)
          (ep:=⟨e.sid, e.sender⟩) hSid
      simpa [hLookup] using hActive.1
    · have hLookup :=
        delegation_blind_endpoint_lookup (hDeleg:=hDeleg) (hDiff:=hDiff)
          (ep:=⟨e.sid, e.receiver⟩) hSid
      simpa [hLookup] using hActive.2

/-- Harmony split for delegation:
    delegated session remains coherent and all other sessions are preserved. -/
theorem delegation_harmony_split
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role}
    (hCoh : Coherent G D)
    (hDeleg : DelegationStep G G' D D' s A B) :
    SessionCoherent G' D' s ∧
    (∀ sOther, sOther ≠ s → SessionCoherent G' D' sOther) := by
  constructor
  · exact Coherent_implies_SessionCoherent
      (delegation_preserves_coherent G G' D D' s A B hCoh hDeleg)
  · intro sOther hDiff
    exact delegation_recv_preserves_other_sessions
      (hCoh:=hCoh) (hDeleg:=hDeleg) (sOther:=sOther) hDiff

/-- Role exchangeability after delegation:
    once delegation is applied, any finite session-local role-swap sequence preserves coherence. -/
theorem delegation_preserves_exchangeability
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role}
    (pairs : List (Role × Role))
    (hCoh : Coherent G D)
    (hDeleg : DelegationStep G G' D D' s A B) :
    Coherent (swapGEnvRoleList s pairs G') (swapDEnvRoleList s pairs D') := by
  exact Coherent_exchangeable (s:=s) (pairs:=pairs) (G:=G') (D:=D')
    (delegation_preserves_coherent G G' D D' s A B hCoh hDeleg)

/-- Receiving a delegated endpoint preserves coherence and extends footprint safely.

    When coroutine C receives message containing `chan s L`:
    1. C's footprint grows to include s
    2. Coherence is preserved (by delegation_preserves_coherent)
    3. C can now perform operations on session s per type L -/
theorem footprint_grows_on_delegation
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role}
    {fp : SessionFootprint} {L : LocalType}
    (hCoh : Coherent G D)
    (hDeleg : DelegationStep G G' D D' s A B)
    (_hNotIn : ¬fp.contains s) :
    let fp' := footprint_extend fp s L
    Coherent G' D' ∧ fp'.contains s := by
  constructor
  · exact delegation_preserves_coherent G G' D D' s A B hCoh hDeleg
  · exact footprint_extend_contains fp s L

/-! ## Frame Property Setup -/

/-- An operation is session-local if it only affects one session.
    This means: for any session s' ≠ s, the operation preserves all
    endpoint lookups and trace lookups for edges in s'. -/
def SessionLocalOp (s : SessionId) (f : GEnv × DEnv → GEnv × DEnv) : Prop :=
  ∀ G D s', s' ≠ s →
    let (G', D') := f (G, D)
    (∀ ep : Endpoint, ep.sid = s' → lookupG G' ep = lookupG G ep) ∧
    (∀ e : Edge, e.sid = s' → lookupD D' e = lookupD D e)

/-- Session-local operations preserve coherence for other sessions.
    This is the core frame property: if an operation only touches session s,
    then SessionCoherent s' is preserved for all s' ≠ s. -/
theorem session_local_op_preserves_other {s : SessionId}
    {f : GEnv × DEnv → GEnv × DEnv}
    (hLocal : SessionLocalOp s f)
    {G : GEnv} {D : DEnv} (sOther : SessionId) (hDiff : sOther ≠ s)
    (hCoh : SessionCoherent G D sOther) :
    let (G', D') := f (G, D)
    SessionCoherent G' D' sOther := by
  obtain ⟨hEp, hTrace⟩ := hLocal G D sOther hDiff
  intro e hSid hActive
  simp only [EdgeCoherent]
  intro Lrecv hGrecv
  -- The receiver endpoint lookup is unchanged
  have hRecvEp : Endpoint.mk e.sid e.receiver = ⟨e.sid, e.receiver⟩ := rfl
  have hRecvSid : (⟨e.sid, e.receiver⟩ : Endpoint).sid = sOther := hSid
  have hGrecvOrig : lookupG G ⟨e.sid, e.receiver⟩ = some Lrecv := by
    rw [← hEp ⟨e.sid, e.receiver⟩ hRecvSid]
    exact hGrecv
  -- Sender endpoint lookup is unchanged (ActiveEdge gives us sender existence in G').
  have hSenderSome : (lookupG (f (G, D)).1 ⟨e.sid, e.sender⟩).isSome := hActive.1
  rcases (Option.isSome_iff_exists).1 hSenderSome with ⟨Lsender0, hGsenderNew0⟩
  have hSendSid : (⟨e.sid, e.sender⟩ : Endpoint).sid = sOther := hSid
  have hGsenderOrig0 : lookupG G ⟨e.sid, e.sender⟩ = some Lsender0 := by
    simpa [hEp ⟨e.sid, e.sender⟩ hSendSid] using hGsenderNew0
  have hActiveOrig : ActiveEdge G e :=
    ActiveEdge_of_endpoints (G:=G) (e:=e) hGsenderOrig0 hGrecvOrig
  -- Get coherence from original state
  have hEdgeCoh := hCoh e hSid hActiveOrig
  rcases hEdgeCoh Lrecv hGrecvOrig with ⟨Lsender, hGsender, hConsume⟩
  -- The sender endpoint lookup is unchanged
  have hSendSid : (⟨e.sid, e.sender⟩ : Endpoint).sid = sOther := hSid
  have hGsenderNew : lookupG (f (G, D)).1 ⟨e.sid, e.sender⟩ = some Lsender := by
    rw [hEp ⟨e.sid, e.sender⟩ hSendSid]
    exact hGsender
  -- The trace is unchanged
  have hTraceUnch : lookupD (f (G, D)).2 e = lookupD D e := hTrace e hSid
  -- Reconstruct coherence
  refine ⟨Lsender, hGsenderNew, ?_⟩
  rw [hTraceUnch]
  exact hConsume

/-! ## Role Swap as Session-Local Operation -/

/-- Swap roles A and B within a session as a G/D operation. -/
def swapRolesOp (s : SessionId) (A B : Role) : GEnv × DEnv → GEnv × DEnv
  | (G, D) => (swapGEnvRole s A B G, swapDEnvRole s A B D)

/-- Role swap is session-local: other sessions are unaffected. -/
theorem swapRoles_session_local (s : SessionId) (A B : Role) :
    SessionLocalOp s (swapRolesOp s A B) := by
  intro G D s' hDiff
  constructor
  · intro ep hSid
    have hSidNe : ep.sid ≠ s := by
      intro hEq
      apply hDiff
      calc
        s' = ep.sid := by symm; exact hSid
        _ = s := hEq
    have hLookup := lookupG_swap (s:=s) (A:=A) (B:=B) (G:=G) (e:=ep)
    -- swapEndpointRole is identity when ep.sid ≠ s
    have hSwap : swapEndpointRole s A B ep = ep := by
      simp [swapEndpointRole, hSidNe]
    -- Reduce to unchanged lookup
    simpa [swapRolesOp, hSwap, hSidNe] using hLookup
  · intro e hSid
    have hSidNe : e.sid ≠ s := by
      intro hEq
      apply hDiff
      calc
        s' = e.sid := by symm; exact hSid
        _ = s := hEq
    have hLookup := lookupD_swap (s:=s) (A:=A) (B:=B) (D:=D) (e:=e)
    have hSwap : swapEdgeRole s A B e = e := by
      simp [swapEdgeRole, hSidNe]
    simpa [swapRolesOp, hSwap, hSidNe] using hLookup

/-- Role swap preserves global coherence. -/
theorem swapRoles_preserves_coherent {G : GEnv} {D : DEnv}
    (s : SessionId) (A B : Role) (hCoh : Coherent G D) :
    Coherent (swapGEnvRole s A B G) (swapDEnvRole s A B D) := by
  exact CoherentRoleSwap (s:=s) (A:=A) (B:=B) (G:=G) (D:=D) hCoh

/-- Role swap preserves coherence for sessions other than s. -/
theorem swapRoles_preserves_other_sessions {G : GEnv} {D : DEnv}
    (s sOther : SessionId) (A B : Role)
    (hDiff : sOther ≠ s)
    (hCoh : SessionCoherent G D sOther) :
    let (G', D') := swapRolesOp s A B (G, D)
    SessionCoherent G' D' sOther := by
  exact session_local_op_preserves_other (s:=s) (f:=swapRolesOp s A B)
    (hLocal:=swapRoles_session_local (s:=s) (A:=A) (B:=B)) sOther hDiff hCoh

/-! ## VM Integration Notes

The VM-level instruction footprint and cross-session diamond proofs are in
`Runtime/Proofs/Frame.lean`. They require resolving the Store name collision
between Protocol.Environments.Core and Iris.Std.Heap before they can be
connected to this module.

The key definitions that need VM types:
- `instrSessionFootprint : Instr → CoroutineState → Set SessionId`
- `DisjointInstrSessionFootprints : Instr → Instr → CoroutineState → CoroutineState → Prop`
- `cross_session_diamond_from_frame`

These are temporarily defined in Frame.lean with stubs until the import collision
is resolved.
-/

end
