import Runtime.Proofs.DelegationAxiom
import Protocol.Coherence.EdgeCoherence

/-!
# Session-Local State for Protocol Coherence

This module defines per-session slicing of Protocol state and proves that coherence
decomposes as a separating conjunction over sessions. This is the foundation for
the frame rule and cross-session diamond proofs at the VM level.

## Key Definitions

- `SessionCoherent s`: Coherence restricted to edges within session `s`
- `Footprint`: The set of sessions a coroutine can affect (abstract)

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
multiple sessions. The `delegation_preserves_coherent` axiom (from DelegationAxiom.lean)
is used here to prove that receiving a delegated endpoint safely extends the
coroutine's footprint.

See `work/vm_session.md` for the full design document.

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
    An edge belongs to session s iff edge.sid = s. -/
def SessionCoherent (G : GEnv) (D : DEnv) (s : SessionId) : Prop :=
  ∀ e : Edge, e.sid = s → EdgeCoherent G D e

/-- Global coherence implies per-session coherence. -/
theorem Coherent_implies_SessionCoherent {G : GEnv} {D : DEnv} {s : SessionId}
    (hCoh : Coherent G D) : SessionCoherent G D s := by
  intro e _
  exact hCoh e

/-- Per-session coherence for all sessions implies global coherence. -/
theorem SessionCoherent_forall_implies_Coherent {G : GEnv} {D : DEnv}
    (h : ∀ s, SessionCoherent G D s) : Coherent G D := by
  intro e
  exact h e.sid e rfl

/-- **Global coherence decomposes as conjunction over sessions.**
    This is the key structural lemma enabling the frame rule. -/
theorem VMCoherent_iff_forall_SessionCoherent {G : GEnv} {D : DEnv} :
    Coherent G D ↔ ∀ s, SessionCoherent G D s := by
  constructor
  · intro hCoh s
    exact Coherent_implies_SessionCoherent hCoh
  · intro h
    exact SessionCoherent_forall_implies_Coherent h

/-! ## Abstract Footprint

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
structure Footprint where
  /-- The primary session -/
  nativeSession : SessionId
  /-- Delegated sessions: (session, delegated local type) pairs.
      The local type governs what operations are permitted on the delegated endpoint. -/
  delegated : List (SessionId × LocalType)

/-- Compute the set of sessions in a footprint. -/
def Footprint.sessions (fp : Footprint) : List SessionId :=
  fp.nativeSession :: fp.delegated.map Prod.fst

/-- Check if a session is in a footprint. -/
def Footprint.contains (fp : Footprint) (s : SessionId) : Bool :=
  s = fp.nativeSession || fp.delegated.any (·.1 = s)

/-- A footprint as a set. -/
def Footprint.toSet (fp : Footprint) : Set SessionId :=
  {s | fp.contains s}

/-! ## Footprint Dynamics -/

/-- Receiving a delegated endpoint extends the footprint.
    When a coroutine receives a message containing `chan s L` (a delegated endpoint),
    session `s` is added to its footprint with delegated type `L`. -/
def footprint_extend (fp : Footprint) (s : SessionId) (L : LocalType) :
    Footprint :=
  { fp with delegated := (s, L) :: fp.delegated }

/-- Footprint grows when receiving delegation. -/
theorem footprint_extend_contains (fp : Footprint) (s : SessionId) (L : LocalType) :
    (footprint_extend fp s L).contains s := by
  simp [footprint_extend, Footprint.contains]

/-- Completing a delegated protocol shrinks the footprint.
    When a delegated endpoint's type reaches `end`, the delegation is consumed
    and the session is removed from the footprint. -/
def footprint_remove (fp : Footprint) (s : SessionId) : Footprint :=
  { fp with delegated := fp.delegated.filter (·.1 ≠ s) }

/-- Native session always remains in footprint. -/
theorem footprint_remove_preserves_native (fp : Footprint) (s : SessionId) :
    (footprint_remove fp s).nativeSession = fp.nativeSession := by
  simp [footprint_remove]

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

/-! ## Footprint Disjointness -/

/-- Two footprints are disjoint if they share no sessions. -/
def FootprintsDisjoint (fp₁ fp₂ : Footprint) : Prop :=
  ∀ s, ¬(fp₁.contains s ∧ fp₂.contains s)

/-- Disjoint footprints imply operations on different sessions. -/
theorem disjoint_footprints_different_sessions {fp₁ fp₂ : Footprint}
    (h : FootprintsDisjoint fp₁ fp₂)
    {s₁ s₂ : SessionId} (h₁ : fp₁.contains s₁) (h₂ : fp₂.contains s₂) :
    s₁ ≠ s₂ := by
  intro hEq
  subst hEq
  exact h s₁ ⟨h₁, h₂⟩

/-! ## Delegation Preservation (Uses Axiom) -/

/-- Receiving a delegated endpoint preserves session coherence for other sessions.

    This is the key lemma connecting Protocol-level delegation preservation to
    VM-level reasoning. It uses the `delegation_preserves_coherent` axiom.

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
  -- Use the axiom to get global coherence after delegation
  have hCoh' : Coherent G' D' := delegation_preserves_coherent G G' D D' s A B hCoh hDeleg
  -- Extract per-session coherence
  exact Coherent_implies_SessionCoherent hCoh'

/-- Receiving a delegated endpoint preserves coherence and extends footprint safely.

    When coroutine C receives message containing `chan s L`:
    1. C's footprint grows to include s
    2. Coherence is preserved (by delegation_preserves_coherent axiom)
    3. C can now perform operations on session s per type L -/
theorem footprint_grows_on_delegation
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role}
    {fp : Footprint} {L : LocalType}
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
  intro e hSid
  simp only [EdgeCoherent]
  intro Lrecv hGrecv
  -- The receiver endpoint lookup is unchanged
  have hRecvEp : Endpoint.mk e.sid e.receiver = ⟨e.sid, e.receiver⟩ := rfl
  have hRecvSid : (⟨e.sid, e.receiver⟩ : Endpoint).sid = sOther := hSid
  have hGrecvOrig : lookupG G ⟨e.sid, e.receiver⟩ = some Lrecv := by
    rw [← hEp ⟨e.sid, e.receiver⟩ hRecvSid]
    exact hGrecv
  -- Get coherence from original state
  have hEdgeCoh := hCoh e hSid
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

/-! ## VM Integration Notes

The VM-level instruction footprint and cross-session diamond proofs are in
`Runtime/Proofs/Frame.lean`. They require resolving the Store name collision
between Protocol.Environments.Core and Iris.Std.Heap before they can be
connected to this module.

The key definitions that need VM types:
- `instrFootprint : Instr → CoroutineState → Set SessionId`
- `DisjointInstrFootprints : Instr → Instr → CoroutineState → CoroutineState → Prop`
- `cross_session_diamond_from_frame`

These are temporarily defined in Frame.lean with stubs until the import collision
is resolved.
-/

end
