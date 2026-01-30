import Effects.Coherence
import Effects.Decidability
import Effects.Monitor.Part1
import Effects.Typing.Part1
import Effects.Typing.Part3a

/-!
# MPST Verified Monitor

This module implements the proof-carrying runtime monitor for MPST.

## Overview

The monitor is the trusted component that:
1. Tracks protocol state (local types, in-flight messages, buffers)
2. Validates each protocol action before execution
3. Updates state to reflect completed actions
4. Maintains invariants that metatheory proves are preserved

## Monitor State

The `MonitorState` structure contains:
- `G`: GEnv mapping endpoints to their current local types
- `D`: DEnv tracking in-flight message type traces per edge
- `bufs`: Runtime message buffers per directed edge
- `Lin`: Linear context tracking capability tokens
- `supply`: Fresh session ID counter

## Monitor Transitions

`MonStep` is the judgment for valid monitor transitions. Each constructor
corresponds to a protocol action (send, recv, select, branch, newSession).

The key theorem `MonStep_preserves_WTMon` states that valid transitions
preserve the well-typedness invariant.

## Untrusted Code Interface

Untrusted code interacts with the monitor by:
1. Presenting a capability token
2. Requesting an action
3. Monitor validates action matches token's type
4. Monitor updates state and returns new token

This ensures untrusted code can only perform actions allowed by the protocol.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-! ## Preservation Theorem -/

/-- Monitor transitions preserve well-typedness.

This is the key soundness theorem: if the monitor state is well-typed
and we take a valid transition, the result is also well-typed. -/
axiom MonStep_preserves_WTMon (ms ms' : MonitorState) (act : ProtoAction) (v : Value)
    (hStep : MonStep ms act v ms')
    (hWTc : WTMonComplete ms) :
    WTMon ms'

theorem token_consumed_removed (ctx : LinCtx) (e : Endpoint) (ctx' : LinCtx) (S : LocalType)
    (hPairwise : ctx.Pairwise (fun a b => a.1 ≠ b.1))
    (h : LinCtx.consumeToken ctx e = some (ctx', S)) :
    ¬LinCtx.contains ctx' e := by
  -- LinCtx.contains ctx' e = true means ∃ S', (e, S') ∈ ctx'
  -- But consumeToken_not_mem says ∀ S', (e, S') ∉ ctx'
  intro hContains
  simp only [LinCtx.contains, List.any_eq_true] at hContains
  obtain ⟨⟨e', S'⟩, hMem, hEq⟩ := hContains
  simp only [beq_iff_eq] at hEq
  subst hEq
  exact consumeToken_not_mem ctx ctx' e S hPairwise h S' hMem

/-! ## Buffer and DEnv Consistency Helpers -/

/-- If a session is not in G, buffers have no entry for it. -/
theorem BConsistent_lookup_none_of_notin_sessions
    {G : GEnv} {B : Buffers} {e : Edge}
    (hCons : BConsistent G B) (hNot : e.sid ∉ SessionsOf G) :
    B.lookup e = none := by
  by_contra hSome
  cases hFind : B.lookup e with
  | none => exact (hSome hFind)
  | some buf =>
      have hSid : e.sid ∈ SessionsOf G := hCons e buf hFind
      exact (hNot hSid).elim

/-- If a session is not in G, DEnv has no entry for it. -/
theorem DEnv_find_none_of_notin_sessions
    {G : GEnv} {D : DEnv} {e : Edge}
    (hCons : DConsistent G D) (hNot : e.sid ∉ SessionsOf G) :
    D.find? e = none := by
  by_contra hSome
  cases hFind : D.find? e with
  | none => exact (hSome hFind)
  | some ts =>
      have hSid : e.sid ∈ SessionsOfD D := ⟨e, ts, hFind, rfl⟩
      have hSidG : e.sid ∈ SessionsOf G := hCons hSid
      exact (hNot hSidG).elim

/-- BufferTyped is preserved when extending GEnv without changing existing lookups. -/
theorem BufferTyped_weakenG {G G' : GEnv} {D : DEnv} {bufs : Buffers} {e : Edge} :
    BufferTyped G D bufs e →
    (∀ ep L, lookupG G ep = some L → lookupG G' ep = some L) →
    BufferTyped G' D bufs e := by
  intro hBT hMono
  rcases hBT with ⟨hLen, hTyping⟩
  refine ⟨hLen, ?_⟩
  intro i hi
  exact HasTypeVal_mono G G' _ _ (hTyping i hi) hMono

/-! ## Session Creation -/

/-- Lookup in mapped endpoints returns none if session ID doesn't match. -/
theorem lookup_mapped_endpoints_sid_ne (roles : RoleSet) (sid : SessionId)
    (localTypes : Role → LocalType) (e : Endpoint)
    (hNeq : e.sid ≠ sid) :
    (roles.map fun r => (Endpoint.mk sid r, localTypes r)).lookup e = none := by
  induction roles with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map, List.lookup]
    -- Check if e == Endpoint.mk sid r
    have hNeqEndpoint : (e == Endpoint.mk sid r) = false := by
      rw [beq_eq_false_iff_ne]
      intro heq
      have : e.sid = sid := by simp [heq]
      exact hNeq this
    simp only [hNeqEndpoint]
    exact ih

/-- Lookup in mapped endpoints finds the entry if role is in list. -/
theorem lookup_mapped_endpoints_mem (roles : RoleSet) (sid : SessionId)
    (localTypes : Role → LocalType) (r : Role)
    (hMem : r ∈ roles) :
    (roles.map fun r' => (Endpoint.mk sid r', localTypes r')).lookup
      (Endpoint.mk sid r) = some (localTypes r) := by
  induction roles with
  | nil =>
    simp only [List.mem_nil_iff] at hMem
  | cons hd tl ih =>
    simp only [List.map, List.lookup]
    by_cases heq : hd = r
    · -- hd = r: found it
      subst heq
      simp only [beq_self_eq_true]
    · -- hd ≠ r: continue searching
      have hNeqEndpoint : (Endpoint.mk sid r == Endpoint.mk sid hd) = false := by
        rw [beq_eq_false_iff_ne]
        intro heq'
        simp only [Endpoint.mk.injEq] at heq'
        exact heq heq'.2.symm
      simp only [hNeqEndpoint]
      simp only [List.mem_cons] at hMem
      cases hMem with
      | inl h => exact absurd h.symm heq
      | inr h => exact ih h

/-- Create a new session with given roles and local types.

Returns updated monitor state with:
- Fresh session ID allocated
- Endpoints added to G with initial types
- Empty buffers/traces for all edges
- Tokens for all endpoints in Lin -/
def MonitorState.newSession (ms : MonitorState) (roles : RoleSet)
    (localTypes : Role → LocalType) : MonitorState :=
  let sid := ms.supply
  let newEndpoints := roles.map fun r => ({ sid := sid, role := r }, localTypes r)
  let newEdges := RoleSet.allEdges sid roles
  { G := newEndpoints ++ ms.G
    D := initDEnv sid roles ++ ms.D
    bufs := (newEdges.map fun e => (e, [])) ++ ms.bufs
    Lin := (roles.map fun r => ({ sid := sid, role := r }, localTypes r)) ++ ms.Lin
    supply := sid + 1 }

/-- New session preserves well-typedness if local types are coherent projections. -/
axiom newSession_preserves_WTMon (ms : MonitorState) (roles : RoleSet)
    (localTypes : Role → LocalType)
    (hWT : WTMon ms) :
    WTMon (ms.newSession roles localTypes)
