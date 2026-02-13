import Protocol.Coherence
import Protocol.Decidability
import Protocol.Monitor.Core
import Protocol.Typing.Core
import Protocol.Typing.Compatibility

/-! # MPST Monitor Preservation

This module proves preservation for the verified monitor. -/

/-
The Problem. The monitor must maintain well-typedness after every transition.
We need to prove that `MonStep` preserves `WTMon`, connecting the runtime
monitor to the metatheory.

Solution Structure. We prove:
1. `MonStep_preserves_coherent`: coherence preserved by monitor steps
2. `MonStep_preserves_WTMon`: full well-typedness preservation
3. Connection to TypedStep for soundness
The proof uses the coherence preservation lemmas from Protocol.Coherence.
-/

/-! ## Overview

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

section

-- Preservation Theorem

/-- Monitor transitions preserve well-typedness.

This is the key soundness theorem: if the monitor state is well-typed
and we take a valid transition, the result is also well-typed. -/
private theorem lin_valid_after_consume_produce
    {G : GEnv} {Lin lin' : LinCtx} {e : Endpoint} {Lold Lnew : LocalType}
    (hLinValid : ∀ e' S', (e', S') ∈ Lin → lookupG G e' = some S')
    (hLinUnique : Lin.Pairwise (fun a b => a.1 ≠ b.1))
    (hConsume : LinCtx.consumeToken Lin e = some (lin', Lold)) :
    ∀ e' S', (e', S') ∈ LinCtx.produceToken lin' e Lnew →
      lookupG (updateG G e Lnew) e' = some S' := by
  intro e' S' hMem
  simp only [LinCtx.produceToken, List.mem_cons] at hMem
  cases hMem with
  | inl hHead =>
      rcases Prod.mk.inj hHead with ⟨hE, hS⟩
      subst hE
      subst hS
      simp
  | inr hTail =>
      have hOld : (e', S') ∈ Lin := mem_of_consumeToken Lin lin' e e' Lold S' hConsume hTail
      have hLookupOld : lookupG G e' = some S' := hLinValid e' S' hOld
      have hNe : e' ≠ e := by
        intro hEq
        have hMemE : (e, S') ∈ lin' := by
          simpa [hEq] using hTail
        exact consumeToken_not_mem Lin lin' e Lold hLinUnique hConsume S' hMemE
      simpa [lookupG_update_neq G e e' Lnew hNe.symm] using hLookupOld

-- Linear Pairwise/Freshness Helper Lemmas
private theorem lin_unique_after_consume_produce
    {Lin lin' : LinCtx} {e : Endpoint} {Lold Lnew : LocalType}
    (hLinUnique : Lin.Pairwise (fun a b => a.1 ≠ b.1))
    (hConsume : LinCtx.consumeToken Lin e = some (lin', Lold)) :
    (LinCtx.produceToken lin' e Lnew).Pairwise (fun a b => a.1 ≠ b.1) := by
  have hTailUnique : lin'.Pairwise (fun a b => a.1 ≠ b.1) :=
    consumeToken_pairwise Lin lin' e Lold hLinUnique hConsume
  have hNotIn : ∀ S', (e, S') ∉ lin' := by
    intro S'
    exact consumeToken_not_mem Lin lin' e Lold hLinUnique hConsume S'
  exact produceToken_pairwise lin' e Lnew hTailUnique hNotIn

private theorem endpoint_sid_fresh_of_consume
    {Lin lin' : LinCtx} {e : Endpoint} {Lold : LocalType} {supply : SessionId}
    (hFresh : ∀ e' S', (e', S') ∈ Lin → e'.sid < supply)
    (hConsume : LinCtx.consumeToken Lin e = some (lin', Lold)) :
    e.sid < supply := by
  have hIn : (e, Lold) ∈ Lin := consumeToken_endpoint_in_ctx Lin lin' e Lold hConsume
  exact hFresh e Lold hIn

-- Linear Supply Freshness Transport
private theorem lin_supply_fresh_after_consume_produce
    {Lin lin' : LinCtx} {e : Endpoint} {Lold Lnew : LocalType} {supply : SessionId}
    (hFresh : ∀ e' S', (e', S') ∈ Lin → e'.sid < supply)
    (hConsume : LinCtx.consumeToken Lin e = some (lin', Lold)) :
    ∀ e' S', (e', S') ∈ LinCtx.produceToken lin' e Lnew → e'.sid < supply := by
  intro e' S' hMem
  simp only [LinCtx.produceToken, List.mem_cons] at hMem
  cases hMem with
  | inl hHead =>
      rcases Prod.mk.inj hHead with ⟨hE, _⟩
      subst hE
      exact endpoint_sid_fresh_of_consume hFresh hConsume
  | inr hTail =>
      exact consumeToken_preserves_supply_fresh Lin lin' e Lold supply hFresh hConsume e' S' hTail

-- Main WTMon Preservation Theorem
theorem MonStep_preserves_WTMon (ms ms' : MonitorState) (act : ProtoAction) (v : Value)
    (hStep : MonStep ms act v ms')
    (hWTc : WTMonComplete ms) :
    WTMon ms' := by
  rcases hWTc with ⟨hWT, _hRoleComplete⟩
  rcases hWT with ⟨hCoh, hHead, hValid, hBT, hLinValid, hLinUnique, hSupplyFresh, hSupplyFreshG⟩
  cases hStep
  -- WTMon Preservation: Send Case
  case send hG hRecvReady hConsume hv =>
      rename_i e target T L lin'
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact Coherent_send_preserved ms.G ms.D e target T L hCoh hG hRecvReady
      · exact HeadCoherent_send_preserved ms.G ms.D e target T L hHead hCoh hG hRecvReady
      ·
        exact ValidLabels_send_preserved ms.G ms.D ms.bufs e target T L v
          hValid hCoh hBT hG hRecvReady
      · exact BuffersTyped_send_preserved ms.G ms.D ms.bufs e target T L v hBT hv hG
      ·
        intro e' S' hMem
        exact lin_valid_after_consume_produce
          (G:=ms.G) (Lin:=ms.Lin) (lin':=lin') (e:=e)
          (Lold:=.send target T L) (Lnew:=L)
          hLinValid hLinUnique hConsume e' S' hMem
      ·
        exact lin_unique_after_consume_produce
          (Lin:=ms.Lin) (lin':=lin') (e:=e)
          (Lold:=.send target T L) (Lnew:=L) hLinUnique hConsume
      ·
        intro e' S' hMem
        exact lin_supply_fresh_after_consume_produce
          (Lin:=ms.Lin) (lin':=lin') (e:=e)
          (Lold:=.send target T L) (Lnew:=L) (supply:=ms.supply)
          hSupplyFresh hConsume e' S' hMem
      ·
        have heFresh : e.sid < ms.supply :=
          endpoint_sid_fresh_of_consume
            (Lin:=ms.Lin) (lin':=lin') (e:=e)
            (Lold:=.send target T L) (supply:=ms.supply) hSupplyFresh hConsume
        exact updateG_preserves_supply_fresh ms.G e L ms.supply hSupplyFreshG heFresh
  -- WTMon Preservation: Recv Case
  case recv hG hConsume hBuf hv =>
      rename_i e source T L vs lin'
      have hTrace :
          (lookupD ms.D { sid := e.sid, sender := source, receiver := e.role }).head? = some T := by
        exact trace_head_from_buffer hBuf hv (hBT { sid := e.sid, sender := source, receiver := e.role })
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact Coherent_recv_preserved ms.G ms.D e source T L hCoh hG hTrace
      · exact HeadCoherent_recv_preserved ms.G ms.D e source T L hHead hCoh hG hTrace
      ·
        exact ValidLabels_recv_preserved ms.G ms.D ms.bufs e source T L v vs
          hValid hCoh hBT hBuf hv hG
      · exact BuffersTyped_recv_preserved ms.G ms.D ms.bufs e source T L v vs hBT hBuf hv hG
      ·
        intro e' S' hMem
        exact lin_valid_after_consume_produce
          (G:=ms.G) (Lin:=ms.Lin) (lin':=lin') (e:=e)
          (Lold:=.recv source T L) (Lnew:=L)
          hLinValid hLinUnique hConsume e' S' hMem
      ·
        exact lin_unique_after_consume_produce
          (Lin:=ms.Lin) (lin':=lin') (e:=e)
          (Lold:=.recv source T L) (Lnew:=L) hLinUnique hConsume
      ·
        intro e' S' hMem
        exact lin_supply_fresh_after_consume_produce
          (Lin:=ms.Lin) (lin':=lin') (e:=e)
          (Lold:=.recv source T L) (Lnew:=L) (supply:=ms.supply)
          hSupplyFresh hConsume e' S' hMem
      ·
        have heFresh : e.sid < ms.supply :=
          endpoint_sid_fresh_of_consume
            (Lin:=ms.Lin) (lin':=lin') (e:=e)
            (Lold:=.recv source T L) (supply:=ms.supply) hSupplyFresh hConsume
        exact updateG_preserves_supply_fresh ms.G e L ms.supply hSupplyFreshG heFresh
  -- WTMon Preservation: Select Case
  case select hG hFind hRecvReady hConsume =>
      rename_i e target bs ℓ L lin'
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact Coherent_select_preserved ms.G ms.D e target bs ℓ L hCoh hG hFind hRecvReady
      · exact HeadCoherent_select_preserved ms.G ms.D e target bs ℓ L hHead hCoh hG hFind hRecvReady
      ·
        exact ValidLabels_select_preserved ms.G ms.D ms.bufs e target bs ℓ L
          hValid hCoh hBT hG hFind hRecvReady
      · exact BuffersTyped_select_preserved ms.G ms.D ms.bufs e target bs ℓ L hBT hG hFind
      ·
        intro e' S' hMem
        exact lin_valid_after_consume_produce
          (G:=ms.G) (Lin:=ms.Lin) (lin':=lin') (e:=e)
          (Lold:=.select target bs) (Lnew:=L)
          hLinValid hLinUnique hConsume e' S' hMem
      ·
        exact lin_unique_after_consume_produce
          (Lin:=ms.Lin) (lin':=lin') (e:=e)
          (Lold:=.select target bs) (Lnew:=L) hLinUnique hConsume
      ·
        intro e' S' hMem
        exact lin_supply_fresh_after_consume_produce
          (Lin:=ms.Lin) (lin':=lin') (e:=e)
          (Lold:=.select target bs) (Lnew:=L) (supply:=ms.supply)
          hSupplyFresh hConsume e' S' hMem
      ·
        have heFresh : e.sid < ms.supply :=
          endpoint_sid_fresh_of_consume
            (Lin:=ms.Lin) (lin':=lin') (e:=e)
            (Lold:=.select target bs) (supply:=ms.supply) hSupplyFresh hConsume
        exact updateG_preserves_supply_fresh ms.G e L ms.supply hSupplyFreshG heFresh
  -- WTMon Preservation: Branch Case
  case branch hG hBuf hFind hConsume =>
      rename_i e source bs ℓ L vs lin'
      have hTrace :
          (lookupD ms.D { sid := e.sid, sender := source, receiver := e.role }).head? = some .string := by
        exact trace_head_from_buffer hBuf (HasTypeVal.string ℓ)
          (hBT { sid := e.sid, sender := source, receiver := e.role })
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact Coherent_branch_preserved ms.G ms.D e source bs ℓ L hCoh hG hFind hTrace
      · exact HeadCoherent_branch_preserved ms.G ms.D e source bs ℓ L hHead hCoh hG hFind hTrace
      ·
        exact ValidLabels_branch_preserved ms.G ms.D ms.bufs e source bs ℓ L vs
          hValid hCoh hBT hG hFind hBuf
      · exact BuffersTyped_branch_preserved ms.G ms.D ms.bufs e source bs ℓ L vs hBT hBuf hG hFind
      ·
        intro e' S' hMem
        exact lin_valid_after_consume_produce
          (G:=ms.G) (Lin:=ms.Lin) (lin':=lin') (e:=e)
          (Lold:=.branch source bs) (Lnew:=L)
          hLinValid hLinUnique hConsume e' S' hMem
      ·
        exact lin_unique_after_consume_produce
          (Lin:=ms.Lin) (lin':=lin') (e:=e)
          (Lold:=.branch source bs) (Lnew:=L) hLinUnique hConsume
      ·
        intro e' S' hMem
        exact lin_supply_fresh_after_consume_produce
          (Lin:=ms.Lin) (lin':=lin') (e:=e)
          (Lold:=.branch source bs) (Lnew:=L) (supply:=ms.supply)
          hSupplyFresh hConsume e' S' hMem
      ·
        have heFresh : e.sid < ms.supply :=
          endpoint_sid_fresh_of_consume
            (Lin:=ms.Lin) (lin':=lin') (e:=e)
            (Lold:=.branch source bs) (supply:=ms.supply) hSupplyFresh hConsume
        exact updateG_preserves_supply_fresh ms.G e L ms.supply hSupplyFreshG heFresh

-- Token Removal Corollary
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

-- Buffer and DEnv Consistency Helpers

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

-- Session Creation

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
private def newSessionEndpoints (sid : SessionId) (roles : RoleSet)
    (localTypes : Role → LocalType) : GEnv :=
  roles.map fun r => ({ sid := sid, role := r }, localTypes r)

private def newSessionBuffers (sid : SessionId) (roles : RoleSet) : Buffers :=
  (RoleSet.allEdges sid roles).map fun e => (e, [])

private def newSessionLin (sid : SessionId) (roles : RoleSet)
    (localTypes : Role → LocalType) : LinCtx :=
  roles.map fun r => ({ sid := sid, role := r }, localTypes r)

-- Certified Session Initialization Requirement

/-- Compile-time proof bundle required to call `MonitorState.newSession`.

If Lean reports `NewSessionCert ...` is missing, provide:
1. `roles_nodup`: no duplicate roles in the new session.
2. `seed_wt`: a proof that the freshly initialized session state at `ms.supply`
   is well-typed (`WTMon`). -/
structure NewSessionCert (ms : MonitorState) (roles : RoleSet)
    (localTypes : Role → LocalType) : Prop where
  /-- No duplicate roles/endpoints in the newly created session. -/
  roles_nodup : roles.Nodup
  /-- Certified well-typedness for the new-session seed at fresh session id. -/
  seed_wt :
    WTMon
      { G := newSessionEndpoints ms.supply roles localTypes
        D := initDEnv ms.supply roles
        bufs := newSessionBuffers ms.supply roles
        Lin := newSessionLin ms.supply roles localTypes
        supply := ms.supply + 1 }

/--
Named requirement used at `newSession` call sites.

If this is missing, Lean emits an error mentioning
`CertifiedDeploymentProofForNewSession ...`, making it explicit that callers
must provide certified deployment evidence (role uniqueness + seed `WTMon`).
-/
abbrev CertifiedDeploymentProofForNewSession
    (ms : MonitorState) (roles : RoleSet) (localTypes : Role → LocalType) : Prop :=
  NewSessionCert ms roles localTypes

def MonitorState.newSession (ms : MonitorState) (roles : RoleSet)
    (localTypes : Role → LocalType)
    (_cert : CertifiedDeploymentProofForNewSession ms roles localTypes) : MonitorState :=
  let sid := ms.supply
  let newEndpoints := newSessionEndpoints sid roles localTypes
  let newBufs := newSessionBuffers sid roles
  let newLin := newSessionLin sid roles localTypes
  { G := newEndpoints ++ ms.G
    D := initDEnv sid roles ++ ms.D
    bufs := newBufs ++ ms.bufs
    Lin := newLin ++ ms.Lin
    supply := sid + 1 }

/- NOTE:
`MonitorState.newSession` is currently consumed through certified deployment
paths (`DeployedProtocol.initMonitorState_wellTyped`), which provide explicit
proof artifacts for initialization. A generic preservation theorem over
arbitrary `roles/localTypes` is intentionally omitted here. -/
