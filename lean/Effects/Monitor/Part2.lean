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
theorem MonStep_preserves_WTMon (ms ms' : MonitorState) (act : ProtoAction) (v : Value)
    (hStep : MonStep ms act v ms')
    (hWTc : WTMonComplete ms) :
    WTMon ms' := by
  -- Unpack the complete invariant for use in the per-action cases.
  rcases hWTc with ⟨hWT, _hComplete⟩
  cases hStep with
  | send hG hRecvReady hLin hv =>
    -- Send case: enqueue value, advance sender type
    rename_i e target T L lin'  -- Bring implicit variables into scope
    constructor
    · -- Coherent: use Coherent_send_preserved
      have h := Coherent_send_preserved ms.G ms.D e target T L hWT.coherent hG hRecvReady
      simp only [MonitorState.sendEdge] at h ⊢
      exact h
    · -- HeadCoherent: send preserves head coherence
      -- The receiver's expected type doesn't change (only sender advances)
      -- Need hRecvReady: receiver can accept T after consuming current buffer
      have h := HeadCoherent_send_preserved ms.G ms.D e target T L hWT.headCoherent hWT.coherent hG hRecvReady
      simp only [MonitorState.sendEdge]
      exact h
    · -- ValidLabels: send preserves valid labels (no label changes)
      have h := ValidLabels_send_preserved (G:=ms.G) (D:=ms.D) (bufs:=ms.bufs)
        (senderEp:=e) (receiverRole:=target) (T:=T) (L:=L) (v:=v)
        (hValid:=hWT.validLabels) (hCoh:=hWT.coherent) (hBT:=hWT.buffers_typed)
        (hG:=hG) (hRecvReady:=hRecvReady)
      simp only [MonitorState.sendEdge, enqueueBuf]
      exact h
    · -- BuffersTyped: enqueue preserves buffer typing
      have h := BuffersTyped_send_preserved ms.G ms.D ms.bufs e target T L v hWT.buffers_typed hv hG
      simp only [MonitorState.sendEdge, enqueueBuf]
      exact h
    · -- lin_valid: produced token matches updated G
      intro e' S' hMem
      simp only [LinCtx.produceToken, List.mem_cons] at hMem
      cases hMem with
      | inl heq =>
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact lookupG_update_eq ms.G _ _
      | inr hTail =>
        -- Entry (e', S') ∈ lin' (after consuming e from ms.Lin)
        -- Case split on e' = e vs e' ≠ e
        by_cases he : e' = e
        · -- e' = e: Contradiction from linearity invariant
          subst he
          exact absurd hTail (consumeToken_not_mem _ _ _ _ hWT.lin_unique hLin S')
        · -- e' ≠ e: use that (e', S') was in ms.Lin and G is only updated at e
          have hInOrigLin : (e', S') ∈ ms.Lin := mem_of_consumeToken _ _ _ _ _ _ hLin hTail
          have hGlookup : lookupG ms.G e' = some S' := hWT.lin_valid e' S' hInOrigLin
          rw [lookupG_update_neq _ _ _ _ (Ne.symm he)]
          exact hGlookup
    · -- lin_unique: produceToken preserves Pairwise
      have hLin'Pairwise := consumeToken_pairwise _ _ _ _ hWT.lin_unique hLin
      have hNotIn := consumeToken_not_mem _ _ _ _ hWT.lin_unique hLin
      exact produceToken_pairwise _ _ _ hLin'Pairwise hNotIn
    · -- supply_fresh: all endpoints in new Lin have sid < supply
      have hLin'Fresh := consumeToken_preserves_supply_fresh _ _ _ _ _ hWT.supply_fresh hLin
      have hInOrig := consumeToken_endpoint_in_ctx _ _ _ _ hLin
      have heFresh := hWT.supply_fresh e _ hInOrig
      exact produceToken_preserves_supply_fresh _ _ _ _ hLin'Fresh heFresh
    · -- supply_fresh_G: all endpoints in updated G have sid < supply
      have hInOrig := consumeToken_endpoint_in_ctx _ _ _ _ hLin
      have heFresh := hWT.supply_fresh e _ hInOrig
      exact updateG_preserves_supply_fresh ms.G e L ms.supply hWT.supply_fresh_G heFresh

  | recv hG hLin hBuf hv =>
    -- Recv case: dequeue value, advance receiver type
    rename_i e source T L vs lin'
    constructor
    · -- Coherent: use Coherent_recv_preserved
      have hTyped := hWT.buffers_typed (MonitorState.recvEdge e source)
      have hTrace := trace_head_from_buffer hBuf hv hTyped
      have h := Coherent_recv_preserved ms.G ms.D e source T L hWT.coherent hG hTrace
      simp only [MonitorState.recvEdge] at h ⊢
      exact h
    · -- HeadCoherent: recv advances receiver, preserves head coherence
      -- Derive hTrace from BufferTyped using trace_head_from_buffer
      have hTyped := hWT.buffers_typed (MonitorState.recvEdge e source)
      have hTrace := trace_head_from_buffer hBuf hv hTyped
      have h := HeadCoherent_recv_preserved ms.G ms.D e source T L
        hWT.headCoherent hWT.coherent hG hTrace
      simp only [MonitorState.recvEdge]
      exact h
    · -- ValidLabels: recv dequeues from buffer, preserves valid labels
      have h := ValidLabels_recv_preserved ms.G ms.D ms.bufs e source T L v vs
        hWT.validLabels hWT.coherent hWT.buffers_typed hBuf hv hG
      -- h: ValidLabels G' D' (updateBuf bufs e (lookupBuf bufs e).tail)
      -- Goal: ValidLabels G' D' (updateBuf bufs e vs)
      -- From hBuf: lookupBuf bufs e = v :: vs, so (lookupBuf bufs e).tail = vs
      simp only [MonitorState.recvEdge] at h hBuf ⊢
      have hTail : (lookupBuf ms.bufs { sid := e.sid, sender := source, receiver := e.role }).tail = vs := by
        rw [hBuf]; rfl
      rw [hTail] at h
      exact h
    · -- BuffersTyped: dequeue preserves buffer typing
      have h := BuffersTyped_recv_preserved ms.G ms.D ms.bufs e source T L v vs hWT.buffers_typed hBuf hv hG
      simp only [MonitorState.recvEdge]
      exact h
    · -- lin_valid
      intro e' S' hMem
      simp only [LinCtx.produceToken, List.mem_cons] at hMem
      cases hMem with
      | inl heq =>
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact lookupG_update_eq ms.G _ _
      | inr hTail =>
        by_cases he : e' = e
        · -- e' = e: Contradiction from linearity invariant
          subst he
          exact absurd hTail (consumeToken_not_mem _ _ _ _ hWT.lin_unique hLin S')
        · have hInOrigLin : (e', S') ∈ ms.Lin := mem_of_consumeToken _ _ _ _ _ _ hLin hTail
          have hGlookup : lookupG ms.G e' = some S' := hWT.lin_valid e' S' hInOrigLin
          rw [lookupG_update_neq _ _ _ _ (Ne.symm he)]
          exact hGlookup
    · -- lin_unique: produceToken preserves Pairwise
      have hLin'Pairwise := consumeToken_pairwise _ _ _ _ hWT.lin_unique hLin
      have hNotIn := consumeToken_not_mem _ _ _ _ hWT.lin_unique hLin
      exact produceToken_pairwise _ _ _ hLin'Pairwise hNotIn
    · -- supply_fresh: all endpoints in new Lin have sid < supply
      have hLin'Fresh := consumeToken_preserves_supply_fresh _ _ _ _ _ hWT.supply_fresh hLin
      have hInOrig := consumeToken_endpoint_in_ctx _ _ _ _ hLin
      have heFresh := hWT.supply_fresh e _ hInOrig
      exact produceToken_preserves_supply_fresh _ _ _ _ hLin'Fresh heFresh
    · -- supply_fresh_G: all endpoints in updated G have sid < supply
      have hInOrig := consumeToken_endpoint_in_ctx _ _ _ _ hLin
      have heFresh := hWT.supply_fresh e _ hInOrig
      exact updateG_preserves_supply_fresh ms.G e L ms.supply hWT.supply_fresh_G heFresh

  | select hG hFind hRecvReady hLin =>
    -- Select case: like send but with label
    rename_i e target bs ℓ L lin'
    constructor
    · -- Coherent: use Coherent_select_preserved
      have h := Coherent_select_preserved ms.G ms.D e target bs ℓ L hWT.coherent hG hFind hRecvReady
      simp only [MonitorState.sendEdge] at h ⊢
      exact h
    · -- HeadCoherent: select preserves head coherence (appends to END)
      have h := HeadCoherent_select_preserved ms.G ms.D e target bs ℓ L hWT.headCoherent hWT.coherent hG hFind hRecvReady
      simp only [MonitorState.sendEdge]
      exact h
    · -- ValidLabels: select preserves valid labels (enqueues label at END)
      have h := ValidLabels_select_preserved (G:=ms.G) (D:=ms.D) (bufs:=ms.bufs)
        (selectorEp:=e) (targetRole:=target) (selectBranches:=bs) (ℓ:=ℓ) (L:=L)
        (hValid:=hWT.validLabels) (hCoh:=hWT.coherent) (hBT:=hWT.buffers_typed)
        (hG:=hG) (_hFind:=hFind) (hRecvReady:=hRecvReady)
      simp only [MonitorState.sendEdge, enqueueBuf]
      exact h
    · -- BuffersTyped: select enqueues label, preserves buffer typing
      have h := BuffersTyped_select_preserved ms.G ms.D ms.bufs e target bs ℓ L hWT.buffers_typed hG hFind
      simp only [MonitorState.sendEdge, enqueueBuf]
      exact h
    · -- lin_valid
      intro e' S' hMem
      simp only [LinCtx.produceToken, List.mem_cons] at hMem
      cases hMem with
      | inl heq =>
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact lookupG_update_eq ms.G _ _
      | inr hTail =>
        by_cases he : e' = e
        · -- e' = e: Contradiction from linearity invariant
          subst he
          exact absurd hTail (consumeToken_not_mem _ _ _ _ hWT.lin_unique hLin S')
        · have hInOrigLin : (e', S') ∈ ms.Lin := mem_of_consumeToken _ _ _ _ _ _ hLin hTail
          have hGlookup : lookupG ms.G e' = some S' := hWT.lin_valid e' S' hInOrigLin
          rw [lookupG_update_neq _ _ _ _ (Ne.symm he)]
          exact hGlookup
    · -- lin_unique: produceToken preserves Pairwise
      have hLin'Pairwise := consumeToken_pairwise _ _ _ _ hWT.lin_unique hLin
      have hNotIn := consumeToken_not_mem _ _ _ _ hWT.lin_unique hLin
      exact produceToken_pairwise _ _ _ hLin'Pairwise hNotIn
    · -- supply_fresh: all endpoints in new Lin have sid < supply
      have hLin'Fresh := consumeToken_preserves_supply_fresh _ _ _ _ _ hWT.supply_fresh hLin
      have hInOrig := consumeToken_endpoint_in_ctx _ _ _ _ hLin
      have heFresh := hWT.supply_fresh e _ hInOrig
      exact produceToken_preserves_supply_fresh _ _ _ _ hLin'Fresh heFresh
    · -- supply_fresh_G: all endpoints in updated G have sid < supply
      have hInOrig := consumeToken_endpoint_in_ctx _ _ _ _ hLin
      have heFresh := hWT.supply_fresh e _ hInOrig
      exact updateG_preserves_supply_fresh ms.G e L ms.supply hWT.supply_fresh_G heFresh

  | branch hG hBuf hFind hLin =>
    -- Branch case: like recv but with label selection
    rename_i e source bs ℓ L vs lin'
    constructor
    · -- Coherent: use Coherent_branch_preserved
      have hv : HasTypeVal ms.G (.string ℓ) .string := HasTypeVal.string ℓ
      have hTyped := hWT.buffers_typed (MonitorState.recvEdge e source)
      have hTrace := trace_head_from_buffer hBuf hv hTyped
      have h := Coherent_branch_preserved ms.G ms.D e source bs ℓ L hWT.coherent hG hFind hTrace
      simp only [MonitorState.recvEdge] at h ⊢
      exact h
    · -- HeadCoherent: branch dequeues label, preserves head coherence
      -- Derive hTrace from BufferTyped using trace_head_from_buffer
      have hv : HasTypeVal ms.G (.string ℓ) .string := HasTypeVal.string ℓ
      have hTyped := hWT.buffers_typed (MonitorState.recvEdge e source)
      have hTrace := trace_head_from_buffer hBuf hv hTyped
      have h := HeadCoherent_branch_preserved ms.G ms.D e source bs ℓ L
        hWT.headCoherent hWT.coherent hG hFind hTrace
      simp only [MonitorState.recvEdge]
      exact h
    · -- ValidLabels: branch dequeues label from buffer, preserves valid labels
      have h := ValidLabels_branch_preserved ms.G ms.D ms.bufs e source bs ℓ L vs
        hWT.validLabels hWT.coherent hWT.buffers_typed hG hFind hBuf
      simp only [MonitorState.recvEdge] at h ⊢
      exact h
    · -- BuffersTyped: branch dequeues label, preserves buffer typing
      have h := BuffersTyped_branch_preserved ms.G ms.D ms.bufs e source bs ℓ L vs hWT.buffers_typed hBuf hG hFind
      simp only [MonitorState.recvEdge]
      exact h
    · -- lin_valid
      intro e' S' hMem
      simp only [LinCtx.produceToken, List.mem_cons] at hMem
      cases hMem with
      | inl heq =>
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact lookupG_update_eq ms.G _ _
      | inr hTail =>
        by_cases he : e' = e
        · -- e' = e: Contradiction from linearity invariant
          subst he
          exact absurd hTail (consumeToken_not_mem _ _ _ _ hWT.lin_unique hLin S')
        · have hInOrigLin : (e', S') ∈ ms.Lin := mem_of_consumeToken _ _ _ _ _ _ hLin hTail
          have hGlookup : lookupG ms.G e' = some S' := hWT.lin_valid e' S' hInOrigLin
          rw [lookupG_update_neq _ _ _ _ (Ne.symm he)]
          exact hGlookup
    · -- lin_unique: produceToken preserves Pairwise
      have hLin'Pairwise := consumeToken_pairwise _ _ _ _ hWT.lin_unique hLin
      have hNotIn := consumeToken_not_mem _ _ _ _ hWT.lin_unique hLin
      exact produceToken_pairwise _ _ _ hLin'Pairwise hNotIn
    · -- supply_fresh: all endpoints in new Lin have sid < supply
      have hLin'Fresh := consumeToken_preserves_supply_fresh _ _ _ _ _ hWT.supply_fresh hLin
      have hInOrig := consumeToken_endpoint_in_ctx _ _ _ _ hLin
      have heFresh := hWT.supply_fresh e _ hInOrig
      exact produceToken_preserves_supply_fresh _ _ _ _ hLin'Fresh heFresh
    · -- supply_fresh_G: all endpoints in updated G have sid < supply
      have hInOrig := consumeToken_endpoint_in_ctx _ _ _ _ hLin
      have heFresh := hWT.supply_fresh e _ hInOrig
      exact updateG_preserves_supply_fresh ms.G e L ms.supply hWT.supply_fresh_G heFresh

/-! ## Token Linearity Properties -/

/-- Tokens cannot be duplicated: consuming removes from context.

Requires the linearity invariant (no duplicate endpoints in LinCtx). -/
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
      have : e.sid = sid := by simp only [heq, Endpoint.sid]
      exact hNeq this
    simp only [hNeqEndpoint, cond_false]
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
      simp only [hNeqEndpoint, cond_false]
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
theorem newSession_preserves_WTMon (ms : MonitorState) (roles : RoleSet)
    (localTypes : Role → LocalType)
    (hWT : WTMon ms)
    (hNodup : roles.Nodup)  -- Roles must be distinct
    (hConsD : DConsistent ms.G ms.D)
    (hConsB : BConsistent ms.G ms.bufs)
    (hProj : True)  -- Placeholder: localTypes are valid projections
    (hSenders :
      ∀ e Lrecv,
        lookupG (roles.map fun r => (Endpoint.mk ms.supply r, localTypes r))
          { sid := e.sid, role := e.receiver } = some Lrecv →
        ∃ Lsender,
          lookupG (roles.map fun r => (Endpoint.mk ms.supply r, localTypes r))
            { sid := e.sid, role := e.sender } = some Lsender)
    : WTMon (ms.newSession roles localTypes) := by
  simp only [MonitorState.newSession]
  have hSupplyNotIn : ms.supply ∉ SessionsOf ms.G := by
    intro hIn
    obtain ⟨e, L, hLookup, hSid⟩ := hIn
    have hMem : (e, L) ∈ ms.G := lookupG_mem ms.G e L hLookup
    have hFresh := hWT.supply_fresh_G e L hMem
    have hFresh' : ms.supply < ms.supply := by
      simpa [hSid] using hFresh
    exact (Nat.lt_irrefl _ hFresh')
  constructor
  · -- coherent: Coherent (newEndpoints ++ ms.G) ((newEdges.map (·, [])) ++ ms.D)
    intro e Lrecv hGrecv
    by_cases hSid : e.sid = ms.supply
    · -- New session edge: trace is empty, so Consume succeeds.
      have hDnone : ms.D.find? e = none :=
        DEnv_find_none_of_notin_sessions (G:=ms.G) (D:=ms.D) hConsD (by simpa [hSid] using hSupplyNotIn)
      have hLookupD :
          lookupD (initDEnv ms.supply roles ++ ms.D) e = lookupD (initDEnv ms.supply roles) e :=
        lookupD_append_left_of_right_none (D₁:=initDEnv ms.supply roles) (D₂:=ms.D) (e:=e) hDnone
      set recvEp : Endpoint := { sid := e.sid, role := e.receiver }
      have hRecvNone : lookupG ms.G recvEp = none := by
        apply lookupG_none_of_not_session
        simpa [hSid] using hSupplyNotIn
      have hInvRecv := lookupG_append_inv (G₁:=roles.map fun r => (Endpoint.mk ms.supply r, localTypes r))
        (G₂:=ms.G) (e:=recvEp) hGrecv
      have hGrecvNew : lookupG (roles.map fun r => (Endpoint.mk ms.supply r, localTypes r)) recvEp = some Lrecv := by
        cases hInvRecv with
        | inl hLeft => exact hLeft
        | inr hRight =>
            have : lookupG ms.G recvEp = some Lrecv := hRight.2
            have : False := by simpa [hRecvNone] using this
            exact this.elim
      rcases hSenders e Lrecv hGrecvNew with ⟨Lsender, hGsenderNew⟩
      have hGsenderMerged :
          lookupG ((roles.map fun r => (Endpoint.mk ms.supply r, localTypes r)) ++ ms.G)
            { sid := e.sid, role := e.sender } = some Lsender := by
        exact lookupG_append_left hGsenderNew
      refine ⟨Lsender, hGsenderMerged, ?_⟩
      -- Show lookupD initDEnv = [] for this edge.
      by_cases hMem : e ∈ RoleSet.allEdges ms.supply roles
      · have hInit : lookupD (initDEnv ms.supply roles) e = [] :=
          initDEnv_lookup_mem ms.supply roles e hMem
        simpa [hLookupD, hInit, Consume] using (by rfl : (Consume e.sender Lrecv []).isSome)
      · have hInitFind : (initDEnv ms.supply roles).find? e = none :=
          initDEnv_find?_none_of_notin ms.supply roles e hMem
        have hInit : lookupD (initDEnv ms.supply roles) e = [] := by
          simp [lookupD, hInitFind]
        simpa [hLookupD, hInit, Consume] using (by rfl : (Consume e.sender Lrecv []).isSome)
    · -- Old session edge: environments unchanged for this sid.
      have hSidNe : e.sid ≠ ms.supply := hSid
      set senderEp : Endpoint := { sid := e.sid, role := e.sender }
      set recvEp : Endpoint := { sid := e.sid, role := e.receiver }
      -- G lookups fall through to ms.G since new endpoints have different sid.
      have hSenderNone :
          (roles.map fun r => (Endpoint.mk ms.supply r, localTypes r)).lookup senderEp = none :=
        lookup_mapped_endpoints_sid_ne roles ms.supply localTypes _ (by simpa using hSidNe)
      have hRecvNone :
          (roles.map fun r => (Endpoint.mk ms.supply r, localTypes r)).lookup recvEp = none :=
        lookup_mapped_endpoints_sid_ne roles ms.supply localTypes _ (by simpa using hSidNe)
      have hInvRecv := lookupG_append_inv
        (G₁:=roles.map fun r => (Endpoint.mk ms.supply r, localTypes r)) (G₂:=ms.G) (e:=recvEp) hGrecv
      have hGrecv' : lookupG ms.G recvEp = some Lrecv := by
        cases hInvRecv with
        | inl hLeft =>
            have : False := by simpa [hRecvNone] using hLeft
            exact this.elim
        | inr hRight => exact hRight.2
      have hCohEdge := hWT.coherent e Lrecv hGrecv'
      rcases hCohEdge with ⟨Lsender, hGsender', hConsume⟩
      have hSenderEq := lookupG_append_right
        (G₁:=roles.map fun r => (Endpoint.mk ms.supply r, localTypes r)) (G₂:=ms.G) (e:=senderEp) hSenderNone
      have hGsenderMerged :
          lookupG ((roles.map fun r => (Endpoint.mk ms.supply r, localTypes r)) ++ ms.G) senderEp =
            some Lsender := by
        simpa [hSenderEq] using hGsender'
      -- D lookup falls through to ms.D since initDEnv has no entry for other sids.
      have hNotIn : e ∉ RoleSet.allEdges ms.supply roles := by
        intro hMem
        exact hSidNe (RoleSet.allEdges_sid ms.supply roles e hMem)
      have hFindNone : (initDEnv ms.supply roles).find? e = none :=
        initDEnv_find?_none_of_notin ms.supply roles e hNotIn
      have hLookupD :
          lookupD (initDEnv ms.supply roles ++ ms.D) e = lookupD ms.D e :=
        lookupD_append_right (D₁:=initDEnv ms.supply roles) (D₂:=ms.D) (e:=e) hFindNone
      refine ⟨Lsender, hGsenderMerged, ?_⟩
      simpa [hLookupD] using hConsume
  · -- headCoherent: HeadCoherent for combined G and D
    -- New edges have empty traces, so HeadCoherent trivially holds
    intro e
    simp only [HeadCoherent]
    by_cases hSid : e.sid = ms.supply
    · -- New session: trace is empty.
      have hDnone : ms.D.find? e = none :=
        DEnv_find_none_of_notin_sessions (G:=ms.G) (D:=ms.D) hConsD (by simpa [hSid] using hSupplyNotIn)
      have hLookupD :
          lookupD (initDEnv ms.supply roles ++ ms.D) e = lookupD (initDEnv ms.supply roles) e :=
        lookupD_append_left_of_right_none (D₁:=initDEnv ms.supply roles) (D₂:=ms.D) (e:=e) hDnone
      by_cases hMem : e ∈ RoleSet.allEdges ms.supply roles
      · have hInit : lookupD (initDEnv ms.supply roles) e = [] :=
          initDEnv_lookup_mem ms.supply roles e hMem
        cases hRecv :
            lookupG (List.map (fun r => ({ sid := ms.supply, role := r }, localTypes r)) roles ++ ms.G)
              { sid := e.sid, role := e.receiver } with
        | none =>
            simp [hLookupD, hInit, hRecv]
        | some Lrecv =>
            cases Lrecv <;> simp [hLookupD, hInit, hRecv]
      · have hInitFind : (initDEnv ms.supply roles).find? e = none :=
          initDEnv_find?_none_of_notin ms.supply roles e hMem
        have hInit : lookupD (initDEnv ms.supply roles) e = [] := by
          simp [lookupD, hInitFind]
        cases hRecv :
            lookupG (List.map (fun r => ({ sid := ms.supply, role := r }, localTypes r)) roles ++ ms.G)
              { sid := e.sid, role := e.receiver } with
        | none =>
            simp [hLookupD, hInit, hRecv]
        | some Lrecv =>
            cases Lrecv <;> simp [hLookupD, hInit, hRecv]
    · -- Old session: fall back to ms.HeadCoherent.
      have hSidNe : e.sid ≠ ms.supply := hSid
      have hRecvNone :
          (roles.map fun r => (Endpoint.mk ms.supply r, localTypes r)).lookup
            { sid := e.sid, role := e.receiver } = none :=
        lookup_mapped_endpoints_sid_ne roles ms.supply localTypes _ (by simpa using hSidNe)
      -- D lookup falls through to ms.D.
      have hNotIn : e ∉ RoleSet.allEdges ms.supply roles := by
        intro hMem
        exact hSidNe (RoleSet.allEdges_sid ms.supply roles e hMem)
      have hFindNone : (initDEnv ms.supply roles).find? e = none :=
        initDEnv_find?_none_of_notin ms.supply roles e hNotIn
      have hLookupD :
          lookupD (initDEnv ms.supply roles ++ ms.D) e = lookupD ms.D e :=
        lookupD_append_right (D₁:=initDEnv ms.supply roles) (D₂:=ms.D) (e:=e) hFindNone
      -- G lookup falls through to ms.G.
      simp [lookupG, List.lookup_append, hRecvNone, hLookupD] at *
      exact hWT.headCoherent e
  · -- validLabels: ValidLabels for combined G, D, bufs
    -- New edges have empty buffers, so ValidLabels trivially holds
    intro e source bs hLookup
    by_cases hSid : e.sid = ms.supply
    · -- New session: buffer is empty.
      by_cases hMem : e ∈ RoleSet.allEdges ms.supply roles
      · have hBufLookup := initBuffers_lookup_mem ms.supply roles e hMem
        have hBufLookup' :
            List.lookup e ((RoleSet.allEdges ms.supply roles).map (fun e => (e, ([] : List Value)))) =
              some ([] : List Value) := by
          simpa [initBuffers] using hBufLookup
        have hBuf :
            lookupBuf (List.map (fun e => (e, ([] : List Value))) (RoleSet.allEdges ms.supply roles) ++ ms.bufs) e = [] := by
          simp [lookupBuf, List.lookup_append, hBufLookup']
        simp [hBuf]
      · have hBufNone : ms.bufs.lookup e = none :=
          BConsistent_lookup_none_of_notin_sessions (G:=ms.G) (B:=ms.bufs) hConsB (by simpa [hSid] using hSupplyNotIn)
        have hLeftNone :
            List.lookup e ((RoleSet.allEdges ms.supply roles).map (fun e => (e, ([] : List Value)))) = none := by
          have hNone := initBuffers_lookup_none_of_notin ms.supply roles e hMem
          simpa [initBuffers] using hNone
        have hBuf :
            lookupBuf (List.map (fun e => (e, ([] : List Value))) (RoleSet.allEdges ms.supply roles) ++ ms.bufs) e = [] := by
          simp [lookupBuf, List.lookup_append, hLeftNone, hBufNone]
        simp [hBuf]
    · -- Old session: fall back to ms.validLabels.
      have hSidNe : e.sid ≠ ms.supply := hSid
      have hNotIn : e ∉ RoleSet.allEdges ms.supply roles := by
        intro hMem
        exact hSidNe (RoleSet.allEdges_sid ms.supply roles e hMem)
      have hBufNone :
          List.lookup e ((RoleSet.allEdges ms.supply roles).map (fun e => (e, ([] : List Value)))) = none := by
        have hNone := initBuffers_lookup_none_of_notin ms.supply roles e hNotIn
        simpa [initBuffers] using hNone
      have hRecvNone :
          (roles.map fun r => (Endpoint.mk ms.supply r, localTypes r)).lookup
            { sid := e.sid, role := e.receiver } = none :=
        lookup_mapped_endpoints_sid_ne roles ms.supply localTypes _ (by simpa using hSidNe)
      have hLookup' : lookupG ms.G { sid := e.sid, role := e.receiver } = some (.branch source bs) := by
        simpa [lookupG, List.lookup_append, hRecvNone] using hLookup
      have hBufEq :
          lookupBuf (List.map (fun e => (e, ([] : List Value))) (RoleSet.allEdges ms.supply roles) ++ ms.bufs) e =
            lookupBuf ms.bufs e := by
        simp [lookupBuf, List.lookup_append, hBufNone]
      have hValidOld := hWT.validLabels e source bs hLookup'
      simpa [hBufEq] using hValidOld
  · -- buffers_typed: BuffersTyped ... (newEdges.map (·, [])) ++ ms.bufs
    intro e
    by_cases hSid : e.sid = ms.supply
    · -- e.sid = ms.supply: edge belongs to new session
      by_cases hMem : e ∈ RoleSet.allEdges ms.supply roles
      · -- e is one of the new edges: buffer = [], trace = []
        have hBufLookup := initBuffers_lookup_mem ms.supply roles e hMem
        have hDnone : ms.D.find? e = none :=
          DEnv_find_none_of_notin_sessions (G:=ms.G) (D:=ms.D) hConsD (by simpa [hSid] using hSupplyNotIn)
        have hLookupD :
            lookupD (initDEnv ms.supply roles ++ ms.D) e = lookupD (initDEnv ms.supply roles) e :=
          lookupD_append_left_of_right_none (D₁:=initDEnv ms.supply roles) (D₂:=ms.D) (e:=e) hDnone
        have hTrace : lookupD (initDEnv ms.supply roles) e = [] :=
          initDEnv_lookup_mem ms.supply roles e hMem
        have hBufLookup' :
            List.lookup e ((RoleSet.allEdges ms.supply roles).map (fun e => (e, ([] : List Value)))) =
              some ([] : List Value) := by
          simpa [initBuffers] using hBufLookup
        have hBuf :
            lookupBuf (List.map (fun e => (e, ([] : List Value))) (RoleSet.allEdges ms.supply roles) ++ ms.bufs) e = [] := by
          simp [lookupBuf, List.lookup_append, hBufLookup']
        have hTrace' : lookupD (initDEnv ms.supply roles ++ ms.D) e = [] := by
          simpa [hLookupD, hTrace]
        exact bufferTyped_empty _ _ _ _ hBuf hTrace'
      · -- e is not in allEdges but has fresh sid
        -- This is an edge not created by this newSession (e.g., different roles)
        -- It shouldn't be in the old buffers either (fresh session ID)
        -- The lookup falls through to ms.bufs/ms.D, but since e.sid = ms.supply (fresh),
        -- by the supply invariant, e shouldn't be there either.
        have hBufNone : ms.bufs.lookup e = none :=
          BConsistent_lookup_none_of_notin_sessions (G:=ms.G) (B:=ms.bufs) hConsB (by simpa [hSid] using hSupplyNotIn)
        have hDnone : ms.D.find? e = none :=
          DEnv_find_none_of_notin_sessions (G:=ms.G) (D:=ms.D) hConsD (by simpa [hSid] using hSupplyNotIn)
        have hLookupD :
            lookupD (initDEnv ms.supply roles ++ ms.D) e = lookupD (initDEnv ms.supply roles) e :=
          lookupD_append_left_of_right_none (D₁:=initDEnv ms.supply roles) (D₂:=ms.D) (e:=e) hDnone
        have hInitFind : (initDEnv ms.supply roles).find? e = none :=
          initDEnv_find?_none_of_notin ms.supply roles e hMem
        have hTrace : lookupD (initDEnv ms.supply roles) e = [] := by
          simp [lookupD, hInitFind]
        have hLeftNone :
            List.lookup e ((RoleSet.allEdges ms.supply roles).map (fun e => (e, ([] : List Value)))) = none := by
          have hNone := initBuffers_lookup_none_of_notin ms.supply roles e hMem
          simpa [initBuffers] using hNone
        have hBuf :
            lookupBuf (List.map (fun e => (e, ([] : List Value))) (RoleSet.allEdges ms.supply roles) ++ ms.bufs) e = [] := by
          simp [lookupBuf, List.lookup_append, hLeftNone, hBufNone]
        have hTrace' : lookupD (initDEnv ms.supply roles ++ ms.D) e = [] := by
          simpa [hLookupD, hTrace]
        exact bufferTyped_empty _ _ _ _ hBuf hTrace'
    · -- e.sid ≠ ms.supply: edge from old session
      -- The lookup in initBuffers/initDEnv returns none, so we fall through to ms.bufs/ms.D
      -- Need to show HasTypeVal extends from ms.G to newEndpoints ++ ms.G
      -- This requires careful handling of the lookup_append rewriting
      have hSidNe : e.sid ≠ ms.supply := hSid
      have hNotIn : e ∉ RoleSet.allEdges ms.supply roles := by
        intro hMem
        exact hSidNe (RoleSet.allEdges_sid ms.supply roles e hMem)
      have hBufNone :
          List.lookup e ((RoleSet.allEdges ms.supply roles).map (fun e => (e, ([] : List Value)))) = none := by
        have hNone := initBuffers_lookup_none_of_notin ms.supply roles e hNotIn
        simpa [initBuffers] using hNone
      have hFindNone : (initDEnv ms.supply roles).find? e = none :=
        initDEnv_find?_none_of_notin ms.supply roles e hNotIn
      have hLookupD :
          lookupD (initDEnv ms.supply roles ++ ms.D) e = lookupD ms.D e :=
        lookupD_append_right (D₁:=initDEnv ms.supply roles) (D₂:=ms.D) (e:=e) hFindNone
      have hMono :
          ∀ ep L, lookupG ms.G ep = some L →
            lookupG ((roles.map fun r => (Endpoint.mk ms.supply r, localTypes r)) ++ ms.G) ep = some L := by
          intro ep L hLookup
          have hSid' : ep.sid ≠ ms.supply := by
            -- If ep.sid = supply, then it would be in SessionsOf ms.G, contradicting freshness.
            intro hEq
            have hMem : (ep, L) ∈ ms.G := lookupG_mem ms.G ep L hLookup
            have hFresh := hWT.supply_fresh_G ep L hMem
            have hFresh' : ms.supply < ms.supply := by simpa [hEq] using hFresh
            exact (Nat.lt_irrefl _ hFresh')
          have hNone :
              (roles.map fun r => (Endpoint.mk ms.supply r, localTypes r)).lookup ep = none :=
            lookup_mapped_endpoints_sid_ne roles ms.supply localTypes ep (by simpa using hSid')
          have hLookup' : List.lookup ep ms.G = some L := by
            simpa [lookupG] using hLookup
          simp [lookupG, List.lookup_append, hNone, hLookup']
      have hBT := hWT.buffers_typed e
      -- Rewrite buffers and D to fall back to ms.{bufs,D}, then weaken G.
      simp [lookupBuf, List.lookup_append, hBufNone, hLookupD] at hBT
      have hBT' :=
        BufferTyped_weakenG (G:=ms.G) (G':=(roles.map fun r => (Endpoint.mk ms.supply r, localTypes r)) ++ ms.G)
          (D:=ms.D) (bufs:=ms.bufs) (e:=e) hBT hMono
      -- Rewrite buffers and traces back to combined environments.
      simpa [BufferTyped, lookupBuf, List.lookup_append, hBufNone, hLookupD] using hBT'
  · -- lin_valid: for each (e, S) in combined Lin, lookupG G e = some S
    intro e S hMem
    simp only [List.mem_append, List.mem_map] at hMem
    cases hMem with
    | inl hNew =>
      -- e is in new endpoints (sid = ms.supply)
      obtain ⟨r, hrMem, heq⟩ := hNew
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      -- lookupG in prepended list finds the new entry
      simp only [lookupG, List.lookup_append]
      -- Use helper lemma: lookup in newEndpoints finds this entry
      have hLookup := lookup_mapped_endpoints_mem roles ms.supply localTypes r hrMem
      simp only [hLookup, Option.some_or]
    | inr hOld =>
      -- e is in ms.Lin, so e.sid < ms.supply (different from new endpoints)
      have heFresh : e.sid < ms.supply := hWT.supply_fresh e S hOld
      have hNeq : e.sid ≠ ms.supply := Nat.ne_of_lt heFresh
      -- lookupG in prepended list skips new entries (different sid)
      simp only [lookupG, List.lookup_append]
      -- lookup in newEndpoints returns none (e.sid ≠ ms.supply)
      have hLookupNone := lookup_mapped_endpoints_sid_ne roles ms.supply localTypes e hNeq
      simp only [hLookupNone, Option.none_or]
      -- Use hWT.lin_valid for the old entry
      exact hWT.lin_valid e S hOld
  · -- lin_unique: combined Lin is Pairwise distinct
    simp only [List.pairwise_append]
    constructor
    · -- New endpoints are pairwise distinct (from hNodup)
      -- Need to show: mapped list has distinct first components
      -- If r1 ≠ r2 then Endpoint.mk ms.supply r1 ≠ Endpoint.mk ms.supply r2
      have hInj : ∀ r1 r2, Endpoint.mk ms.supply r1 = Endpoint.mk ms.supply r2 → r1 = r2 := by
        intro r1 r2 heq
        simp only [Endpoint.mk.injEq] at heq
        exact heq.2
      -- Mapped list Pairwise follows from Nodup and injectivity
      induction roles with
      | nil => exact List.Pairwise.nil
      | cons hd tl ih =>
        simp only [List.map, List.pairwise_cons]
        simp only [List.nodup_cons] at hNodup
        obtain ⟨hNotMem, hTlNodup⟩ := hNodup
        constructor
        · -- hd's endpoint is different from all in tl's mapped list
          intro a haMem
          simp only [List.mem_map] at haMem
          obtain ⟨r, hrMem, rfl⟩ := haMem
          intro heq
          have hrEq : hd = r := hInj hd r heq
          exact hNotMem (hrEq ▸ hrMem)
        · exact ih hTlNodup
    constructor
    · -- Old endpoints are pairwise distinct
      exact hWT.lin_unique
    · -- Cross: new endpoints don't collide with old (different session IDs)
      intro a haMem b hbMem
      simp only [List.mem_map] at haMem
      obtain ⟨r, _, rfl⟩ := haMem
      -- a = ({ sid := ms.supply, role := r }, localTypes r), so a.1.sid = ms.supply
      -- b.1.sid < ms.supply
      have hbFresh : b.1.sid < ms.supply := hWT.supply_fresh b.1 b.2 hbMem
      intro heq
      -- heq : { sid := ms.supply, role := r } = b.1
      -- This means b.1.sid = ms.supply, contradicting hbFresh
      have hSidEq : b.1.sid = ms.supply := by rw [← heq]
      rw [hSidEq] at hbFresh
      exact Nat.lt_irrefl _ hbFresh
  · -- supply_fresh: all endpoints in combined Lin have sid < supply + 1
    intro e S hMem
    simp only [List.mem_append, List.mem_map] at hMem
    cases hMem with
    | inl hNew =>
      obtain ⟨r, _, heq⟩ := hNew
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      -- New endpoint has sid = ms.supply < ms.supply + 1
      exact Nat.lt_succ_self ms.supply
    | inr hOld =>
      -- Old endpoint has sid < ms.supply < ms.supply + 1
      have heFresh : e.sid < ms.supply := hWT.supply_fresh e S hOld
      exact Nat.lt_trans heFresh (Nat.lt_succ_self ms.supply)
  · -- supply_fresh_G: all endpoints in combined G have sid < supply + 1
    intro e S hMem
    simp only [List.mem_append, List.mem_map] at hMem
    cases hMem with
    | inl hNew =>
      obtain ⟨r, _, heq⟩ := hNew
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      -- New endpoint has sid = ms.supply < ms.supply + 1
      exact Nat.lt_succ_self ms.supply
    | inr hOld =>
      -- Old endpoint has sid < ms.supply < ms.supply + 1
      have heFresh : e.sid < ms.supply := hWT.supply_fresh_G e S hOld
      exact Nat.lt_trans heFresh (Nat.lt_succ_self ms.supply)

end
