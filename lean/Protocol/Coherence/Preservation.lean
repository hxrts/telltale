import Protocol.Coherence.PreservationRecv
import Protocol.Coherence.StoreTyping
import Protocol.Coherence.Unified

/-! # Protocol.Coherence.Preservation

Coherence lemmas and invariants for session-environment evolution.
-/


/-! # MPST Coherence: Preservation

This module proves coherence preservation under all protocol steps.
-/

/-
The Problem. Coherence must be preserved by every step (send, recv, select, branch,
open, close, delegation). This is the main preservation theorem for MPST.

Solution Structure. We combine the per-step preservation lemmas:
1. Head preservation lemmas for send/recv/select/branch
2. Session management (open/close) preservation
3. Delegation preservation via `DelegationEnvelope`
4. Main theorem: `Coherent_step_preserved`
-/


/-!
In binary session types, coherence states that after consuming in-flight messages,
dual endpoints have dual types. In MPST, this generalizes to:

**For each directed edge (p → q) in session s:**
1. The sender's local type G[s,p] is consistent with what was sent on D[s,p,q]
2. The receiver's local type G[s,q] is consistent with what must be received on D[s,p,q]
3. The communication patterns match: sends to q align with branches from p

## Consume Function

The `Consume` function models how a local type evolves as buffered messages arrive.
For role p's view:
- `Consume L [] = some L` (no messages → unchanged)
- `Consume (recv q T L) (T :: ts) = Consume L ts` (receive consumes a message)
- `Consume (branch q bs) _ = ...` (branch must handle incoming label)

## Coherence Invariant

`Coherent G D` states that for every session and every directed edge:
- Sender's continuation after sending matches what's in the queue
- Receiver's continuation after consuming matches sender's intent

## Proof Technique: Edge Case Analysis

The key preservation proofs (`Coherent_send_preserved`, `Coherent_recv_preserved`)
proceed by case analysis on which edge we're checking coherence for:

1. **e = updated edge**: The sender's/receiver's local type changed, trace changed
2. **e involves modified endpoint**: The other endpoint of e was modified
3. **e unrelated**: Neither endpoint was modified, environments unchanged at e

This 3-way case split is the core proof technique for coherence preservation.
Adapted from binary session types where the split is: a = e, a = e.dual, a unrelated.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

-- Coherence Preservation Lemmas

/-- Coherence is preserved when we send a value from p to q.
    Sending updates:
    - G[p] advances (send to q consumed)
    - D[p,q] grows (type appended to trace)

    **Proof strategy** (3-way case split on edge a):

    1. **a = e (the send edge p→q)**:
       - Sender (p) type changes from `send q T L` to `L`
       - Trace D[p,q] grows by T
       - Need: receiver (q) can still consume the trace
       - Key: use `hRecvReady` + `Consume_append` to show receiver handles extended trace

    2. **a involves sender endpoint p (but a ≠ e)**:
       - e.g., edge p→r for r ≠ q
       - Only G[p] changed (not G[r])
       - D[p,r] unchanged (only D[p,q] = D[e] changed)
       - Use `EdgeCoherent_updateG_irrelevant` and `EdgeCoherent_updateD_irrelevant`

    3. **a unrelated to p**:
       - Neither G nor D changed at a
       - Use irrelevance lemmas

    The `hRecvReady` hypothesis is required. Without it, the theorem is FALSE.
    We cannot guarantee the receiver can handle T after consuming the current buffer.

    Reference: `work/effects/004.lean` Coherent_send_preserved -/
-- Send Preservation: Edge Case Analysis
theorem Coherent_send_preserved
    (G : GEnv) (D : DEnv) (senderEp : Endpoint) (receiverRole : Role) (T : ValType) (L : LocalType)
    (hCoh : Coherent G D)
    (hG : lookupG G senderEp = some (.send receiverRole T L))
    -- CRITICAL: The receiver must be ready to accept T after consuming current buffer
    (hRecvReady : ∀ Lrecv, lookupG G { sid := senderEp.sid, role := receiverRole } = some Lrecv →
      ∃ L', Consume senderEp.role Lrecv (lookupD D { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole }) = some L' ∧
            (Consume senderEp.role L' [T]).isSome) :
    let sendEdge := { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole : Edge }
    Coherent (updateG G senderEp L) (updateD D sendEdge (lookupD D sendEdge ++ [T])) := by
  intro sendEdge e hActive  -- The edge we need to show coherence for
  have hActiveOrig : ActiveEdge G e :=
    ActiveEdge_updateG_inv (G:=G) (e:=e) (ep:=senderEp) (L:=L) hActive (by simpa [hG])

  -- Case 1: Updated Edge
  -- Case split: updated edge / shares sender endpoint / unrelated
  rcases edge_case_split e sendEdge senderEp with heq | hShare | hOther
  · -- Case 1: e = sendEdge (the edge being modified)
    subst heq
    simp only [EdgeCoherent]
    intro Lrecv hGrecv
    -- For sendEdge: sender = senderEp.role, receiver = receiverRole
    -- Sender endpoint lookup in updated G
    have hSenderLookup : lookupG (updateG G senderEp L) { sid := senderEp.sid, role := senderEp.role } = some L := by
      convert lookupG_update_eq G senderEp L
    refine ⟨L, hSenderLookup, ?_⟩
    -- Case 1A: Updated Edge Self-Send
    -- Check if receiver = sender (self-send case)
    by_cases hRecvIsSender : receiverRole = senderEp.role
    · -- Self-send: receiver role = sender role
      subst hRecvIsSender
      -- Receiver lookup gives L
      have hRecvLookup : lookupG (updateG G senderEp L) { sid := senderEp.sid, role := senderEp.role } = some L := by
        simpa using hSenderLookup
      have hEq : Lrecv = L := by
        have : some L = some Lrecv := by
          simpa [hRecvLookup, sendEdge] using hGrecv
        exact (Option.some.inj this).symm
      simp only [lookupD_update_eq]
      -- Use hRecvReady - in self-send case, receiver's original type is the sender's type
      -- Note: hRecvReady with a SEND original type is actually unsatisfiable!
      -- Consume on SEND type only succeeds with empty trace, giving back the SEND type.
      -- Then hL'T requires Consume (SEND) [T] to be some, but that's none.
      -- So we derive a contradiction.
      obtain ⟨L', hL', hL'T⟩ := hRecvReady (.send senderEp.role T L) hG
      -- Case on the trace to derive a contradiction
      -- Consume of SEND type only succeeds with empty trace
      cases hTrace : lookupD D { sid := senderEp.sid, sender := senderEp.role, receiver := senderEp.role } with
      | nil =>
        rw [hTrace] at hL'
        simp only [Consume] at hL'
        simp only [Option.some.injEq] at hL'
        subst hL'
        simp only [Consume, consumeOne, Option.isSome] at hL'T
        -- hL'T : false = true is a contradiction
        exact Bool.noConfusion hL'T
      | cons t ts =>
        rw [hTrace] at hL'
        simp only [Consume, consumeOne] at hL'
        -- hL' : none = some L' is a contradiction
        exact Option.noConfusion hL'
    -- Case 1B: Updated Edge Distinct Receiver
    · -- Normal case: receiver ≠ sender
      have hRecvNeq : senderEp ≠ { sid := senderEp.sid, role := receiverRole } := by
        intro h
        have : senderEp.role = receiverRole := by
          have h' := congrArg Endpoint.role h
          simp at h'
          exact h'
        exact hRecvIsSender this.symm
      have hGrecv' : lookupG G { sid := senderEp.sid, role := receiverRole } = some Lrecv := by
        simpa [lookupG_update_neq _ _ _ _ hRecvNeq, sendEdge] using hGrecv
      simp only [lookupD_update_eq]
      -- Use hRecvReady with receiver's original type
      obtain ⟨L', hL', hL'T⟩ := hRecvReady Lrecv hGrecv'
      rw [Consume_append _ _ _ _ hL']
      exact hL'T
  -- Case 2: Unchanged Edge Sharing Sender Endpoint
  · -- Case 2: e ≠ sendEdge, but e shares senderEp
    -- EdgeCoherent_updateD_irrelevant needs: sendEdge ≠ e
    have hNeSymm : sendEdge ≠ e := Ne.symm hShare.1
    have hShare' : { sid := e.sid, role := e.sender : Endpoint } = senderEp ∨
        { sid := e.sid, role := e.receiver : Endpoint } = senderEp := by
      simpa [EdgeShares, senderEndpoint, receiverEndpoint] using hShare.2
    -- Case 2A: Sender Endpoint Matches
    -- Check if senderEp is involved in edge e's endpoints
    by_cases hSenderMatch : { sid := e.sid, role := e.sender : Endpoint } = senderEp
    · -- Sender endpoint is senderEp
      by_cases hRecvMatch : { sid := e.sid, role := e.receiver : Endpoint } = senderEp
      · -- Both endpoints are senderEp - self-loop case
        -- Extract components from endpoint equalities
        have hSid1 : e.sid = senderEp.sid := congrArg Endpoint.sid hSenderMatch
        have hRole1 : e.sender = senderEp.role := congrArg Endpoint.role hSenderMatch
        have hSid2 : e.sid = senderEp.sid := congrArg Endpoint.sid hRecvMatch
        have hRole2 : e.receiver = senderEp.role := congrArg Endpoint.role hRecvMatch
        -- e is a self-loop at senderEp, but e ≠ sendEdge
        simp only [EdgeCoherent]
        intro Lrecv hGrecv
        -- Both lookups in updated G give L
        have hLookupS : lookupG (updateG G senderEp L) { sid := e.sid, role := e.sender } = some L := by
          conv => lhs; rw [hSid1, hRole1]
          exact lookupG_update_eq G senderEp L
        have hLookupR : lookupG (updateG G senderEp L) { sid := e.sid, role := e.receiver } = some L := by
          conv => lhs; rw [hSid2, hRole2]
          exact lookupG_update_eq G senderEp L
        have hEq : Lrecv = L := by
          have : some L = some Lrecv := by
            simpa [hLookupR] using hGrecv
          exact (Option.some.inj this).symm
        refine ⟨L, hLookupS, ?_⟩
        rw [lookupD_update_neq _ _ _ _ hNeSymm]
        -- Need to show Consume e.sender L (lookupD D e) is some
        -- Original coherence: sender had type .send receiverRole T L, receiver had same type
        -- Consume on SEND type only succeeds with empty trace
        have hOrigCoh := Coherent_edge_any hCoh hActiveOrig
        have hOrigRecvG : lookupG G { sid := e.sid, role := e.receiver } = some (.send receiverRole T L) := by
          conv => lhs; rw [hSid2, hRole2]; exact hG
        have hOrig := EdgeCoherent_consume_of_receiver hOrigCoh hOrigRecvG
        -- If trace is non-empty, Consume on SEND fails, contradicting hOrig
        cases hTrace : lookupD D e with
        | nil =>
          rw [hRole1]
          simp only [Consume, Option.isSome]
        | cons t ts =>
          rw [hRole1, hTrace] at hOrig
          simp only [Consume, consumeOne, Option.isSome] at hOrig
          -- hOrig : false = true is a contradiction
          exact Bool.noConfusion hOrig
      -- Case 2A(ii): Sender Matches, Receiver Distinct
      · -- Sender endpoint = senderEp, receiver endpoint ≠ senderEp
        -- Sender's type changed to L, but EdgeCoherent only checks receiver's Consume
        -- The receiver's type and trace are unchanged
        have hRecvNoMatch : senderEp ≠ { sid := e.sid, role := e.receiver } := fun h => hRecvMatch h.symm
        apply EdgeCoherent_updateD_irrelevant _ _ _ _ _ hNeSymm
        -- For EdgeCoherent_updateG_irrelevant, we need both endpoints ≠ senderEp
        -- But sender endpoint = senderEp! So we can't use that lemma directly.
        -- However, EdgeCoherent doesn't actually depend on sender's type in a way that matters
        -- Let's prove it directly
        simp only [EdgeCoherent]
        intro Lrecv hGrecv
        -- Receiver lookup is unchanged (receiver ≠ senderEp)
        have hGrecv' : lookupG G { sid := e.sid, role := e.receiver } = some Lrecv := by
          simpa [lookupG_update_neq _ _ _ _ hRecvNoMatch] using hGrecv
        -- Original coherence gives Consume for the unchanged receiver/trace
        have hOrigCoh := Coherent_edge_any hCoh hActiveOrig
        have hConsume := EdgeCoherent_consume_of_receiver hOrigCoh hGrecv'
        -- Sender endpoint is senderEp, so its updated lookup provides existence
        have hSid : e.sid = senderEp.sid := congrArg Endpoint.sid hSenderMatch
        have hRole : e.sender = senderEp.role := congrArg Endpoint.role hSenderMatch
        have hSenderLookup : lookupG (updateG G senderEp L) { sid := e.sid, role := e.sender } = some L := by
          conv => lhs; rw [hSid, hRole]; exact lookupG_update_eq G senderEp L
        refine ⟨L, hSenderLookup, hConsume⟩
    -- Case 2B: Receiver Endpoint Matches
    · -- Sender endpoint ≠ senderEp, so receiver must match
      have hSenderNoMatch : senderEp ≠ { sid := e.sid, role := e.sender } := fun h => hSenderMatch h.symm
      have hRecvMatch : { sid := e.sid, role := e.receiver : Endpoint } = senderEp := by
        cases hShare' with
        | inl h => exact (hSenderMatch h).elim
        | inr h => exact h
      -- Receiver endpoint = senderEp, sender endpoint ≠ senderEp
      -- Receiver's type changed from .send receiverRole T L to L
      -- But original coherence required Consume on the SEND type to succeed
      -- This means trace was empty, so Consume on L with empty trace succeeds
      apply EdgeCoherent_updateD_irrelevant _ _ _ _ _ hNeSymm
      simp only [EdgeCoherent]
      intro Lrecv hGrecv
      -- Receiver lookup gives L
      have hSid : e.sid = senderEp.sid := congrArg Endpoint.sid hRecvMatch
      have hRole : e.receiver = senderEp.role := congrArg Endpoint.role hRecvMatch
      have hRecvLookup : lookupG (updateG G senderEp L) { sid := e.sid, role := e.receiver } = some L := by
        conv => lhs; rw [hSid, hRole]; exact lookupG_update_eq G senderEp L
      have hEq : Lrecv = L := by
        have : some L = some Lrecv := by
          simpa [hRecvLookup] using hGrecv
        exact (Option.some.inj this).symm
      -- Original coherence: receiver had SEND type, so Consume only works on empty trace
      have hOrigCoh := Coherent_edge_any hCoh hActiveOrig
      have hOrigRecv : lookupG G { sid := e.sid, role := e.receiver } = some (.send receiverRole T L) := by
        conv => lhs; rw [hSid, hRole]; exact hG
      have hOrig := EdgeCoherent_consume_of_receiver hOrigCoh hOrigRecv
      -- Sender existence (unchanged by update)
      rcases EdgeCoherent_sender_of_receiver hOrigCoh hOrigRecv with ⟨Lsender, hGsender⟩
      have hGsender' : lookupG (updateG G senderEp L) { sid := e.sid, role := e.sender } = some Lsender := by
        simpa [lookupG_update_neq _ _ _ _ hSenderNoMatch] using hGsender
      refine ⟨Lsender, hGsender', ?_⟩
      -- Consume e.sender (send ...) trace only succeeds if trace = []
      cases hTrace : lookupD D e with
      | nil =>
        simp only [Consume, Option.isSome]
      | cons t ts =>
        rw [hTrace] at hOrig
        simp only [Consume, consumeOne, Option.isSome] at hOrig
        exact Bool.noConfusion hOrig
  -- Case 3: Unrelated Edge
  · -- Case 3: e ≠ sendEdge and unrelated to senderEp
    have hNeSymm : sendEdge ≠ e := Ne.symm hOther.1
    have hOther' :
        ¬ ({ sid := e.sid, role := e.sender : Endpoint } = senderEp ∨
            { sid := e.sid, role := e.receiver : Endpoint } = senderEp) := by
      simpa [EdgeShares, senderEndpoint, receiverEndpoint] using hOther.2
    have hSenderNoMatch : senderEp ≠ { sid := e.sid, role := e.sender } := by
      intro h
      apply hOther'
      exact Or.inl h.symm
    have hRecvNoMatch : senderEp ≠ { sid := e.sid, role := e.receiver } := by
      intro h
      apply hOther'
      exact Or.inr h.symm
    apply EdgeCoherent_updateD_irrelevant _ _ _ _ _ hNeSymm
    exact EdgeCoherent_updateG_irrelevant _ _ _ _ _ hSenderNoMatch hRecvNoMatch (Coherent_edge_any hCoh hActiveOrig)


end
