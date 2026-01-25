import Effects.Environments

/-!
# MPST Coherence

This module defines the coherence invariant for multiparty session types.

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

noncomputable section

/-! ## Coherence Preservation Lemmas -/

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
  intro sendEdge e  -- The edge we need to show coherence for

  -- Case split: is e the send edge or not?
  by_cases heq : e = sendEdge
  · -- Case 1: e = sendEdge (the edge being modified)
    subst heq
    simp only [EdgeCoherent]
    intro Lsender Lrecv hGsender hGrecv
    -- For sendEdge: sender = senderEp.role, receiver = receiverRole
    -- Sender endpoint lookup in updated G
    have hSenderLookup : lookupG (updateG G senderEp L) { sid := senderEp.sid, role := senderEp.role } = some L := by
      convert lookupG_update_eq G senderEp L
    -- Check if receiver = sender (self-send case)
    by_cases hRecvIsSender : receiverRole = senderEp.role
    · -- Self-send: receiver role = sender role
      subst hRecvIsSender
      -- Both lookups give L
      rw [hSenderLookup] at hGsender hGrecv
      simp only [Option.some.injEq] at hGsender hGrecv
      subst hGsender hGrecv
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
    · -- Normal case: receiver ≠ sender
      have hRecvNeq : senderEp ≠ { sid := senderEp.sid, role := receiverRole } := by
        intro h
        have : senderEp.role = receiverRole := by
          have h' := congrArg Endpoint.role h
          simp at h'
          exact h'
        exact hRecvIsSender this.symm
      rw [hSenderLookup] at hGsender
      rw [lookupG_update_neq _ _ _ _ hRecvNeq] at hGrecv
      simp only [Option.some.injEq] at hGsender
      subst hGsender
      simp only [lookupD_update_eq]
      -- Use hRecvReady with receiver's original type
      obtain ⟨L', hL', hL'T⟩ := hRecvReady Lrecv hGrecv
      rw [Consume_append _ _ _ _ hL']
      exact hL'T
  · -- Case 2: e ≠ sendEdge - use irrelevance lemmas
    -- EdgeCoherent_updateD_irrelevant needs: sendEdge ≠ e
    have hNeSymm : sendEdge ≠ e := Ne.symm heq
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
        intro Lsender Lrecv hGsender hGrecv
        -- Both lookups in updated G give L
        have hLookupS : lookupG (updateG G senderEp L) { sid := e.sid, role := e.sender } = some L := by
          conv => lhs; rw [hSid1, hRole1]
          exact lookupG_update_eq G senderEp L
        have hLookupR : lookupG (updateG G senderEp L) { sid := e.sid, role := e.receiver } = some L := by
          conv => lhs; rw [hSid2, hRole2]
          exact lookupG_update_eq G senderEp L
        rw [hLookupS] at hGsender
        rw [hLookupR] at hGrecv
        simp only [Option.some.injEq] at hGsender hGrecv
        subst hGsender hGrecv
        rw [lookupD_update_neq _ _ _ _ hNeSymm]
        -- Need to show Consume e.sender L (lookupD D e) is some
        -- Original coherence: sender had type .send receiverRole T L, receiver had same type
        -- Consume on SEND type only succeeds with empty trace
        have hOrigCoh := hCoh e
        simp only [EdgeCoherent] at hOrigCoh
        have hOrigSenderG : lookupG G { sid := e.sid, role := e.sender } = some (.send receiverRole T L) := by
          conv => lhs; rw [hSid1, hRole1]; exact hG
        have hOrigRecvG : lookupG G { sid := e.sid, role := e.receiver } = some (.send receiverRole T L) := by
          conv => lhs; rw [hSid2, hRole2]; exact hG
        have hOrig := hOrigCoh (.send receiverRole T L) (.send receiverRole T L) hOrigSenderG hOrigRecvG
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
        intro Lsender Lrecv hGsender hGrecv
        -- Receiver lookup is unchanged (receiver ≠ senderEp)
        rw [lookupG_update_neq _ _ _ _ hRecvNoMatch] at hGrecv
        -- Trace is unchanged (e ≠ sendEdge, so lookupD unchanged)
        -- Original coherence with same receiver type and same trace
        have hOrigCoh := hCoh e
        simp only [EdgeCoherent] at hOrigCoh
        -- Get original sender type
        have hSid : e.sid = senderEp.sid := congrArg Endpoint.sid hSenderMatch
        have hRole : e.sender = senderEp.role := congrArg Endpoint.role hSenderMatch
        have hOrigSender : lookupG G { sid := e.sid, role := e.sender } = some (.send receiverRole T L) := by
          conv => lhs; rw [hSid, hRole]; exact hG
        exact hOrigCoh (.send receiverRole T L) Lrecv hOrigSender hGrecv
    · -- Sender endpoint ≠ senderEp
      have hSenderNoMatch : senderEp ≠ { sid := e.sid, role := e.sender } := fun h => hSenderMatch h.symm
      by_cases hRecvMatch : { sid := e.sid, role := e.receiver : Endpoint } = senderEp
      · -- Receiver endpoint = senderEp, sender endpoint ≠ senderEp
        -- Receiver's type changed from .send receiverRole T L to L
        -- But original coherence required Consume on the SEND type to succeed
        -- This means trace was empty, so Consume on L with empty trace succeeds
        apply EdgeCoherent_updateD_irrelevant _ _ _ _ _ hNeSymm
        simp only [EdgeCoherent]
        intro Lsender Lrecv hGsender hGrecv
        -- Sender lookup is unchanged (sender ≠ senderEp)
        rw [lookupG_update_neq _ _ _ _ hSenderNoMatch] at hGsender
        -- Receiver lookup gives L
        have hSid : e.sid = senderEp.sid := congrArg Endpoint.sid hRecvMatch
        have hRole : e.receiver = senderEp.role := congrArg Endpoint.role hRecvMatch
        have hRecvLookup : lookupG (updateG G senderEp L) { sid := e.sid, role := e.receiver } = some L := by
          conv => lhs; rw [hSid, hRole]; exact lookupG_update_eq G senderEp L
        rw [hRecvLookup] at hGrecv
        simp only [Option.some.injEq] at hGrecv
        subst hGrecv
        -- Original coherence: receiver had SEND type, so Consume only works on empty trace
        have hOrigCoh := hCoh e
        simp only [EdgeCoherent] at hOrigCoh
        have hOrigRecv : lookupG G { sid := e.sid, role := e.receiver } = some (.send receiverRole T L) := by
          conv => lhs; rw [hSid, hRole]; exact hG
        have hOrig := hOrigCoh Lsender (.send receiverRole T L) hGsender hOrigRecv
        -- Consume e.sender (send ...) trace only succeeds if trace = []
        cases hTrace : lookupD D e with
        | nil =>
          simp only [Consume, Option.isSome]
        | cons t ts =>
          rw [hTrace] at hOrig
          simp only [Consume, consumeOne, Option.isSome] at hOrig
          exact Bool.noConfusion hOrig
      · -- Neither endpoint is senderEp - completely unrelated edge
        have hRecvNoMatch : senderEp ≠ { sid := e.sid, role := e.receiver } := fun h => hRecvMatch h.symm
        apply EdgeCoherent_updateD_irrelevant _ _ _ _ _ hNeSymm
        exact EdgeCoherent_updateG_irrelevant _ _ _ _ _ hSenderNoMatch hRecvNoMatch (hCoh e)

/-- Coherence is preserved when we receive a value at q from p.
    Receiving updates:
    - G[q] advances (recv from p consumed)
    - D[p,q] shrinks (type popped from trace)

    **Proof strategy** (3-way case split on edge a):

    1. **a = e (the recv edge p→q)**:
       - Receiver (q) type changes from `recv p T L` to `L`
       - Trace D[p,q] loses T from front
       - Key: the Consume function handles one less T, still matches

    2. **a involves receiver endpoint q (but a ≠ e)**:
       - e.g., edge r→q for r ≠ p
       - Only G[q] changed (not G[r])
       - D[r,q] unchanged (only D[p,q] = D[e] changed)
       - Use lookupG_update_neq and lookupD_update_neq

    3. **a unrelated to q**:
       - Neither G nor D changed at a
       - Old coherence witness still works

    This is the dual of the send case: popping T from trace D[p,q]
    corresponds to the receiver advancing from `recv p T L` to `L`. -/
theorem Coherent_recv_preserved
    (G : GEnv) (D : DEnv) (receiverEp : Endpoint) (senderRole : Role) (T : ValType) (L : LocalType)
    (hCoh : Coherent G D)
    (hG : lookupG G receiverEp = some (.recv senderRole T L))
    (hTrace : (lookupD D { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role }).head? = some T) :
    let e := { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role : Edge }
    Coherent (updateG G receiverEp L) (updateD D e (lookupD D e).tail) := by
  intro recvEdge e  -- The edge we need to show coherence for

  -- Case split: is e the recv edge or not?
  by_cases heq : e = recvEdge
  · -- Case 1: e = recvEdge (the edge being modified)
    subst heq
    simp only [EdgeCoherent]
    intro Lsender Lrecv hGsender hGrecv
    -- For recvEdge: sender = senderRole, receiver = receiverEp.role
    -- Receiver endpoint lookup in updated G
    have hRecvLookup : lookupG (updateG G receiverEp L) { sid := receiverEp.sid, role := receiverEp.role } = some L := by
      convert lookupG_update_eq G receiverEp L
    -- Check if sender = receiver (self-recv case)
    by_cases hSenderIsRecv : senderRole = receiverEp.role
    · -- Self-recv: sender role = receiver role
      subst hSenderIsRecv
      -- Both lookups give L
      rw [hRecvLookup] at hGsender hGrecv
      simp only [Option.some.injEq] at hGsender hGrecv
      subst hGsender hGrecv
      simp only [lookupD_update_eq]
      -- Original coherence at this edge
      have hOrigCoh := hCoh recvEdge
      simp only [EdgeCoherent] at hOrigCoh
      -- Receiver's original type was .recv, so original coherence worked
      -- The trace was T :: rest (from hTrace), original Consume consumed T and continued
      -- After recv, we consume from rest
      -- Use Consume_cons to decompose the original
      cases hTraceVal : lookupD D recvEdge with
      | nil =>
        -- If trace was empty, hTrace would say head? = some T, but [] has head? = none
        rw [hTraceVal] at hTrace
        simp only [List.head?] at hTrace
        -- hTrace : none = some T is a contradiction
        exact Option.noConfusion hTrace
      | cons t rest =>
        -- t = T from hTrace
        rw [hTraceVal] at hTrace
        simp only [List.head?, Option.some.injEq] at hTrace
        subst hTrace
        -- Original coherence: Consume recvEdge.role (.recv recvEdge.role t L) (t :: rest) is some
        have hOrig := hOrigCoh (.recv receiverEp.role t L) (.recv receiverEp.role t L) hG hG
        -- Decompose using Consume definition
        rw [hTraceVal] at hOrig
        -- recvEdge.sender = receiverEp.role, and after subst, t = T (the message type)
        -- The beq checks: recvEdge.sender == receiverEp.role (true) and t == t (true)
        simp only [Consume, consumeOne] at hOrig
        have hBeqRole : (recvEdge.sender == receiverEp.role) = true := beq_self_eq_true _
        have hBeqType : (t == t) = true := beq_self_eq_true _
        simp only [hBeqRole, hBeqType, Bool.and_self, ite_true] at hOrig
        -- Now we need: Consume recvEdge.sender L rest is some
        simp only [List.tail_cons]
        exact hOrig
    · -- Normal case: sender ≠ receiver
      have hSenderNeq : receiverEp ≠ { sid := receiverEp.sid, role := senderRole } := by
        intro h
        have : receiverEp.role = senderRole := congrArg Endpoint.role h
        exact hSenderIsRecv this.symm
      rw [hRecvLookup] at hGrecv
      rw [lookupG_update_neq _ _ _ _ hSenderNeq] at hGsender
      simp only [Option.some.injEq] at hGrecv
      subst hGrecv
      simp only [lookupD_update_eq]
      -- Original coherence
      have hOrigCoh := hCoh recvEdge
      simp only [EdgeCoherent] at hOrigCoh
      -- Use original coherence with receiver's original type
      cases hTraceVal : lookupD D recvEdge with
      | nil =>
        rw [hTraceVal] at hTrace
        simp only [List.head?] at hTrace
        exact Option.noConfusion hTrace
      | cons t rest =>
        rw [hTraceVal] at hTrace
        simp only [List.head?, Option.some.injEq] at hTrace
        subst hTrace
        have hOrig := hOrigCoh Lsender (.recv senderRole t L) hGsender hG
        rw [hTraceVal] at hOrig
        simp only [Consume, consumeOne] at hOrig
        -- recvEdge.sender = senderRole, and after subst, t = T
        have hBeqRole : (recvEdge.sender == senderRole) = true := beq_self_eq_true _
        have hBeqType : (t == t) = true := beq_self_eq_true _
        simp only [hBeqRole, hBeqType, Bool.and_self, ite_true] at hOrig
        simp only [List.tail_cons]
        exact hOrig
  · -- Case 2: e ≠ recvEdge - use irrelevance lemmas
    have hNeSymm : recvEdge ≠ e := Ne.symm heq
    -- Check if receiverEp is involved in edge e's endpoints
    by_cases hSenderMatch : { sid := e.sid, role := e.sender : Endpoint } = receiverEp
    · -- Sender endpoint is receiverEp
      by_cases hRecvMatch : { sid := e.sid, role := e.receiver : Endpoint } = receiverEp
      · -- Both endpoints are receiverEp - self-loop case
        have hSid1 : e.sid = receiverEp.sid := congrArg Endpoint.sid hSenderMatch
        have hRole1 : e.sender = receiverEp.role := congrArg Endpoint.role hSenderMatch
        have hSid2 : e.sid = receiverEp.sid := congrArg Endpoint.sid hRecvMatch
        have hRole2 : e.receiver = receiverEp.role := congrArg Endpoint.role hRecvMatch
        simp only [EdgeCoherent]
        intro Lsender Lrecv hGsender hGrecv
        have hLookupS : lookupG (updateG G receiverEp L) { sid := e.sid, role := e.sender } = some L := by
          conv => lhs; rw [hSid1, hRole1]
          exact lookupG_update_eq G receiverEp L
        have hLookupR : lookupG (updateG G receiverEp L) { sid := e.sid, role := e.receiver } = some L := by
          conv => lhs; rw [hSid2, hRole2]
          exact lookupG_update_eq G receiverEp L
        rw [hLookupS] at hGsender
        rw [hLookupR] at hGrecv
        simp only [Option.some.injEq] at hGsender hGrecv
        subst hGsender hGrecv
        rw [lookupD_update_neq _ _ _ _ hNeSymm]
        -- Original coherence at e with receiver's original type .recv
        have hOrigCoh := hCoh e
        simp only [EdgeCoherent] at hOrigCoh
        have hOrigSenderG : lookupG G { sid := e.sid, role := e.sender } = some (.recv senderRole T L) := by
          conv => lhs; rw [hSid1, hRole1]; exact hG
        have hOrigRecvG : lookupG G { sid := e.sid, role := e.receiver } = some (.recv senderRole T L) := by
          conv => lhs; rw [hSid2, hRole2]; exact hG
        have hOrig := hOrigCoh (.recv senderRole T L) (.recv senderRole T L) hOrigSenderG hOrigRecvG
        -- Consume e.sender (.recv senderRole T L) trace succeeds
        -- If sender ≠ senderRole, Consume only works on empty trace
        -- If sender = senderRole, Consume matches the recv
        -- Either way, we can derive Consume e.sender L trace.tail
        -- Actually, simpler: if trace is empty, Consume L [] = some L
        -- If trace is non-empty, original must have matched the recv, so...
        -- This case is complex. Let's use: after consuming, the type becomes L
        cases hTraceE : lookupD D e with
        | nil =>
          rw [hRole1]
          simp only [Consume, Option.isSome]
        | cons t ts =>
          -- Original coherence: Consume e.sender (.recv senderRole T L) (t::ts) is some
          -- For recv type, this only works if e.sender = senderRole and t = T
          rw [hRole1] at hOrig
          simp only [hTraceE, Consume, consumeOne] at hOrig
          -- If senderRole = receiverEp.role (from hRole1), then the match depends on T = t
          -- Check if senderRole = receiverEp.role
          by_cases hSR : senderRole = receiverEp.role
          · -- If senderRole = receiverEp.role, then e = recvEdge (contradiction with heq)
            -- recvEdge = {receiverEp.sid, senderRole, receiverEp.role}
            -- After hSR: recvEdge = {receiverEp.sid, receiverEp.role, receiverEp.role}
            -- e has: e.sid = receiverEp.sid, e.sender = receiverEp.role, e.receiver = receiverEp.role
            -- So e = recvEdge
            exfalso
            apply heq
            have hEdgeEq : e = recvEdge := by
              -- e.sid = receiverEp.sid = recvEdge.sid
              -- e.sender = receiverEp.role = senderRole = recvEdge.sender (by hSR)
              -- e.receiver = receiverEp.role = recvEdge.receiver
              have hSidEq : e.sid = recvEdge.sid := hSid1
              have hSenderEq : e.sender = recvEdge.sender := hRole1.trans hSR.symm
              have hRecvEq : e.receiver = recvEdge.receiver := hRole2
              -- Use decidable equality
              calc e = ⟨e.sid, e.sender, e.receiver⟩ := by rfl
                _ = ⟨recvEdge.sid, recvEdge.sender, recvEdge.receiver⟩ := by
                    simp only [hSidEq, hSenderEq, hRecvEq]
                _ = recvEdge := by rfl
            exact hEdgeEq
          · -- senderRole ≠ receiverEp.role
            -- But we're in self-loop case where e.sender = receiverEp.role
            -- hOrig has Consume receiverEp.role (.recv senderRole T L) (t::ts)
            -- For this to succeed, we need receiverEp.role == senderRole, which is false
            -- So hOrig simplifies to none.isSome = true, a contradiction
            have hBeq : (receiverEp.role == senderRole) = false := beq_eq_false_iff_ne.mpr (Ne.symm hSR)
            simp only [hBeq, Bool.false_and] at hOrig
            simp only [Option.isSome] at hOrig
            exact Bool.noConfusion hOrig
      · -- Sender endpoint = receiverEp, receiver endpoint ≠ receiverEp
        have hRecvNoMatch : receiverEp ≠ { sid := e.sid, role := e.receiver } := fun h => hRecvMatch h.symm
        apply EdgeCoherent_updateD_irrelevant _ _ _ _ _ hNeSymm
        simp only [EdgeCoherent]
        intro Lsender Lrecv hGsender hGrecv
        rw [lookupG_update_neq _ _ _ _ hRecvNoMatch] at hGrecv
        have hOrigCoh := hCoh e
        simp only [EdgeCoherent] at hOrigCoh
        have hSid : e.sid = receiverEp.sid := congrArg Endpoint.sid hSenderMatch
        have hRole : e.sender = receiverEp.role := congrArg Endpoint.role hSenderMatch
        have hOrigSender : lookupG G { sid := e.sid, role := e.sender } = some (.recv senderRole T L) := by
          conv => lhs; rw [hSid, hRole]; exact hG
        exact hOrigCoh (.recv senderRole T L) Lrecv hOrigSender hGrecv
    · -- Sender endpoint ≠ receiverEp
      have hSenderNoMatch : receiverEp ≠ { sid := e.sid, role := e.sender } := fun h => hSenderMatch h.symm
      by_cases hRecvMatch : { sid := e.sid, role := e.receiver : Endpoint } = receiverEp
      · -- Receiver endpoint = receiverEp, sender endpoint ≠ receiverEp
        apply EdgeCoherent_updateD_irrelevant _ _ _ _ _ hNeSymm
        simp only [EdgeCoherent]
        intro Lsender Lrecv hGsender hGrecv
        rw [lookupG_update_neq _ _ _ _ hSenderNoMatch] at hGsender
        have hSid : e.sid = receiverEp.sid := congrArg Endpoint.sid hRecvMatch
        have hRole : e.receiver = receiverEp.role := congrArg Endpoint.role hRecvMatch
        have hRecvLookup : lookupG (updateG G receiverEp L) { sid := e.sid, role := e.receiver } = some L := by
          conv => lhs; rw [hSid, hRole]; exact lookupG_update_eq G receiverEp L
        rw [hRecvLookup] at hGrecv
        simp only [Option.some.injEq] at hGrecv
        subst hGrecv
        -- Original coherence: receiver had .recv type
        have hOrigCoh := hCoh e
        simp only [EdgeCoherent] at hOrigCoh
        have hOrigRecv : lookupG G { sid := e.sid, role := e.receiver } = some (.recv senderRole T L) := by
          conv => lhs; rw [hSid, hRole]; exact hG
        have hOrig := hOrigCoh Lsender (.recv senderRole T L) hGsender hOrigRecv
        -- If e.sender = senderRole and trace head = T, then Consume succeeds after eating T
        -- Otherwise, trace must be empty for Consume on recv to work
        cases hTraceE : lookupD D e with
        | nil =>
          simp only [Consume, Option.isSome]
        | cons t ts =>
          simp only [hTraceE, Consume, consumeOne] at hOrig
          -- Analyze whether e.sender matches senderRole and T matches t
          by_cases hSenderEq : e.sender = senderRole
          · by_cases hTypeEq : T = t
            · simp only [hSenderEq, hTypeEq, beq_self_eq_true, Bool.and_self] at hOrig
              -- hOrig says Consume senderRole L ts is some
              -- But we need Consume e.sender L (t::ts)
              -- e.sender = senderRole, so Consume senderRole L (T::ts)
              -- L is the continuation after recv, so if L = .recv senderRole T' L', it consumes
              -- Otherwise, Consume L (T::ts) = none for send/end
              -- But we need (Consume e.sender L (t::ts)).isSome
              -- This depends on L. The original coherence gives us info about (.recv ...) consuming.
              -- After recv, L is the continuation. If L can't consume t::ts, we have a problem.
              -- Actually, the goal is just to show coherence at this edge in the NEW state.
              -- The new receiver type is L, trace is unchanged (e ≠ recvEdge).
              -- Original: Consume e.sender (.recv senderRole T L) (T::ts) = some L''
              -- After decomposition: Consume senderRole L ts = some L''
              -- But new goal: Consume e.sender L (T::ts)
              -- e.sender = senderRole, so: Consume senderRole L (T::ts)
              -- This is different from Consume senderRole L ts!
              -- Wait, this is the case where e ≠ recvEdge but e.receiver = receiverEp.
              -- The trace at e is NOT the recvEdge trace!
              -- The update to D is only at recvEdge, not at e.
              -- So we're checking coherence at e with:
              -- - Sender type: original (from G, not updated)
              -- - Receiver type: L (updated from .recv senderRole T L)
              -- - Trace: original (not updated since e ≠ recvEdge)
              -- We need: Consume e.sender L (original trace) succeeds
              -- But original coherence was for .recv type, not L type!
              -- This is the tricky case. The receiver's type changed, affecting coherence.
              -- Hmm, but e.sender might not be senderRole...
              -- Actually we're in the case where e.sender = senderRole.
              -- Original: Consume senderRole (.recv senderRole T L) (t::ts) = some L''
              -- where t = T (from hTypeEq)
              -- This gives: Consume senderRole L ts = some L''
              -- New: Consume senderRole L (T::ts) = ?
              -- These are different! New trace still has T at front, but type lost the recv.
              -- This means the new coherence might FAIL if L is not a recv for T!
              -- Actually wait, let me re-read. We're at edge e where:
              -- - e.receiver = receiverEp.role
              -- - e.sender ≠ receiverEp.role (so sender endpoint ≠ receiverEp)
              -- - e ≠ recvEdge
              -- recvEdge = {receiverEp.sid, senderRole, receiverEp.role}
              -- e has e.receiver = receiverEp.role
              -- For e ≠ recvEdge with same receiver, we need e.sender ≠ senderRole or e.sid ≠ receiverEp.sid
              -- But we're in the case hSenderEq : e.sender = senderRole!
              -- So for e ≠ recvEdge, we need e.sid ≠ receiverEp.sid.
              -- But hSid says e.sid = receiverEp.sid!
              -- Contradiction! If e.sender = senderRole, e.receiver = receiverEp.role, e.sid = receiverEp.sid,
              -- then e = recvEdge, contradicting heq.
              -- So this case is impossible.
              exfalso
              apply heq
              -- Prove e = recvEdge field by field
              have hEdgeEq : e = recvEdge := by
                have hSidEq : e.sid = recvEdge.sid := hSid
                have hSenderEqR : e.sender = recvEdge.sender := hSenderEq
                have hRecvEq : e.receiver = recvEdge.receiver := hRole
                calc e = ⟨e.sid, e.sender, e.receiver⟩ := by rfl
                  _ = ⟨recvEdge.sid, recvEdge.sender, recvEdge.receiver⟩ := by
                      simp only [hSidEq, hSenderEqR, hRecvEq]
                  _ = recvEdge := by rfl
              exact hEdgeEq
            · -- T ≠ t
              -- The Consume fails because the expected type T doesn't match t
              -- hOrig becomes none.isSome = true, a contradiction
              have hBeq : (T == t) = false := beq_eq_false_iff_ne.mpr hTypeEq
              -- Note: in Consume, we check (t == T), not (T == t)
              have hBeqComm : (t == T) = false := by
                have : t ≠ T := Ne.symm hTypeEq
                exact beq_eq_false_iff_ne.mpr this
              simp only [hSenderEq, beq_self_eq_true, Bool.true_and, hBeqComm] at hOrig
              simp only [Option.isSome] at hOrig
              exact Bool.noConfusion hOrig
          · -- e.sender ≠ senderRole
            -- The Consume on (.recv senderRole T L) fails because e.sender ≠ senderRole
            -- hOrig becomes none.isSome = true, a contradiction
            have hBeq : (e.sender == senderRole) = false := beq_eq_false_iff_ne.mpr hSenderEq
            simp only [hBeq, Bool.false_and] at hOrig
            simp only [Option.isSome] at hOrig
            exact Bool.noConfusion hOrig
      · -- Neither endpoint is receiverEp - completely unrelated edge
        have hRecvNoMatch : receiverEp ≠ { sid := e.sid, role := e.receiver } := fun h => hRecvMatch h.symm
        apply EdgeCoherent_updateD_irrelevant _ _ _ _ _ hNeSymm
        exact EdgeCoherent_updateG_irrelevant _ _ _ _ _ hSenderNoMatch hRecvNoMatch (hCoh e)

/-- Coherent is preserved when selecting (sending a label).
    Select appends .string to trace, advances selector type.
    Similar structure to Coherent_send_preserved. -/

end
