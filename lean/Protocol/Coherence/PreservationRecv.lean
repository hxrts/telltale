import Protocol.Coherence.StoreTyping
import Protocol.Coherence.Unified

/-! # Protocol.Coherence.PreservationRecv

Coherence preservation proof for recv steps.
-/

/-
The Problem. A recv step pops the head of one trace and advances the receiver
endpoint type. We must preserve `Coherent` through this coupled update.

Solution Structure.
1. Perform the same edge partition as in send preservation.
2. Rebuild coherence directly on the updated edge.
3. Use irrelevance lemmas on non-updated edges.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ## Coherence Recv Preservation -/
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
/-! ## Recv Preservation: Edge Case Analysis -/
theorem Coherent_recv_preserved
    (G : GEnv) (D : DEnv) (receiverEp : Endpoint) (senderRole : Role) (T : ValType) (L : LocalType)
    (hCoh : Coherent G D)
    (hG : lookupG G receiverEp = some (.recv senderRole T L))
    (hTrace : (lookupD D { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role }).head? = some T) :
    let e := { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role : Edge }
    Coherent (updateG G receiverEp L) (updateD D e (lookupD D e).tail) := by
  intro recvEdge e hActive  -- The edge we need to show coherence for
  have hActiveOrig : ActiveEdge G e :=
    ActiveEdge_updateG_inv (G:=G) (e:=e) (ep:=receiverEp) (L:=L) hActive (by simpa [hG])

  /-! ## Case 1: Updated Recv Edge -/
  -- Case split: updated edge / shares receiver endpoint / unrelated
  rcases edge_case_split e recvEdge receiverEp with heq | hShare | hOther
  · -- Case 1: e = recvEdge (the edge being modified)
    subst heq
    simp only [EdgeCoherent]
    intro Lrecv hGrecv
    -- For recvEdge: sender = senderRole, receiver = receiverEp.role
    -- Receiver endpoint lookup in updated G
    have hRecvLookup : lookupG (updateG G receiverEp L) { sid := receiverEp.sid, role := receiverEp.role } = some L := by
      convert lookupG_update_eq G receiverEp L
    /-! ## Case 1A: Updated Edge Self-Recv -/
    -- Check if sender = receiver (self-recv case)
    by_cases hSenderIsRecv : senderRole = receiverEp.role
    · -- Self-recv: sender role = receiver role
      subst hSenderIsRecv
      -- Receiver lookup gives L
      have hEq : Lrecv = L := by
        have : some L = some Lrecv := by
          simpa [hRecvLookup, recvEdge] using hGrecv
        exact (Option.some.inj this).symm
      have hSenderLookup : lookupG (updateG G receiverEp L) { sid := receiverEp.sid, role := receiverEp.role } = some L := by
        simpa using hRecvLookup
      refine ⟨L, hSenderLookup, ?_⟩
      simp only [lookupD_update_eq]
      -- Original coherence at this edge
      have hOrigCoh := Coherent_edge_any hCoh hActiveOrig
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
        have hOrig := EdgeCoherent_consume_of_receiver hOrigCoh hG
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
        simpa [hEq] using hOrig
    /-! ## Case 1B: Updated Edge Distinct Sender -/
    · -- Normal case: sender ≠ receiver
      have hSenderNeq : receiverEp ≠ { sid := receiverEp.sid, role := senderRole } := by
        intro h
        have : receiverEp.role = senderRole := congrArg Endpoint.role h
        exact hSenderIsRecv this.symm
      have hEq : Lrecv = L := by
        have : some L = some Lrecv := by
          simpa [hRecvLookup, recvEdge] using hGrecv
        exact (Option.some.inj this).symm
      simp only [lookupD_update_eq]
      -- Original coherence
      have hOrigCoh := Coherent_edge_any hCoh hActiveOrig
      -- Sender existence (unchanged by update)
      rcases EdgeCoherent_sender_of_receiver hOrigCoh hG with ⟨Lsender, hGsender⟩
      have hSenderLookup : lookupG (updateG G receiverEp L) { sid := receiverEp.sid, role := senderRole } = some Lsender := by
        simpa [lookupG_update_neq _ _ _ _ hSenderNeq] using hGsender
      refine ⟨Lsender, hSenderLookup, ?_⟩
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
        have hOrig := EdgeCoherent_consume_of_receiver hOrigCoh hG
        rw [hTraceVal] at hOrig
        simp only [Consume, consumeOne] at hOrig
        -- recvEdge.sender = senderRole, and after subst, t = T
        have hBeqRole : (recvEdge.sender == senderRole) = true := beq_self_eq_true _
        have hBeqType : (t == t) = true := beq_self_eq_true _
        simp only [hBeqRole, hBeqType, Bool.and_self, ite_true] at hOrig
        simp only [List.tail_cons]
        simpa [hEq] using hOrig
  /-! ## Case 2: Unchanged Edge Sharing Receiver Endpoint -/
  · -- Case 2: e ≠ recvEdge, but e shares receiverEp
    have hNeSymm : recvEdge ≠ e := Ne.symm hShare.1
    have hShare' : { sid := e.sid, role := e.sender : Endpoint } = receiverEp ∨
        { sid := e.sid, role := e.receiver : Endpoint } = receiverEp := by
      simpa [EdgeShares, senderEndpoint, receiverEndpoint] using hShare.2
    /-! ## Case 2A: Sender Endpoint Matches -/
    by_cases hSenderMatch : { sid := e.sid, role := e.sender : Endpoint } = receiverEp
    · -- Sender endpoint is receiverEp
      by_cases hRecvMatch : { sid := e.sid, role := e.receiver : Endpoint } = receiverEp
      · -- Both endpoints are receiverEp - self-loop case
        have hSid1 : e.sid = receiverEp.sid := congrArg Endpoint.sid hSenderMatch
        have hRole1 : e.sender = receiverEp.role := congrArg Endpoint.role hSenderMatch
        have hSid2 : e.sid = receiverEp.sid := congrArg Endpoint.sid hRecvMatch
        have hRole2 : e.receiver = receiverEp.role := congrArg Endpoint.role hRecvMatch
        simp only [EdgeCoherent]
        intro Lrecv hGrecv
        have hLookupS : lookupG (updateG G receiverEp L) { sid := e.sid, role := e.sender } = some L := by
          conv => lhs; rw [hSid1, hRole1]
          exact lookupG_update_eq G receiverEp L
        have hLookupR : lookupG (updateG G receiverEp L) { sid := e.sid, role := e.receiver } = some L := by
          conv => lhs; rw [hSid2, hRole2]
          exact lookupG_update_eq G receiverEp L
        have hEq : Lrecv = L := by
          have : some L = some Lrecv := by
            simpa [hLookupR] using hGrecv
          exact (Option.some.inj this).symm
        refine ⟨L, hLookupS, ?_⟩
        rw [lookupD_update_neq _ _ _ _ hNeSymm]
        -- Original coherence at e with receiver's original type .recv
        have hOrigCoh := Coherent_edge_any hCoh hActiveOrig
        have hOrigRecvG : lookupG G { sid := e.sid, role := e.receiver } = some (.recv senderRole T L) := by
          conv => lhs; rw [hSid2, hRole2]; exact hG
        have hOrig := EdgeCoherent_consume_of_receiver hOrigCoh hOrigRecvG
        cases hTraceE : lookupD D e with
        | nil =>
          rw [hRole1]
          simp only [Consume, Option.isSome]
        | cons t ts =>
          by_cases hSR : senderRole = receiverEp.role
          · -- Then e = recvEdge, contradicting hShare.1
            exfalso
            apply hShare.1
            have hEdgeEq : e = recvEdge := by
              have hSidEq : e.sid = recvEdge.sid := hSid1
              have hSenderEq : e.sender = recvEdge.sender := hRole1.trans hSR.symm
              have hRecvEq : e.receiver = recvEdge.receiver := hRole2
              calc e = ⟨e.sid, e.sender, e.receiver⟩ := by rfl
                _ = ⟨recvEdge.sid, recvEdge.sender, recvEdge.receiver⟩ := by
                    simp only [hSidEq, hSenderEq, hRecvEq]
                _ = recvEdge := by rfl
            exact hEdgeEq
          · -- senderRole ≠ receiverEp.role, so Consume on recv fails for non-empty trace
            have hBeqRole : (receiverEp.role == senderRole) = false := by
              exact beq_eq_false_iff_ne.mpr (Ne.symm hSR)
            rw [hRole1, hTraceE] at hOrig
            simp [Consume, consumeOne, hBeqRole] at hOrig
      /-! ## Case 2A(ii): Sender Matches, Receiver Distinct -/
      · -- Sender endpoint = receiverEp, receiver endpoint ≠ receiverEp
        have hRecvNoMatch : receiverEp ≠ { sid := e.sid, role := e.receiver } := fun h => hRecvMatch h.symm
        apply EdgeCoherent_updateD_irrelevant _ _ _ _ _ hNeSymm
        simp only [EdgeCoherent]
        intro Lrecv hGrecv
        have hGrecv' : lookupG G { sid := e.sid, role := e.receiver } = some Lrecv := by
          simpa [lookupG_update_neq _ _ _ _ hRecvNoMatch] using hGrecv
        have hOrigCoh := Coherent_edge_any hCoh hActiveOrig
        have hConsume := EdgeCoherent_consume_of_receiver hOrigCoh hGrecv'
        have hSid : e.sid = receiverEp.sid := congrArg Endpoint.sid hSenderMatch
        have hRole : e.sender = receiverEp.role := congrArg Endpoint.role hSenderMatch
        have hSenderLookup : lookupG (updateG G receiverEp L) { sid := e.sid, role := e.sender } = some L := by
          conv => lhs; rw [hSid, hRole]; exact lookupG_update_eq G receiverEp L
        refine ⟨L, hSenderLookup, hConsume⟩
    /-! ## Case 2B: Receiver Endpoint Matches -/
    · -- Sender endpoint ≠ receiverEp, so receiver must match
      have hSenderNoMatch : receiverEp ≠ { sid := e.sid, role := e.sender } := fun h => hSenderMatch h.symm
      have hRecvMatch : { sid := e.sid, role := e.receiver : Endpoint } = receiverEp := by
        cases hShare' with
        | inl h => exact (hSenderMatch h).elim
        | inr h => exact h
      apply EdgeCoherent_updateD_irrelevant _ _ _ _ _ hNeSymm
      simp only [EdgeCoherent]
      intro Lrecv hGrecv
      have hSid : e.sid = receiverEp.sid := congrArg Endpoint.sid hRecvMatch
      have hRole : e.receiver = receiverEp.role := congrArg Endpoint.role hRecvMatch
      have hRecvLookup : lookupG (updateG G receiverEp L) { sid := e.sid, role := e.receiver } = some L := by
        conv => lhs; rw [hSid, hRole]; exact lookupG_update_eq G receiverEp L
      have hEq : Lrecv = L := by
        have : some L = some Lrecv := by
          simpa [hRecvLookup] using hGrecv
        exact (Option.some.inj this).symm
      -- Original coherence: receiver had .recv type
      have hOrigCoh := Coherent_edge_any hCoh hActiveOrig
      have hOrigRecv : lookupG G { sid := e.sid, role := e.receiver } = some (.recv senderRole T L) := by
        conv => lhs; rw [hSid, hRole]; exact hG
      have hOrig := EdgeCoherent_consume_of_receiver hOrigCoh hOrigRecv
      rcases EdgeCoherent_sender_of_receiver hOrigCoh hOrigRecv with ⟨Lsender, hGsender⟩
      have hGsender' : lookupG (updateG G receiverEp L) { sid := e.sid, role := e.sender } = some Lsender := by
        simpa [lookupG_update_neq _ _ _ _ hSenderNoMatch] using hGsender
      refine ⟨Lsender, hGsender', ?_⟩
      cases hTraceE : lookupD D e with
      | nil =>
        simp only [Consume, Option.isSome]
      | cons t ts =>
        have hSenderNe : e.sender ≠ senderRole := by
          intro hEq
          apply hShare.1
          have hEdgeEq : e = recvEdge := by
            have hSidEq : e.sid = recvEdge.sid := hSid
            have hSenderEq : e.sender = recvEdge.sender := hEq
            have hRecvEq : e.receiver = recvEdge.receiver := hRole
            calc e = ⟨e.sid, e.sender, e.receiver⟩ := by rfl
              _ = ⟨recvEdge.sid, recvEdge.sender, recvEdge.receiver⟩ := by
                  simp only [hSidEq, hSenderEq, hRecvEq]
              _ = recvEdge := by rfl
          exact hEdgeEq
        have hBeq : (e.sender == senderRole) = false := beq_eq_false_iff_ne.mpr hSenderNe
        simp only [hTraceE, Consume, consumeOne, hBeq] at hOrig
        simp only [Option.isSome] at hOrig
        exfalso
        exact Bool.noConfusion hOrig
  /-! ## Case 3: Unrelated Edge -/
  · -- Case 3: e ≠ recvEdge and unrelated to receiverEp
    have hNeSymm : recvEdge ≠ e := Ne.symm hOther.1
    have hOther' :
        ¬ ({ sid := e.sid, role := e.sender : Endpoint } = receiverEp ∨
            { sid := e.sid, role := e.receiver : Endpoint } = receiverEp) := by
      simpa [EdgeShares, senderEndpoint, receiverEndpoint] using hOther.2
    have hSenderNoMatch : receiverEp ≠ { sid := e.sid, role := e.sender } := by
      intro h
      apply hOther'
      exact Or.inl h.symm
    have hRecvNoMatch : receiverEp ≠ { sid := e.sid, role := e.receiver } := by
      intro h
      apply hOther'
      exact Or.inr h.symm
    apply EdgeCoherent_updateD_irrelevant _ _ _ _ _ hNeSymm
    exact EdgeCoherent_updateG_irrelevant _ _ _ _ _ hSenderNoMatch hRecvNoMatch (Coherent_edge_any hCoh hActiveOrig)


end
