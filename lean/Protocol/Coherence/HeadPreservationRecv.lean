import Protocol.Coherence.EdgeCoherence

/-! # Protocol.Coherence.HeadPreservationRecv

Head-coherence preservation for recv steps, including recv-specific consume helpers.
-/

/-
The Problem. Receiving consumes the trace head and advances the receiver's local
type. We must show `HeadCoherent` is preserved for the updated environments.

Solution Structure.
1. Prove recv-specific `Consume` helper lemmas.
2. Do the standard edge split (updated edge vs unrelated edge).
3. Use coherence facts to align consumed trace heads with recv expectations.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ## HeadCoherent Recv Preservation -/
private theorem Consume_tail_of_self_recv
    {from_ : Role} {T : ValType} {L : LocalType} {ts : List ValType} :
    (Consume from_ (.recv from_ T L) (T :: ts)).isSome →
    (Consume from_ L ts).isSome := by
  -- Reduce Consume on a matching recv head to Consume on the tail.
  intro hConsume
  simpa [Consume, consumeOne, beq_self_eq_true, Bool.true_and] using hConsume

/-- Helper: If Consume succeeds on a recv head, the head type matches. -/
private theorem Consume_head_eq_of_recv
    {from_ r : Role} {T : ValType} {L : LocalType} {t : ValType} {ts : List ValType} :
    (Consume from_ (.recv r T L) (t :: ts)).isSome → t = T := by
  -- Extract a witness and apply the recv-head matching lemma.
  intro hConsume
  rcases (Option.isSome_iff_exists).1 hConsume with ⟨L', hEq⟩
  exact (Consume_recv_head_match (from_:=from_) (r:=r) (T:=T) (L:=L) (t:=t) (ts:=ts) hEq).2

/-- Helper: Consume on a branch with a non-empty trace is impossible. -/
private theorem Consume_branch_nonempty_isSome_false
    {from_ r : Role} {bs : List (String × LocalType)} {t : ValType} {ts : List ValType} :
    (Consume from_ (.branch r bs) (t :: ts)).isSome → False := by
  -- Turn isSome into an equality and use the existing contradiction lemma.
  intro hConsume
  rcases (Option.isSome_iff_exists).1 hConsume with ⟨L', hEq⟩
  exact Consume_branch_nonempty_false (from_:=from_) (r:=r) (bs:=bs) (t:=t) (ts:=ts) (L':=L') hEq

/-! ## Main Recv Preservation Theorem -/

/-- HeadCoherent is preserved when receiving.
    Recv action removes trace HEAD, and receiver type advances from recv to continuation.
    The key insight is that Coherent implies the continuation can consume the remaining trace,
    which means the new head (if any) must match the continuation's expected recv type.
    Reference: `work/effects/004.lean` proof structure -/
theorem HeadCoherent_recv_preserved
    (G : GEnv) (D : DEnv) (receiverEp : Endpoint) (senderRole : Role) (Trecv : ValType)
    (L : LocalType)
    (hHead : HeadCoherent G D)
    (hCoh : Coherent G D)
    (hG : lookupG G receiverEp = some (.recv senderRole Trecv L))
    (hTrace : (lookupD D { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role }).head? =
      some Trecv) :
    let e := { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role : Edge }
    HeadCoherent (updateG G receiverEp L) (updateD D e (lookupD D e).tail) := by
  intro recvEdge e hActive  -- The edge we check HeadCoherent for
  simp only [HeadCoherent] at hHead ⊢
  have hActiveOrig : ActiveEdge G e :=
    ActiveEdge_updateG_inv (G:=G) (e:=e) (ep:=receiverEp) (L:=L) hActive (by simp [hG])
  -- Case split: is e the recv edge or not?
  by_cases heq : e = recvEdge
  · -- Case 1: e = recvEdge - type and trace both change
    subst heq
    -- Updated-edge subcase: self-recv vs distinct sender/receiver
    by_cases hSenderIsRecv : senderRole = receiverEp.role
    · -- Self-recv: senderRole = receiverEp.role, sender/receiver endpoints coincide.
      subst hSenderIsRecv
      have hRecvLookup : lookupG (updateG G receiverEp L) receiverEp = some L := by
        simpa using (lookupG_update_eq G receiverEp L)
      rw [hRecvLookup, lookupD_update_eq]
      cases hTraceVal : lookupD D recvEdge with
      | nil =>
          cases L <;> simp
      | cons t ts =>
          rw [hTraceVal] at hTrace
          have hHeadEq : t = Trecv := by
            simpa [List.head?] using hTrace
          simp [List.tail_cons]
          have hActiveRecv : ActiveEdge G recvEdge := by
            have hSender : lookupG G { sid := recvEdge.sid, role := recvEdge.sender } =
                some (.recv receiverEp.role Trecv L) := by
              simpa [recvEdge] using hG
            have hRecv : lookupG G { sid := recvEdge.sid, role := recvEdge.receiver } =
                some (.recv receiverEp.role Trecv L) := by
              simpa [recvEdge] using hG
            exact ActiveEdge_of_endpoints hSender hRecv
          have hEdgeCoh : EdgeCoherent G D recvEdge := Coherent_edge_any hCoh hActiveRecv
          have hRecvLookup' :
              lookupG G ⟨recvEdge.sid, recvEdge.receiver⟩ = some (.recv receiverEp.role Trecv L) := by
            simpa [recvEdge] using hG
          have hConsumeRaw :
              (Consume receiverEp.role (.recv receiverEp.role Trecv L) (t :: ts)).isSome := by
            obtain ⟨Ls, _hSender, hConsume⟩ := hEdgeCoh (.recv receiverEp.role Trecv L) hRecvLookup'
            simpa [recvEdge, hTraceVal] using hConsume
          have hConsume :
              (Consume receiverEp.role (.recv receiverEp.role Trecv L) (Trecv :: ts)).isSome := by
            simpa [hHeadEq] using hConsumeRaw
          have hConsumeTail : (Consume receiverEp.role L ts).isSome :=
            Consume_tail_of_self_recv (from_:=receiverEp.role) (T:=Trecv) (L:=L) (ts:=ts) hConsume
          cases hL : L with
          | end_ => trivial
          | send _ _ _ => trivial
          | select _ _ => trivial
          | var _ => trivial
          | mu _ => trivial
          | recv r T' L' =>
              cases ts with
              | nil => trivial
              | cons t' ts' =>
                  have hConsume' :
                      (Consume receiverEp.role (.recv r T' L') (t' :: ts')).isSome := by
                    simpa [hL] using hConsumeTail
                  have hHeadEq :=
                    Consume_head_eq_of_recv
                      (from_:=receiverEp.role) (r:=r) (T:=T') (L:=L') (t:=t') (ts:=ts') hConsume'
                  exact hHeadEq.symm
          | branch source bs =>
              cases ts with
              | nil => trivial
              | cons t' ts' =>
                  have hConsume' :
                      (Consume receiverEp.role (.branch source bs) (t' :: ts')).isSome := by
                    simpa [hL] using hConsumeTail
                  exact (Consume_branch_nonempty_isSome_false
                    (from_:=receiverEp.role) (r:=source) (bs:=bs) (t:=t') (ts:=ts') hConsume').elim
    · -- Distinct sender/receiver
      have hSenderNeq : receiverEp ≠ { sid := receiverEp.sid, role := senderRole } := by
        intro h
        exact hSenderIsRecv (congrArg Endpoint.role h).symm
      have hRecvLookup :
          lookupG (updateG G receiverEp L) { sid := receiverEp.sid, role := receiverEp.role } = some L := by
        convert lookupG_update_eq G receiverEp L
      rw [hRecvLookup, lookupD_update_eq]
      cases hTraceVal : lookupD D recvEdge with
      | nil =>
          rw [hTraceVal] at hTrace
          simp only [List.head?] at hTrace
          exact Option.noConfusion hTrace
      | cons t ts =>
          rw [hTraceVal] at hTrace
          simp only [List.head?, Option.some.injEq] at hTrace
          have hHeadEq : t = Trecv := hTrace
          simp only [List.tail_cons]
          cases hL : L with
          | end_ => trivial
          | send _ _ _ => trivial
          | select _ _ => trivial
          | var _ => trivial
          | mu _ => trivial
          | recv r T' L' =>
              cases ts with
              | nil => trivial
              | cons t' ts' =>
                  have hEdgeCoh : EdgeCoherent G D recvEdge := Coherent_edge_any hCoh hActiveOrig
                  have hG' : lookupG G receiverEp = some (.recv senderRole t L) := by
                    simpa [hHeadEq] using hG
                  have hConsumeFull :
                      (Consume senderRole (.recv senderRole t L) (t :: t' :: ts')).isSome := by
                    obtain ⟨Ls, _hSender, hConsume⟩ := hEdgeCoh (.recv senderRole t L) hG'
                    simpa [hTraceVal] using hConsume
                  have hConsumeTail :
                      (Consume senderRole L (t' :: ts')).isSome := by
                    simpa [Consume_recv_cons] using hConsumeFull
                  have hHeadEq :=
                    Consume_head_eq_of_recv
                      (from_:=senderRole) (r:=r) (T:=T') (L:=L') (t:=t') (ts:=ts') (by
                        simpa [hL] using hConsumeTail)
                  exact hHeadEq.symm
          | branch source bs =>
              cases ts with
              | nil => trivial
              | cons t' ts' =>
                  have hEdgeCoh : EdgeCoherent G D recvEdge := Coherent_edge_any hCoh hActiveOrig
                  have hG' : lookupG G receiverEp = some (.recv senderRole t L) := by
                    simpa [hHeadEq] using hG
                  have hConsumeFull :
                      (Consume senderRole (.recv senderRole t L) (t :: t' :: ts')).isSome := by
                    obtain ⟨Ls, _hSender, hConsume⟩ := hEdgeCoh (.recv senderRole t L) hG'
                    simpa [hTraceVal] using hConsume
                  have hConsumeTail :
                      (Consume senderRole L (t' :: ts')).isSome := by
                    simpa [Consume_recv_cons] using hConsumeFull
                  have hConsume' :
                      (Consume senderRole (.branch source bs) (t' :: ts')).isSome := by
                    simpa [hL] using hConsumeTail
                  exact (Consume_branch_nonempty_isSome_false
                    (from_:=senderRole) (r:=source) (bs:=bs) (t:=t') (ts:=ts') hConsume').elim
  · -- Case 2: e ≠ recvEdge
    by_cases hRecvMatch : { sid := e.sid, role := e.receiver : Endpoint } = receiverEp
    · -- Receiver endpoint is receiverEp, type changed from .recv to L
      subst hRecvMatch
      rw [lookupG_update_eq]
      have hNeSymm : recvEdge ≠ e := Ne.symm heq
      rw [lookupD_update_neq _ _ _ _ hNeSymm]
      cases hL : L with
      | end_ => trivial
      | send _ _ _ => trivial
      | select _ _ => trivial
      | var _ => trivial
      | mu _ => trivial
      | recv r T' L' =>
          have hEdgeCoh : EdgeCoherent G D e := Coherent_edge_any hCoh hActiveOrig
          have hRecvType' : lookupG G ⟨e.sid, e.receiver⟩ = some (.recv senderRole Trecv L) := by
            simp only [hG]
          have hSenderNe : e.sender ≠ senderRole := by
            intro hEq
            apply heq
            have hEdgeEq : e = recvEdge := by
              have hSidEq : e.sid = recvEdge.sid := rfl
              have hSenderEq : e.sender = recvEdge.sender := hEq
              have hRecvEq : e.receiver = recvEdge.receiver := rfl
              calc e = ⟨e.sid, e.sender, e.receiver⟩ := by rfl
                _ = ⟨recvEdge.sid, recvEdge.sender, recvEdge.receiver⟩ := by
                    simp only [hSidEq, hSenderEq, hRecvEq]
                _ = recvEdge := by rfl
            exact hEdgeEq
          have hTraceEmpty := trace_empty_when_recv_other_sender hEdgeCoh hRecvType' hSenderNe
          rw [hTraceEmpty]
          trivial
      | branch source bs' =>
          have hEdgeCoh : EdgeCoherent G D e := Coherent_edge_any hCoh hActiveOrig
          have hRecvType' : lookupG G ⟨e.sid, e.receiver⟩ = some (.recv senderRole Trecv L) := by
            simp only [hG]
          have hSenderNe : e.sender ≠ senderRole := by
            intro hEq
            apply heq
            have hEdgeEq : e = recvEdge := by
              have hSidEq : e.sid = recvEdge.sid := rfl
              have hSenderEq : e.sender = recvEdge.sender := hEq
              have hRecvEq : e.receiver = recvEdge.receiver := rfl
              calc e = ⟨e.sid, e.sender, e.receiver⟩ := by rfl
                _ = ⟨recvEdge.sid, recvEdge.sender, recvEdge.receiver⟩ := by
                    simp only [hSidEq, hSenderEq, hRecvEq]
                _ = recvEdge := by rfl
            exact hEdgeEq
          have hTraceEmpty := trace_empty_when_recv_other_sender hEdgeCoh hRecvType' hSenderNe
          rw [hTraceEmpty]
          trivial
    · -- Receiver endpoint unchanged
      have hRecvNoMatch : receiverEp ≠ { sid := e.sid, role := e.receiver } := fun h => hRecvMatch h.symm
      rw [lookupG_update_neq _ _ _ _ hRecvNoMatch]
      have hNeSymm : recvEdge ≠ e := Ne.symm heq
      rw [lookupD_update_neq _ _ _ _ hNeSymm]
      exact hHead e hActiveOrig

end
