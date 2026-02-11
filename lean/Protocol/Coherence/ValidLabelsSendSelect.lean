import Protocol.Coherence.EdgeCoherence
import Protocol.Coherence.Preservation
import Protocol.Coherence.SelectPreservation

/-! # Protocol.Coherence.ValidLabelsSendSelect

ValidLabels preservation lemmas for send/select transitions.
-/

/-
The Problem. Show label validity is preserved for message and label send-side updates.

Solution Structure. Prove edge-case analyses for send/select buffer updates and endpoint changes.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical
section

/-! ## ValidLabels Preservation Lemmas -/

/-- ValidLabels is preserved when sending.
    Send appends a value to the buffer, but ValidLabels checks branch labels
    which are only relevant when receiver has branch type.
    Self-send and branch-receiver cases are ruled out by `hRecvReady`. -/
theorem ValidLabels_send_preserved
    (G : GEnv) (D : DEnv) (bufs : Buffers)
    (senderEp : Endpoint) (receiverRole : Role) (T : ValType) (L : LocalType) (v : Value)
    (hValid : ValidLabels G D bufs)
    (hCoh : Coherent G D)
    (hBT : BuffersTyped G D bufs)
    (hG : lookupG G senderEp = some (.send receiverRole T L))
    (hRecvReady : ∀ Lrecv, lookupG G { sid := senderEp.sid, role := receiverRole } = some Lrecv →
      ∃ L', Consume senderEp.role Lrecv (lookupD D { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole }) = some L' ∧
            (Consume senderEp.role L' [T]).isSome) :
    let sendEdge := { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole : Edge }
    ValidLabels (updateG G senderEp L) (updateD D sendEdge (lookupD D sendEdge ++ [T]))
               (updateBuf bufs sendEdge (lookupBuf bufs sendEdge ++ [v])) := by
  intro sendEdge e source bs hActive hBranch
  let recvEp : Endpoint := { sid := e.sid, role := e.receiver }
  have hActiveOrig : ActiveEdge G e :=
    ActiveEdge_updateG_inv (G:=G) (e:=e) (ep:=senderEp) (L:=L) hActive (by simpa [hG])
  by_cases hRecvEq : recvEp = senderEp
  · -- Receiver is the updated endpoint: original type is .send, so buffers must be empty.
    have hNoSelf : receiverRole ≠ senderEp.role := by
      intro hEq
      subst hEq
      obtain ⟨L', hConsume, hConsumeT⟩ := hRecvReady (.send senderEp.role T L) hG
      cases hTrace : lookupD D { sid := senderEp.sid, sender := senderEp.role, receiver := senderEp.role } with
      | nil =>
          rw [hTrace] at hConsume
          simp only [Consume] at hConsume
          have hL' : L' = .send senderEp.role T L := Option.some.inj hConsume.symm
          rw [hL'] at hConsumeT
          simp only [Consume, consumeOne, Option.isSome] at hConsumeT
          exact Bool.noConfusion hConsumeT
      | cons t ts =>
          rw [hTrace] at hConsume
          simp only [Consume, consumeOne] at hConsume
          exact Option.noConfusion hConsume
    have hSend : lookupG G recvEp = some (.send receiverRole T L) := by
      simpa [hRecvEq] using hG
    have hTraceEmpty : lookupD D e = [] :=
      trace_empty_when_send_receiver (Coherent_edge_any hCoh hActiveOrig) hSend
    have hBufEmpty : lookupBuf bufs e = [] := by
      rcases hBT e with ⟨hLen, _⟩
      cases hBuf : lookupBuf bufs e with
      | nil => rfl
      | cons v' vs =>
          have hLen' : Nat.succ vs.length = 0 := by
            simpa [hTraceEmpty, hBuf] using hLen
          exact (False.elim (Nat.succ_ne_zero _ hLen'))
    have hNe : e ≠ sendEdge := by
      intro hEq
      subst hEq
      have hRecvRole : receiverRole = senderEp.role := by
        have h' := congrArg Endpoint.role hRecvEq
        simpa [recvEp] using h'
      exact hNoSelf hRecvRole
    have hBufEq :
        lookupBuf (updateBuf bufs sendEdge (lookupBuf bufs sendEdge ++ [v])) e =
          lookupBuf bufs e := by
      exact lookupBuf_update_neq _ _ _ _ (Ne.symm hNe)
    have hBuf' :
        lookupBuf (updateBuf bufs sendEdge (lookupBuf bufs sendEdge ++ [v])) e = [] := by
      simpa [hBufEq, hBufEmpty]
    simp [hBuf']
  · -- Receiver endpoint unchanged: use original ValidLabels and buffer update facts.
    have hBranchOld : lookupG G recvEp = some (.branch source bs) := by
      have hBranch' := hBranch
      rw [lookupG_update_neq G senderEp recvEp L (Ne.symm hRecvEq)] at hBranch'
      exact hBranch'
    by_cases hEdge : e = sendEdge
    · -- If receiver is branch at sendEdge, hRecvReady is inconsistent.
      subst hEdge
      obtain ⟨L', hConsume, hConsumeT⟩ := hRecvReady (.branch source bs) hBranchOld
      cases hTrace : lookupD D sendEdge with
      | nil =>
          rw [hTrace] at hConsume
          simp only [Consume] at hConsume
          have hL' : L' = .branch source bs := Option.some.inj hConsume.symm
          rw [hL'] at hConsumeT
          simp only [Consume, consumeOne, Option.isSome] at hConsumeT
          exact (False.elim (Bool.noConfusion hConsumeT))
      | cons t ts =>
          rw [hTrace] at hConsume
          simp only [Consume, consumeOne] at hConsume
          exact (False.elim (Option.noConfusion hConsume))
    · -- Edge unaffected: buffer unchanged, use old ValidLabels.
      have hBufEq :
          lookupBuf (updateBuf bufs sendEdge (lookupBuf bufs sendEdge ++ [v])) e =
            lookupBuf bufs e := by
        exact lookupBuf_update_neq _ _ _ _ (Ne.symm hEdge)
      have hValidOld := hValid e source bs hActiveOrig hBranchOld
      simpa [hBufEq] using hValidOld

/-- ValidLabels is preserved when selecting (sending a label).
    Select appends label to buffer END, so HEAD unchanged.
    Self-select and branch-receiver cases are ruled out by `hRecvReady`. -/
theorem ValidLabels_select_preserved
    (G : GEnv) (D : DEnv) (bufs : Buffers)
    (selectorEp : Endpoint) (targetRole : Role)
    (selectBranches : List (String × LocalType)) (ℓ : String) (L : LocalType)
    (hValid : ValidLabels G D bufs)
    (hCoh : Coherent G D)
    (hBT : BuffersTyped G D bufs)
    (hG : lookupG G selectorEp = some (.select targetRole selectBranches))
    (_hFind : selectBranches.find? (fun b => b.1 == ℓ) = some (ℓ, L))
    (hRecvReady : ∀ Lrecv, lookupG G { sid := selectorEp.sid, role := targetRole } = some Lrecv →
      ∃ L', Consume selectorEp.role Lrecv (lookupD D { sid := selectorEp.sid, sender := selectorEp.role, receiver := targetRole }) = some L' ∧
            (Consume selectorEp.role L' [.string]).isSome) :
    let selectEdge := { sid := selectorEp.sid, sender := selectorEp.role, receiver := targetRole : Edge }
    ValidLabels (updateG G selectorEp L) (updateD D selectEdge (lookupD D selectEdge ++ [.string]))
               (updateBuf bufs selectEdge (lookupBuf bufs selectEdge ++ [.string ℓ])) := by
  intro selectEdge e source bs hActive hBranch
  let recvEp : Endpoint := { sid := e.sid, role := e.receiver }
  have hActiveOrig : ActiveEdge G e :=
    ActiveEdge_updateG_inv (G:=G) (e:=e) (ep:=selectorEp) (L:=L) hActive (by simpa [hG])
  by_cases hRecvEq : recvEp = selectorEp
  · -- Receiver is the updated endpoint: original type is .select, so buffers must be empty.
    have hNoSelf : targetRole ≠ selectorEp.role := by
      intro hEq
      subst hEq
      obtain ⟨L', hConsume, hConsumeT⟩ := hRecvReady (.select selectorEp.role selectBranches) hG
      cases hTrace : lookupD D { sid := selectorEp.sid, sender := selectorEp.role, receiver := selectorEp.role } with
      | nil =>
          rw [hTrace] at hConsume
          simp only [Consume] at hConsume
          have hL' : L' = .select selectorEp.role selectBranches := Option.some.inj hConsume.symm
          rw [hL'] at hConsumeT
          simp only [Consume, consumeOne, Option.isSome] at hConsumeT
          exact Bool.noConfusion hConsumeT
      | cons t ts =>
          rw [hTrace] at hConsume
          simp only [Consume, consumeOne] at hConsume
          exact Option.noConfusion hConsume
    have hSelect : lookupG G recvEp = some (.select targetRole selectBranches) := by
      simpa [hRecvEq] using hG
    have hTraceEmpty : lookupD D e = [] :=
      trace_empty_when_select_receiver (Coherent_edge_any hCoh hActiveOrig) hSelect
    have hBufEmpty : lookupBuf bufs e = [] := by
      rcases hBT e with ⟨hLen, _⟩
      cases hBuf : lookupBuf bufs e with
      | nil => rfl
      | cons v' vs =>
          have hLen' : Nat.succ vs.length = 0 := by
            simpa [hTraceEmpty, hBuf] using hLen
          exact (False.elim (Nat.succ_ne_zero _ hLen'))
    have hNe : e ≠ selectEdge := by
      intro hEq
      subst hEq
      have hRecvRole : targetRole = selectorEp.role := by
        have h' := congrArg Endpoint.role hRecvEq
        simpa [recvEp] using h'
      exact hNoSelf hRecvRole
    have hBufEq :
        lookupBuf (updateBuf bufs selectEdge (lookupBuf bufs selectEdge ++ [.string ℓ])) e =
          lookupBuf bufs e := by
      exact lookupBuf_update_neq _ _ _ _ (Ne.symm hNe)
    have hBuf' :
        lookupBuf (updateBuf bufs selectEdge (lookupBuf bufs selectEdge ++ [.string ℓ])) e = [] := by
      simpa [hBufEq, hBufEmpty]
    simp [hBuf']
  · -- Receiver endpoint unchanged: use original ValidLabels and buffer update facts.
    have hBranchOld : lookupG G recvEp = some (.branch source bs) := by
      have hBranch' := hBranch
      rw [lookupG_update_neq G selectorEp recvEp L (Ne.symm hRecvEq)] at hBranch'
      exact hBranch'
    by_cases hEdge : e = selectEdge
    · -- If receiver is branch at selectEdge, hRecvReady is inconsistent.
      subst hEdge
      obtain ⟨L', hConsume, hConsumeT⟩ := hRecvReady (.branch source bs) hBranchOld
      cases hTrace : lookupD D selectEdge with
      | nil =>
          rw [hTrace] at hConsume
          simp only [Consume] at hConsume
          have hL' : L' = .branch source bs := Option.some.inj hConsume.symm
          rw [hL'] at hConsumeT
          simp only [Consume, consumeOne, Option.isSome] at hConsumeT
          exact (False.elim (Bool.noConfusion hConsumeT))
      | cons t ts =>
          rw [hTrace] at hConsume
          simp only [Consume, consumeOne] at hConsume
          exact (False.elim (Option.noConfusion hConsume))
    · -- Edge unaffected: buffer unchanged, use old ValidLabels.
      have hBufEq :
          lookupBuf (updateBuf bufs selectEdge (lookupBuf bufs selectEdge ++ [.string ℓ])) e =
            lookupBuf bufs e := by
        exact lookupBuf_update_neq _ _ _ _ (Ne.symm hEdge)
      have hValidOld := hValid e source bs hActiveOrig hBranchOld
      simpa [hBufEq] using hValidOld


end
