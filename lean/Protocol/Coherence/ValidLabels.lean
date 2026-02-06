import Protocol.Coherence.EdgeCoherence
import Protocol.Coherence.Preservation
import Protocol.Coherence.SelectPreservation

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

/-! ## Buffer Typing Preservation Helpers -/

private theorem trace_empty_when_branch_receiver
    {G : GEnv} {D : DEnv} {e : Edge}
    {r : Role} {bs : List (String × LocalType)}
    (hCoh : EdgeCoherent G D e)
    (hBranch : lookupG G ⟨e.sid, e.receiver⟩ = some (.branch r bs)) :
    lookupD D e = [] := by
  simp only [EdgeCoherent] at hCoh
  obtain ⟨Ls, _hLsender, hIsSome⟩ := hCoh (.branch r bs) hBranch
  cases hTrace : lookupD D e with
  | nil => rfl
  | cons t ts =>
      rw [hTrace] at hIsSome
      simp only [Consume, consumeOne] at hIsSome
      exact Bool.noConfusion hIsSome

private theorem buffer_empty_of_typed_trace_empty
    {G : GEnv} {D : DEnv} {bufs : Buffers} {e : Edge}
    (hBT : BuffersTyped G D bufs)
    (hTrace : lookupD D e = []) :
    lookupBuf bufs e = [] := by
  rcases hBT e with ⟨hLen, _⟩
  cases hBuf : lookupBuf bufs e with
  | nil => rfl
  | cons v vs =>
      have hLen' : Nat.succ vs.length = 0 := by
        simpa [hTrace, hBuf] using hLen
      exact (False.elim (Nat.succ_ne_zero _ hLen'))

private theorem HasTypeVal_updateG_weaken {G : GEnv} {ep : Endpoint} {Lnew : LocalType}
    {v : Value} {T : ValType} :
    HasTypeVal G v T →
    HasTypeVal (updateG G ep Lnew) v T := by
  intro hv
  cases hv with
  | unit => exact HasTypeVal.unit
  | bool b => exact HasTypeVal.bool b
  | nat n => exact HasTypeVal.nat n
  | string s => exact HasTypeVal.string s
  | prod h₁ h₂ =>
    exact HasTypeVal.prod (HasTypeVal_updateG_weaken h₁) (HasTypeVal_updateG_weaken h₂)
  | chan h =>
    rename_i e' L'
    by_cases heq : e' = ep
    · subst heq
      apply HasTypeVal.chan
      exact lookupG_update_eq G e' Lnew
    · apply HasTypeVal.chan
      rw [lookupG_update_neq G ep e' Lnew (Ne.symm heq)]
      exact h

private theorem BuffersTyped_updateG_weaken {G : GEnv} {D : DEnv} {bufs : Buffers}
    {e : Endpoint} {L : LocalType} :
    BuffersTyped G D bufs →
    BuffersTyped (updateG G e L) D bufs := by
  intro hBT a
  rcases hBT a with ⟨hLen, hTyping⟩
  refine ⟨hLen, ?_⟩
  intro i hi
  exact HasTypeVal_updateG_weaken (hTyping i hi)

private theorem BuffersTyped_enqueue_local {G : GEnv} {D : DEnv} {bufs : Buffers}
    {e : Edge} {v : Value} {T : ValType}
    (hBT : BuffersTyped G D bufs)
    (hv : HasTypeVal G v T) :
    BuffersTyped G (updateD D e (lookupD D e ++ [T])) (enqueueBuf bufs e v) := by
  intro a
  unfold BufferTyped
  by_cases ha : a = e
  · -- a = e: the edge we're enqueuing on
    have hOrig := hBT e
    unfold BufferTyped at hOrig
    obtain ⟨hLen, hTyping⟩ := hOrig
    subst ha
    simp only [enqueueBuf, lookupBuf_update_eq, lookupD_update_eq]
    have hNewLen : (lookupBuf bufs a ++ [v]).length = (lookupD D a ++ [T]).length := by
      simp [List.length_append]
      omega
    refine ⟨hNewLen, ?_⟩
    intro i hi
    by_cases hOld : i < (lookupBuf bufs a).length
    · -- i < old length: use original typing
      have hTrace : i < (lookupD D a).length := hLen ▸ hOld
      have hiTrace : i < (lookupD D a ++ [T]).length := by
        simpa [hNewLen] using hi
      have hBufGet : (lookupBuf bufs a ++ [v])[i] = (lookupBuf bufs a)[i] := by
        exact List.getElem_append_left (as := lookupBuf bufs a) (bs := [v]) hOld (h' := hi)
      have hTraceGet : (lookupD D a ++ [T])[i] = (lookupD D a)[i] := by
        exact List.getElem_append_left (as := lookupD D a) (bs := [T]) hTrace (h' := hiTrace)
      have hGoal : HasTypeVal G (lookupBuf bufs a)[i] (lookupD D a)[i] := by
        convert hTyping i hOld using 2
      have hGoal' : HasTypeVal G (lookupBuf bufs a ++ [v])[i] (lookupD D a ++ [T])[i] := by
        simpa [hBufGet, hTraceGet] using hGoal
      simpa [lookupBuf_update_eq, lookupD_update_eq] using hGoal'
    · -- i = old length: the newly added element
      have hLe : (lookupBuf bufs a).length ≤ i := Nat.le_of_not_lt hOld
      have hLe' : i ≤ (lookupBuf bufs a).length := by
        have hi' : i < (lookupBuf bufs a).length + 1 := by
          have hi' := hi
          simp [List.length_append] at hi'
          exact hi'
        exact Nat.le_of_lt_succ hi'
      have hEq : i = (lookupBuf bufs a).length := Nat.le_antisymm hLe' hLe
      have hTraceEq : i = (lookupD D a).length := hLen ▸ hEq
      have hiTrace : i < (lookupD D a ++ [T]).length := by
        simpa [hNewLen] using hi
      have hBufGet : (lookupBuf bufs a ++ [v])[i] = v := by
        have hLe : (lookupBuf bufs a).length ≤ i := by simpa [hEq]
        simpa [hEq] using
          (List.getElem_append_right (as := lookupBuf bufs a) (bs := [v]) (i := i) hLe (h₂ := hi))
      have hTraceGet : (lookupD D a ++ [T])[i] = T := by
        have hLe : (lookupD D a).length ≤ i := by simpa [hTraceEq]
        simpa [hTraceEq] using
          (List.getElem_append_right (as := lookupD D a) (bs := [T]) (i := i) hLe (h₂ := hiTrace))
      have hGoal' : HasTypeVal G (lookupBuf bufs a ++ [v])[i] (lookupD D a ++ [T])[i] := by
        simpa [hBufGet, hTraceGet] using hv
      simpa [lookupBuf_update_eq, lookupD_update_eq] using hGoal'
  · -- a ≠ e: unaffected edge
    have hOrig := hBT a
    have hBufEq : lookupBuf (updateBuf bufs e (lookupBuf bufs e ++ [v])) a = lookupBuf bufs a := by
      exact lookupBuf_update_neq _ _ _ _ (Ne.symm ha)
    have hTraceEq : lookupD (updateD D e (lookupD D e ++ [T])) a = lookupD D a := by
      exact lookupD_update_neq _ _ _ _ (Ne.symm ha)
    simpa [BufferTyped, hBufEq, hTraceEq, enqueueBuf] using hOrig

private theorem BuffersTyped_dequeue_local {G : GEnv} {D : DEnv} {bufs : Buffers}
    {recvEdge : Edge} {v : Value} {vs : List Value} {T : ValType} :
    BuffersTyped G D bufs →
    lookupBuf bufs recvEdge = v :: vs →
    (lookupD D recvEdge).head? = some T →
    BuffersTyped G (updateD D recvEdge (lookupD D recvEdge).tail) (updateBuf bufs recvEdge vs) := by
  intro hBT hBuf hHead a
  unfold BufferTyped
  by_cases ha : a = recvEdge
  · subst a
    have hOrig := hBT recvEdge
    unfold BufferTyped at hOrig
    obtain ⟨hLen, hTyping⟩ := hOrig
    cases hTrace : lookupD D recvEdge with
    | nil =>
        simp [hTrace] at hHead
    | cons t ts =>
        have hT : t = T := by
          simpa [hTrace] using hHead
        have hLen' : vs.length = ts.length := by
          simpa [hBuf, hTrace] using hLen
        have hBufEq : lookupBuf (updateBuf bufs recvEdge vs) recvEdge = vs := by
          exact lookupBuf_update_eq _ _ _
        have hTraceEq :
            lookupD (updateD D recvEdge (lookupD D recvEdge).tail) recvEdge = ts := by
          simp [lookupD_update_eq, hTrace]
        refine ⟨?_, ?_⟩
        · simp [lookupBuf_update_eq, lookupD_update_eq, hLen']
        · intro i hi
          have hi' : i < vs.length := by
            simpa [hBufEq] using hi
          have hi_succ : i + 1 < (lookupBuf bufs recvEdge).length := by
            have h' : i + 1 < vs.length + 1 := Nat.succ_lt_succ hi'
            simpa [hBuf, List.length_cons] using h'
          have hTypedIdx := hTyping (i + 1) hi_succ
          have hTypedIdx' : HasTypeVal G vs[i] ts[i] := by
            simpa [List.get_eq_getElem, hBuf, hTrace, List.getElem_cons_succ] using hTypedIdx
          simpa [hBufEq, lookupD_update_eq] using hTypedIdx'
  · -- a ≠ recvEdge: unaffected edge
    have hOrig := hBT a
    have hBufEq : lookupBuf (updateBuf bufs recvEdge vs) a = lookupBuf bufs a := by
      exact lookupBuf_update_neq _ _ _ _ (Ne.symm ha)
    have hTraceEq :
        lookupD (updateD D recvEdge (lookupD D recvEdge).tail) a = lookupD D a := by
      exact lookupD_update_neq _ _ _ _ (Ne.symm ha)
    simpa [BufferTyped, hBufEq, hTraceEq] using hOrig

/-- BuffersTyped is preserved when sending.
    Send appends v to buffer and T to trace at the send edge.
    For i < original length: buf[i] : trace[i] preserved.
    For i = original length: buf[i] = v, trace[i] = T, and hv : v : T. -/
theorem BuffersTyped_send_preserved
    (G : GEnv) (D : DEnv) (bufs : Buffers)
    (senderEp : Endpoint) (receiverRole : Role) (T : ValType) (L : LocalType) (v : Value)
    (hTyped : BuffersTyped G D bufs)
    (hv : HasTypeVal G v T)
    (_hG : lookupG G senderEp = some (.send receiverRole T L)) :
    let sendEdge := { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole : Edge }
    BuffersTyped (updateG G senderEp L) (updateD D sendEdge (lookupD D sendEdge ++ [T]))
                 (updateBuf bufs sendEdge (lookupBuf bufs sendEdge ++ [v])) := by
  intro sendEdge
  have hBT' :
      BuffersTyped G (updateD D sendEdge (lookupD D sendEdge ++ [T]))
        (enqueueBuf bufs sendEdge v) :=
    BuffersTyped_enqueue_local (G:=G) (D:=D) (bufs:=bufs) (e:=sendEdge) (v:=v) (T:=T) hTyped hv
  have hBT'' :
      BuffersTyped (updateG G senderEp L) (updateD D sendEdge (lookupD D sendEdge ++ [T]))
        (enqueueBuf bufs sendEdge v) :=
    BuffersTyped_updateG_weaken (e:=senderEp) (L:=L) hBT'
  simpa [enqueueBuf] using hBT''

/-- BuffersTyped is preserved when receiving.
    Recv removes head from buffer and trace at the recv edge.
    For all i: buf'[i] = buf[i+1], trace'[i] = trace[i+1], preserved from original. -/
theorem BuffersTyped_recv_preserved
    (G : GEnv) (D : DEnv) (bufs : Buffers)
    (receiverEp : Endpoint) (senderRole : Role) (T : ValType) (L : LocalType) (v : Value) (vs : List Value)
    (hTyped : BuffersTyped G D bufs)
    (hBuf : lookupBuf bufs { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role } = v :: vs)
    (hv : HasTypeVal G v T)
    (_hG : lookupG G receiverEp = some (.recv senderRole T L)) :
    let recvEdge := { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role : Edge }
    BuffersTyped (updateG G receiverEp L) (updateD D recvEdge (lookupD D recvEdge).tail)
                 (updateBuf bufs recvEdge vs) := by
  intro recvEdge
  have hTypedEdge := hTyped recvEdge
  have hTrace : (lookupD D recvEdge).head? = some T :=
    trace_head_from_buffer hBuf hv hTypedEdge
  have hBT' :
      BuffersTyped G (updateD D recvEdge (lookupD D recvEdge).tail)
        (updateBuf bufs recvEdge vs) :=
    BuffersTyped_dequeue_local (G:=G) (D:=D) (bufs:=bufs) (recvEdge:=recvEdge) (v:=v) (vs:=vs) (T:=T)
      hTyped hBuf hTrace
  have hBT'' :
      BuffersTyped (updateG G receiverEp L) (updateD D recvEdge (lookupD D recvEdge).tail)
        (updateBuf bufs recvEdge vs) :=
    BuffersTyped_updateG_weaken (e:=receiverEp) (L:=L) hBT'
  exact hBT''

/-- BuffersTyped is preserved when selecting (sending a label).
    Select appends label string to buffer and .string to trace.
    Similar to send but with label type. -/
theorem BuffersTyped_select_preserved
    (G : GEnv) (D : DEnv) (bufs : Buffers)
    (selectorEp : Endpoint) (targetRole : Role)
    (bs : List (String × LocalType)) (ℓ : String) (L : LocalType)
    (hTyped : BuffersTyped G D bufs)
    (_hG : lookupG G selectorEp = some (.select targetRole bs))
    (_hFind : bs.find? (fun b => b.1 == ℓ) = some (ℓ, L)) :
    let selectEdge := { sid := selectorEp.sid, sender := selectorEp.role, receiver := targetRole : Edge }
    BuffersTyped (updateG G selectorEp L) (updateD D selectEdge (lookupD D selectEdge ++ [.string]))
                 (updateBuf bufs selectEdge (lookupBuf bufs selectEdge ++ [.string ℓ])) := by
  intro selectEdge
  have hv : HasTypeVal G (.string ℓ) .string := HasTypeVal.string ℓ
  have hBT' :
      BuffersTyped G (updateD D selectEdge (lookupD D selectEdge ++ [.string]))
        (enqueueBuf bufs selectEdge (.string ℓ)) :=
    BuffersTyped_enqueue_local (G:=G) (D:=D) (bufs:=bufs) (e:=selectEdge) (v:=.string ℓ) (T:=.string)
      hTyped hv
  have hBT'' :
      BuffersTyped (updateG G selectorEp L) (updateD D selectEdge (lookupD D selectEdge ++ [.string]))
        (enqueueBuf bufs selectEdge (.string ℓ)) :=
    BuffersTyped_updateG_weaken (e:=selectorEp) (L:=L) hBT'
  simpa [enqueueBuf] using hBT''

/-- BuffersTyped is preserved when branching (receiving a label).
    Branch removes label string from buffer HEAD and .string from trace HEAD.
    Similar to recv but with label type. -/
theorem BuffersTyped_branch_preserved
    (G : GEnv) (D : DEnv) (bufs : Buffers)
    (brancherEp : Endpoint) (senderRole : Role)
    (bs : List (String × LocalType)) (ℓ : String) (L : LocalType) (vs : List Value)
    (hTyped : BuffersTyped G D bufs)
    (hBuf : lookupBuf bufs { sid := brancherEp.sid, sender := senderRole, receiver := brancherEp.role } = .string ℓ :: vs)
    (_hG : lookupG G brancherEp = some (.branch senderRole bs))
    (_hFind : bs.find? (fun b => b.1 == ℓ) = some (ℓ, L)) :
    let branchEdge := { sid := brancherEp.sid, sender := senderRole, receiver := brancherEp.role : Edge }
    BuffersTyped (updateG G brancherEp L) (updateD D branchEdge (lookupD D branchEdge).tail)
                 (updateBuf bufs branchEdge vs) := by
  intro branchEdge
  have hv : HasTypeVal G (.string ℓ) .string := HasTypeVal.string ℓ
  have hTypedEdge := hTyped branchEdge
  have hTrace : (lookupD D branchEdge).head? = some .string :=
    trace_head_from_buffer hBuf hv hTypedEdge
  have hBT' :
      BuffersTyped G (updateD D branchEdge (lookupD D branchEdge).tail)
        (updateBuf bufs branchEdge vs) :=
    BuffersTyped_dequeue_local (G:=G) (D:=D) (bufs:=bufs) (recvEdge:=branchEdge) (v:=.string ℓ) (vs:=vs) (T:=.string)
      hTyped hBuf hTrace
  have hBT'' :
      BuffersTyped (updateG G brancherEp L) (updateD D branchEdge (lookupD D branchEdge).tail)
        (updateBuf bufs branchEdge vs) :=
    BuffersTyped_updateG_weaken (e:=brancherEp) (L:=L) hBT'
  exact hBT''

/-! ## ValidLabels Preservation (recv/branch) -/

theorem ValidLabels_recv_preserved
    (G : GEnv) (D : DEnv) (bufs : Buffers)
    (receiverEp : Endpoint) (senderRole : Role) (T : ValType) (L : LocalType)
    (v : Value) (vs : List Value)
    (hValid : ValidLabels G D bufs)
    (hCoh : Coherent G D)
    (hBT : BuffersTyped G D bufs)
    (hBuf : lookupBuf bufs { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role } = v :: vs)
    (hv : HasTypeVal G v T)
    (hG : lookupG G receiverEp = some (.recv senderRole T L)) :
    let recvEdge := { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role : Edge }
    ValidLabels (updateG G receiverEp L) (updateD D recvEdge (lookupD D recvEdge).tail)
               (updateBuf bufs recvEdge vs) := by
  intro recvEdge e source bs hActive hBranch
  let recvEp : Endpoint := { sid := e.sid, role := e.receiver }
  have hActiveOrig : ActiveEdge G e :=
    ActiveEdge_updateG_inv (G:=G) (e:=e) (ep:=receiverEp) (L:=L) hActive (by simpa [hG])
  have hTypedEdge := hBT recvEdge
  have hTrace : (lookupD D recvEdge).head? = some T :=
    trace_head_from_buffer hBuf hv hTypedEdge
  have hCoh' := Coherent_recv_preserved G D receiverEp senderRole T L hCoh hG hTrace
  have hBT' :=
    BuffersTyped_recv_preserved G D bufs receiverEp senderRole T L v vs hBT hBuf hv hG
  by_cases hRecvEq : recvEp = receiverEp
  · -- Receiver is the updated endpoint; if L is branch, traces must be empty.
    have hTraceEmpty : lookupD (updateD D recvEdge (lookupD D recvEdge).tail) e = [] :=
      trace_empty_when_branch_receiver (Coherent_edge_any hCoh' hActive) hBranch
    have hBufEmpty : lookupBuf (updateBuf bufs recvEdge vs) e = [] :=
      buffer_empty_of_typed_trace_empty hBT' hTraceEmpty
    simp [hBufEmpty]
  · -- Receiver endpoint unchanged: use original ValidLabels.
    have hBranchOld : lookupG G recvEp = some (.branch source bs) := by
      have hBranch' := hBranch
      rw [lookupG_update_neq G receiverEp recvEp L (Ne.symm hRecvEq)] at hBranch'
      exact hBranch'
    have hNe : e ≠ recvEdge := by
      intro hEq
      apply hRecvEq
      subst hEq
      rfl
    have hBufEq : lookupBuf (updateBuf bufs recvEdge vs) e = lookupBuf bufs e := by
      exact lookupBuf_update_neq _ _ _ _ (Ne.symm hNe)
    have hValidOld := hValid e source bs hActiveOrig hBranchOld
    simpa [hBufEq] using hValidOld

theorem ValidLabels_branch_preserved
    (G : GEnv) (D : DEnv) (bufs : Buffers)
    (brancherEp : Endpoint) (senderRole : Role)
    (branchOptions : List (String × LocalType)) (ℓ : String) (L : LocalType) (vs : List Value)
    (hValid : ValidLabels G D bufs)
    (hCoh : Coherent G D)
    (hBT : BuffersTyped G D bufs)
    (hG : lookupG G brancherEp = some (.branch senderRole branchOptions))
    (hFind : branchOptions.find? (fun b => b.1 == ℓ) = some (ℓ, L))
    (hBufEq : lookupBuf bufs { sid := brancherEp.sid, sender := senderRole, receiver := brancherEp.role } = .string ℓ :: vs) :
    let branchEdge := { sid := brancherEp.sid, sender := senderRole, receiver := brancherEp.role : Edge }
    ValidLabels (updateG G brancherEp L) (updateD D branchEdge (lookupD D branchEdge).tail)
               (updateBuf bufs branchEdge vs) := by
  intro branchEdge e source bs hActive hBranch
  let recvEp : Endpoint := { sid := e.sid, role := e.receiver }
  have hActiveOrig : ActiveEdge G e :=
    ActiveEdge_updateG_inv (G:=G) (e:=e) (ep:=brancherEp) (L:=L) hActive (by simpa [hG])
  have hv : HasTypeVal G (.string ℓ) .string := HasTypeVal.string ℓ
  have hTypedEdge := hBT branchEdge
  have hTrace : (lookupD D branchEdge).head? = some .string :=
    trace_head_from_buffer hBufEq hv hTypedEdge
  have hCoh' := Coherent_branch_preserved G D brancherEp senderRole branchOptions ℓ L hCoh hG hFind hTrace
  have hBT' :=
    BuffersTyped_branch_preserved G D bufs brancherEp senderRole branchOptions ℓ L vs hBT hBufEq hG hFind
  by_cases hRecvEq : recvEp = brancherEp
  · -- Receiver is the updated endpoint; if L is branch, traces must be empty.
    have hTraceEmpty : lookupD (updateD D branchEdge (lookupD D branchEdge).tail) e = [] :=
      trace_empty_when_branch_receiver (Coherent_edge_any hCoh' hActive) hBranch
    have hBufEmpty : lookupBuf (updateBuf bufs branchEdge vs) e = [] :=
      buffer_empty_of_typed_trace_empty hBT' hTraceEmpty
    simp [hBufEmpty]
  · -- Receiver endpoint unchanged: use original ValidLabels.
    have hBranchOld : lookupG G recvEp = some (.branch source bs) := by
      have hBranch' := hBranch
      rw [lookupG_update_neq G brancherEp recvEp L (Ne.symm hRecvEq)] at hBranch'
      exact hBranch'
    have hNe : e ≠ branchEdge := by
      intro hEq
      apply hRecvEq
      subst hEq
      rfl
    have hBufEq' : lookupBuf (updateBuf bufs branchEdge vs) e = lookupBuf bufs e := by
      exact lookupBuf_update_neq _ _ _ _ (Ne.symm hNe)
    have hValidOld := hValid e source bs hActiveOrig hBranchOld
    simpa [hBufEq'] using hValidOld

/-! ## Initialization Lemma -/

/-- Empty environments are coherent. -/
theorem Coherent_empty : Coherent [] (∅ : DEnv) := by
  intro e hActive
  -- No receiver exists in the empty environment
  have : False := by
    simp [ActiveEdge, lookupG] at hActive
  exact (False.elim this)

/-- Initialize coherent environments for a new session with local types. -/
def initSession (sid : SessionId) (roles : RoleSet) (localTypes : Role → LocalType) :
    GEnv × DEnv × Buffers :=
  let G := roles.map fun r => ({ sid := sid, role := r }, localTypes r)
  let D := initDEnv sid roles
  let bufs := initBuffers sid roles
  (G, D, bufs)

/-- Initialized session environments are coherent (when types are projections). -/
theorem initSession_coherent (sid : SessionId) (roles : RoleSet) (localTypes : Role → LocalType)
    (_hProj : True)  -- Placeholder for "localTypes are valid projections"
    (hSenders :
      ∀ (e : Edge) (Lrecv : LocalType),
        lookupG (roles.map fun r => ({ sid := sid, role := r }, localTypes r))
          { sid := e.sid, role := e.receiver } = some Lrecv →
        ∃ Lsender,
          lookupG (roles.map fun r => ({ sid := sid, role := r }, localTypes r))
            { sid := e.sid, role := e.sender } = some Lsender)
    : let (G, D, _) := initSession sid roles localTypes
      Coherent G D := by
  -- Buffers/traces are initialized empty for all edges, so Consume always succeeds.
  simp [initSession, Coherent, EdgeCoherent]
  intro e hActive Lrecv hGrecv
  rcases hSenders e Lrecv hGrecv with ⟨Lsender, hGsender⟩
  refine ⟨?_, ?_⟩
  · exact ⟨Lsender, hGsender⟩
  -- All traces are empty in initDEnv.
  have hTrace : lookupD (initDEnv sid roles) e = [] := by
    by_cases hMem : e ∈ RoleSet.allEdges sid roles
    · exact initDEnv_lookup_mem sid roles e hMem
    · have hFind : (initDEnv sid roles).find? e = none :=
        initDEnv_find?_none_of_notin sid roles e hMem
      simp [lookupD, hFind]
  -- Consume with empty trace always succeeds.
  simp [hTrace, Consume]


end
