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

/-! ## ValidLabels Preservation Lemmas -/

/-- ValidLabels is preserved when sending.
    Send appends a value to the buffer, but ValidLabels checks branch labels
    which are only relevant when receiver has branch type.
    The main case (buffer head unchanged when appending) works.
    Edge cases (empty buffer, self-send, type changes) use sorry. -/
theorem ValidLabels_send_preserved
    (G : GEnv) (D : DEnv) (bufs : Buffers)
    (senderEp : Endpoint) (receiverRole : Role) (T : ValType) (L : LocalType) (v : Value)
    (hValid : ValidLabels G D bufs)
    (hG : lookupG G senderEp = some (.send receiverRole T L)) :
    let sendEdge := { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole : Edge }
    ValidLabels (updateG G senderEp L) (updateD D sendEdge (lookupD D sendEdge ++ [T]))
               (updateBuf bufs sendEdge (lookupBuf bufs sendEdge ++ [v])) := by
  -- ValidLabels checks buffer head against branch labels.
  -- Send appends to buffer END, so head unchanged for non-empty buffers.
  intro sendEdge e source bs hBranch
  -- Case split: is e the send edge or not?
  by_cases heq : e = sendEdge
  · -- e = sendEdge: buffer appends v at END
    subst heq
    -- Receiver endpoint for sendEdge is { sid := senderEp.sid, role := receiverRole }
    -- Check if this equals senderEp (self-send case)
    by_cases hSelf : senderEp = ⟨senderEp.sid, receiverRole⟩
    · -- Self-send case: senderEp.role = receiverRole
      sorry  -- Edge case: self-send
    · -- Normal case: receiver ≠ sender
      have hRecvNeq : senderEp ≠ ⟨sendEdge.sid, sendEdge.receiver⟩ := by
        simp only [sendEdge]; exact hSelf
      rw [lookupG_update_neq _ _ _ _ hRecvNeq] at hBranch
      rw [lookupBuf_update_eq]
      -- Original ValidLabels at sendEdge
      have hOrig := hValid sendEdge source bs hBranch
      -- Buffer was bufOld, now bufOld ++ [v]
      cases hBuf : lookupBuf bufs sendEdge with
      | nil =>
        simp only [List.nil_append]
        -- Empty buffer, now [v]. Check if v is .string with valid label
        cases v with
        | string l => sorry  -- Need: l ∈ bs (requires protocol consistency)
        | _ => trivial
      | cons h t =>
        simp only [List.cons_append]
        -- Buffer head unchanged, use original ValidLabels
        -- Match on h :: (t ++ [v]) has same result as h :: t since head is h
        cases h with
        | string l =>
          simp only [hBuf] at hOrig
          exact hOrig
        | _ => trivial
  · -- e ≠ sendEdge: buffer unchanged at e
    have hNeSymm : sendEdge ≠ e := Ne.symm heq
    rw [lookupBuf_update_neq _ _ _ _ hNeSymm]
    -- G might change at receiver endpoint
    by_cases hRecvEq : ⟨e.sid, e.receiver⟩ = senderEp
    · -- Receiver at e is senderEp, type changes from .send to L
      rw [← hRecvEq, lookupG_update_eq] at hBranch
      -- hBranch says L = .branch source bs, but L is continuation of send
      -- This is unusual unless L happens to be .branch
      sorry  -- Type consistency case
    · -- Receiver at e is not senderEp, G unchanged
      have hRecvNeq : senderEp ≠ ⟨e.sid, e.receiver⟩ := fun h => hRecvEq h.symm
      rw [lookupG_update_neq _ _ _ _ hRecvNeq] at hBranch
      exact hValid e source bs hBranch

/-- ValidLabels is preserved when receiving.
    Recv removes head from buffer. If the head was checked by ValidLabels,
    the remaining buffer still satisfies the property for the continuation type.
    The main case (buffer tail preservation) requires protocol consistency. -/
theorem ValidLabels_recv_preserved
    (G : GEnv) (D : DEnv) (bufs : Buffers)
    (receiverEp : Endpoint) (senderRole : Role) (T : ValType) (L : LocalType)
    (hValid : ValidLabels G D bufs)
    (hG : lookupG G receiverEp = some (.recv senderRole T L))
    (hTrace : (lookupD D { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role }).head? = some T) :
    let recvEdge := { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role : Edge }
    ValidLabels (updateG G receiverEp L) (updateD D recvEdge (lookupD D recvEdge).tail)
               (updateBuf bufs recvEdge (lookupBuf bufs recvEdge).tail) := by
  -- ValidLabels checks buffer head against branch labels.
  -- Recv removes buffer HEAD, so new head needs to match if continuation is branch.
  intro recvEdge e source bs hBranch
  by_cases heq : e = recvEdge
  · -- e = recvEdge: buffer becomes tail
    subst heq
    -- Receiver at recvEdge is receiverEp
    -- Check if receiverEp type changed (it did, from .recv to L)
    by_cases hSelf : senderRole = receiverEp.role
    · sorry  -- Edge case: self-recv
    · -- Normal case: sender ≠ receiver
      have hRecvEpEq : ⟨recvEdge.sid, recvEdge.receiver⟩ = receiverEp := rfl
      rw [hRecvEpEq, lookupG_update_eq] at hBranch
      -- hBranch : L = .branch source bs
      -- L is the continuation of recv, which could be branch
      rw [lookupBuf_update_eq]
      -- New buffer is tail of original
      cases hBuf : lookupBuf bufs recvEdge with
      | nil =>
        simp only [List.tail_nil]
        -- Empty buffer stays empty, goal is trivially True
      | cons h t =>
        simp only [List.tail_cons]
        -- New head is t.head (if t non-empty)
        cases t with
        | nil => trivial  -- Tail is empty
        | cons h' t' =>
          -- Need to show h' is valid for bs if h' is .string
          -- This requires protocol consistency from original ValidLabels
          -- The original ValidLabels was about h :: h' :: t', not h' :: t'
          sorry  -- Protocol consistency: new head valid for continuation
  · -- e ≠ recvEdge: buffer unchanged at e
    have hNeSymm : recvEdge ≠ e := Ne.symm heq
    rw [lookupBuf_update_neq _ _ _ _ hNeSymm]
    by_cases hRecvEq : ⟨e.sid, e.receiver⟩ = receiverEp
    · rw [← hRecvEq, lookupG_update_eq] at hBranch
      sorry  -- Type consistency: L = .branch case
    · have hRecvNeq : receiverEp ≠ ⟨e.sid, e.receiver⟩ := fun h => hRecvEq h.symm
      rw [lookupG_update_neq _ _ _ _ hRecvNeq] at hBranch
      exact hValid e source bs hBranch

/-- ValidLabels is preserved when selecting (sending a label).
    Select appends label to buffer END, so HEAD unchanged. -/
theorem ValidLabels_select_preserved
    (G : GEnv) (D : DEnv) (bufs : Buffers)
    (selectorEp : Endpoint) (targetRole : Role)
    (selectBranches : List (String × LocalType)) (ℓ : String) (L : LocalType)
    (hValid : ValidLabels G D bufs)
    (hG : lookupG G selectorEp = some (.select targetRole selectBranches))
    (hFind : selectBranches.find? (fun b => b.1 == ℓ) = some (ℓ, L)) :
    let selectEdge := { sid := selectorEp.sid, sender := selectorEp.role, receiver := targetRole : Edge }
    ValidLabels (updateG G selectorEp L) (updateD D selectEdge (lookupD D selectEdge ++ [.string]))
               (updateBuf bufs selectEdge (lookupBuf bufs selectEdge ++ [.string ℓ])) := by
  -- Same structure as ValidLabels_send_preserved
  intro selectEdge e source bs hBranch
  by_cases heq : e = selectEdge
  · -- e = selectEdge: buffer appends .string ℓ at END
    subst heq
    by_cases hSelf : selectorEp = ⟨selectorEp.sid, targetRole⟩
    · sorry  -- Edge case: self-select
    · -- Normal case: target ≠ selector
      have hRecvNeq : selectorEp ≠ ⟨selectEdge.sid, selectEdge.receiver⟩ := by
        simp only [selectEdge]; exact hSelf
      rw [lookupG_update_neq _ _ _ _ hRecvNeq] at hBranch
      rw [lookupBuf_update_eq]
      have hOrig := hValid selectEdge source bs hBranch
      cases hBuf : lookupBuf bufs selectEdge with
      | nil =>
        simp only [List.nil_append]
        -- Empty buffer, now [.string ℓ]. Need to check if ℓ ∈ bs
        -- This requires protocol consistency (select to branch matching)
        sorry
      | cons h t =>
        simp only [List.cons_append]
        cases h with
        | string l =>
          simp only [hBuf] at hOrig
          exact hOrig
        | _ => trivial
  · -- e ≠ selectEdge: buffer unchanged at e
    have hNeSymm : selectEdge ≠ e := Ne.symm heq
    rw [lookupBuf_update_neq _ _ _ _ hNeSymm]
    by_cases hRecvEq : ⟨e.sid, e.receiver⟩ = selectorEp
    · rw [← hRecvEq, lookupG_update_eq] at hBranch
      sorry  -- Type consistency case
    · have hRecvNeq : selectorEp ≠ ⟨e.sid, e.receiver⟩ := fun h => hRecvEq h.symm
      rw [lookupG_update_neq _ _ _ _ hRecvNeq] at hBranch
      exact hValid e source bs hBranch

/-- ValidLabels is preserved when branching (receiving a label).
    Branch removes label from buffer HEAD. -/
theorem ValidLabels_branch_preserved
    (G : GEnv) (D : DEnv) (bufs : Buffers)
    (brancherEp : Endpoint) (senderRole : Role)
    (branchOptions : List (String × LocalType)) (ℓ : String) (L : LocalType) (vs : List Value)
    (hValid : ValidLabels G D bufs)
    (hG : lookupG G brancherEp = some (.branch senderRole branchOptions))
    (hFind : branchOptions.find? (fun b => b.1 == ℓ) = some (ℓ, L))
    (hBufEq : lookupBuf bufs { sid := brancherEp.sid, sender := senderRole, receiver := brancherEp.role } = .string ℓ :: vs) :
    let branchEdge := { sid := brancherEp.sid, sender := senderRole, receiver := brancherEp.role : Edge }
    ValidLabels (updateG G brancherEp L) (updateD D branchEdge (lookupD D branchEdge).tail)
               (updateBuf bufs branchEdge vs) := by
  -- Same structure as ValidLabels_recv_preserved
  intro branchEdge e source bs hBranch
  by_cases heq : e = branchEdge
  · -- e = branchEdge: buffer becomes vs (tail of original)
    subst heq
    by_cases hSelf : senderRole = brancherEp.role
    · sorry  -- Edge case: self-branch
    · -- Normal case: sender ≠ receiver
      have hRecvEpEq : ⟨branchEdge.sid, branchEdge.receiver⟩ = brancherEp := rfl
      rw [hRecvEpEq, lookupG_update_eq] at hBranch
      -- hBranch : L = .branch source bs
      -- L is the continuation after branching
      rw [lookupBuf_update_eq]
      -- Buffer becomes vs
      cases vs with
      | nil => trivial  -- vs is empty
      | cons h' t' =>
        -- Need to show h' is valid for bs if h' is .string
        -- This requires protocol consistency
        sorry  -- Protocol consistency: continuation head valid
  · -- e ≠ branchEdge: buffer unchanged at e
    have hNeSymm : branchEdge ≠ e := Ne.symm heq
    rw [lookupBuf_update_neq _ _ _ _ hNeSymm]
    by_cases hRecvEq : ⟨e.sid, e.receiver⟩ = brancherEp
    · rw [← hRecvEq, lookupG_update_eq] at hBranch
      sorry  -- Type consistency: L = .branch case
    · have hRecvNeq : brancherEp ≠ ⟨e.sid, e.receiver⟩ := fun h => hRecvEq h.symm
      rw [lookupG_update_neq _ _ _ _ hRecvNeq] at hBranch
      exact hValid e source bs hBranch

/-- BuffersTyped is preserved when sending.
    Send appends v to buffer and T to trace at the send edge.
    For i < original length: buf[i] : trace[i] preserved.
    For i = original length: buf[i] = v, trace[i] = T, and hv : v : T. -/
theorem BuffersTyped_send_preserved
    (G : GEnv) (D : DEnv) (bufs : Buffers)
    (senderEp : Endpoint) (receiverRole : Role) (T : ValType) (L : LocalType) (v : Value)
    (hTyped : BuffersTyped G D bufs)
    (hv : HasTypeVal G v T)
    (hG : lookupG G senderEp = some (.send receiverRole T L)) :
    let sendEdge := { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole : Edge }
    BuffersTyped (updateG G senderEp L) (updateD D sendEdge (lookupD D sendEdge ++ [T]))
                 (updateBuf bufs sendEdge (lookupBuf bufs sendEdge ++ [v])) := by
  intro sendEdge e
  simp only [BufferTyped]
  by_cases he : e = sendEdge
  · -- e = sendEdge: buffer and trace both get appended
    -- For i < original length: use original typing with HasTypeVal_mono
    -- For i = original length: use hv for appended element
    -- Requires List.get_append_left/right lemmas for indexing
    sorry
  · -- e ≠ sendEdge: unchanged, use HasTypeVal_mono for GEnv update
    -- The mono case for e' = senderEp is tricky: channel values in buffer
    -- shouldn't reference the endpoint being updated (separate sessions).
    -- This requires additional invariants; use sorry for now.
    sorry

/-- BuffersTyped is preserved when receiving.
    Recv removes head from buffer and trace at the recv edge.
    For all i: buf'[i] = buf[i+1], trace'[i] = trace[i+1], preserved from original. -/
theorem BuffersTyped_recv_preserved
    (G : GEnv) (D : DEnv) (bufs : Buffers)
    (receiverEp : Endpoint) (senderRole : Role) (T : ValType) (L : LocalType) (v : Value) (vs : List Value)
    (hTyped : BuffersTyped G D bufs)
    (hBuf : lookupBuf bufs { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role } = v :: vs)
    (hv : HasTypeVal G v T)
    (hG : lookupG G receiverEp = some (.recv senderRole T L)) :
    let recvEdge := { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role : Edge }
    BuffersTyped (updateG G receiverEp L) (updateD D recvEdge (lookupD D recvEdge).tail)
                 (updateBuf bufs recvEdge vs) := by
  intro recvEdge e
  simp only [BufferTyped]
  by_cases he : e = recvEdge
  · -- e = recvEdge: buffer becomes vs, trace loses head
    -- Tail indexing: buf'[i] = buf[i+1], trace'[i] = trace[i+1]
    -- Original typing gives buf[i+1] : trace[i+1], need HasTypeVal_mono for G update
    sorry
  · -- e ≠ recvEdge: unchanged, use HasTypeVal_mono for GEnv update
    -- The mono case for e' = receiverEp is tricky: channel values in buffer
    -- shouldn't reference the endpoint being updated (separate sessions).
    -- This requires additional invariants; use sorry for now.
    sorry

/-- BuffersTyped is preserved when selecting (sending a label).
    Select appends label string to buffer and .string to trace.
    Similar to send but with label type. -/
theorem BuffersTyped_select_preserved
    (G : GEnv) (D : DEnv) (bufs : Buffers)
    (selectorEp : Endpoint) (targetRole : Role)
    (bs : List (String × LocalType)) (ℓ : String) (L : LocalType)
    (hTyped : BuffersTyped G D bufs)
    (hG : lookupG G selectorEp = some (.select targetRole bs))
    (hFind : bs.find? (fun b => b.1 == ℓ) = some (ℓ, L)) :
    let selectEdge := { sid := selectorEp.sid, sender := selectorEp.role, receiver := targetRole : Edge }
    BuffersTyped (updateG G selectorEp L) (updateD D selectEdge (lookupD D selectEdge ++ [.string]))
                 (updateBuf bufs selectEdge (lookupBuf bufs selectEdge ++ [.string ℓ])) := by
  intro selectEdge e
  simp only [BufferTyped]
  by_cases he : e = selectEdge
  · -- e = selectEdge: buffer and trace both get appended with label
    -- For i < original length: use original typing with HasTypeVal_mono
    -- For i = original length: .string ℓ : .string by HasTypeVal.string
    -- Requires List.get_append_left/right lemmas
    sorry
  · -- e ≠ selectEdge: unchanged, use HasTypeVal_mono for GEnv update
    sorry

/-- BuffersTyped is preserved when branching (receiving a label).
    Branch removes label string from buffer HEAD and .string from trace HEAD.
    Similar to recv but with label type. -/
theorem BuffersTyped_branch_preserved
    (G : GEnv) (D : DEnv) (bufs : Buffers)
    (brancherEp : Endpoint) (senderRole : Role)
    (bs : List (String × LocalType)) (ℓ : String) (L : LocalType) (vs : List Value)
    (hTyped : BuffersTyped G D bufs)
    (hBuf : lookupBuf bufs { sid := brancherEp.sid, sender := senderRole, receiver := brancherEp.role } = .string ℓ :: vs)
    (hG : lookupG G brancherEp = some (.branch senderRole bs))
    (hFind : bs.find? (fun b => b.1 == ℓ) = some (ℓ, L)) :
    let branchEdge := { sid := brancherEp.sid, sender := senderRole, receiver := brancherEp.role : Edge }
    BuffersTyped (updateG G brancherEp L) (updateD D branchEdge (lookupD D branchEdge).tail)
                 (updateBuf bufs branchEdge vs) := by
  intro branchEdge e
  simp only [BufferTyped]
  by_cases he : e = branchEdge
  · -- e = branchEdge: buffer becomes vs, trace loses head
    -- Tail indexing: buf'[i] = buf[i+1], trace'[i] = trace[i+1]
    -- Original typing gives buf[i+1] : trace[i+1], need HasTypeVal_mono for G update
    sorry
  · -- e ≠ branchEdge: unchanged, use HasTypeVal_mono for GEnv update
    sorry

/-! ## Initialization Lemma -/

/-- Empty environments are coherent. -/
theorem Coherent_empty : Coherent [] Lean.RBMap.empty := by
  intro e Lsender Lrecv hGsender hGrecv
  -- lookupG [] _ = none for any endpoint
  unfold lookupG at hGsender
  simp only [List.lookup] at hGsender
  -- hGsender : none = some Lsender is a contradiction
  exact (Option.some_ne_none Lsender hGsender.symm).elim

/-- Initialize coherent environments for a new session with local types. -/
def initSession (sid : SessionId) (roles : RoleSet) (localTypes : Role → LocalType) :
    GEnv × DEnv × Buffers :=
  let G := roles.map fun r => ({ sid := sid, role := r }, localTypes r)
  let D := initDEnv sid roles
  let bufs := initBuffers sid roles
  (G, D, bufs)

/-- Initialized session environments are coherent (when types are projections). -/
theorem initSession_coherent (sid : SessionId) (roles : RoleSet) (localTypes : Role → LocalType)
    (hProj : True)  -- Placeholder for "localTypes are valid projections"
    : let (G, D, _) := initSession sid roles localTypes
      Coherent G D := by
  sorry  -- Requires projection coherence


end
