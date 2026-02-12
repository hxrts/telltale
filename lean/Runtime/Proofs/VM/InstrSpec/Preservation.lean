import Runtime.VM.Semantics.InstrSpec
import Protocol.Coherence.EdgeCoherence
import Protocol.Coherence.Preservation
import Protocol.Coherence.SelectPreservation
import Protocol.Coherence.ConfigEquiv
import Protocol.Coherence.Delegation

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # VM Instruction Specification Proofs

Preservation theorems connecting VM instruction specs to Protocol-level coherence. -/

/-
The Problem. VM instructions (send, recv, select, branch, delegate) must preserve
the Protocol coherence invariant. Each instruction has a spec defining pre/post
conditions that need to be connected to the coherence preservation theorems.

Solution Structure. For each instruction type, defines a preservation theorem
(e.g., `SendSpec_preserves_Coherent`) that extracts preconditions from the spec
and applies the corresponding Protocol-level preservation lemma. Uses SendReady,
buffer head evidence, and label matching to satisfy preconditions.
-/

open scoped Classical

section

/-! ## Preservation Theorems -/

/-- Send preserves Coherence when SendReady holds.

    The proof extracts the sender type from the spec and constructs the
    receiver-readiness evidence required by `Coherent_send_preserved`. -/
theorem SendSpec_preserves_Coherent {G G' : GEnv} {D D' : DEnv}
    {senderEp : Endpoint} {receiverRole : Role} {T : ValType}
    (hSpec : SendSpec G G' D D' senderEp receiverRole T)
    (hCoh : Coherent G D)
    (hReady : SendReady G D) :
    Coherent G' D' := by
  -- Extract sender type from spec
  obtain ⟨L', hSenderType⟩ := hSpec.sender_type
  -- SendReady gives us the receiver readiness condition
  have hRecvReady : ∀ Lrecv, lookupG G { sid := senderEp.sid, role := receiverRole } = some Lrecv →
      ∃ L'', Consume senderEp.role Lrecv
        (lookupD D { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole }) = some L'' ∧
        (Consume senderEp.role L'' [T]).isSome := by
    intro Lrecv hLrecv
    exact hReady senderEp receiverRole T L' hSenderType Lrecv hLrecv
  -- The spec tells us G' and D' are the result of the update
  -- Apply Protocol-level preservation
  have hResult := Coherent_send_preserved G D senderEp receiverRole T L' hCoh hSenderType hRecvReady
  -- Need to show G' = updateG G senderEp L' and D' = updateD D edge (trace ++ [T])
  have hGUpdate : G' = updateG G senderEp L' := hSpec.type_updated L' hSenderType
  rw [hGUpdate, hSpec.trace_extended]
  exact hResult

/-! ## Receive Preservation -/

/-- Receive preserves Coherence.

    The proof uses the buffer head evidence from the spec to satisfy
    the precondition of `Coherent_recv_preserved`. -/
theorem RecvSpec_preserves_Coherent {G G' : GEnv} {D D' : DEnv}
    {receiverEp : Endpoint} {senderRole : Role} {T : ValType}
    (hSpec : RecvSpec G G' D D' receiverEp senderRole T)
    (hCoh : Coherent G D) :
    Coherent G' D' := by
  -- Extract receiver type and buffer data from spec
  obtain ⟨L', hRecvType⟩ := hSpec.receiver_type
  obtain ⟨rest, hBuffer⟩ := hSpec.buffer_has_data
  -- Construct the trace head evidence
  let edge : Edge := { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role }
  have hTraceHead : (lookupD D edge).head? = some T := by
    simp only [edge, hBuffer, List.head?_cons]
  -- Apply Protocol-level preservation
  have hResult := Coherent_recv_preserved G D receiverEp senderRole T L' hCoh hRecvType hTraceHead
  -- The spec tells us G' and D' are the result of the update
  have hGUpdate : G' = updateG G receiverEp L' := hSpec.type_updated L' hRecvType
  obtain ⟨rest', hTraceEq, hDUpdate⟩ := hSpec.trace_consumed
  -- Show rest = rest' (both come from the same buffer)
  have hRestEq : rest = rest' := by
    have h1 : T :: rest = lookupD D edge := hBuffer.symm
    have h2 : T :: rest' = lookupD D edge := hTraceEq.symm
    have h3 : T :: rest = T :: rest' := h1.trans h2.symm
    exact List.tail_eq_of_cons_eq h3
  rw [hGUpdate, hDUpdate, ← hRestEq]
  -- Align the trace tail with `rest`
  simpa [edge, hBuffer, List.tail_cons] using hResult

/-! ## Select/Branch Preservation -/

/-- Select preserves Coherence when SelectReady holds.

    Similar to send, but uses SelectReady for the receiver's ability
    to accept a label message. -/
theorem SelectSpec_preserves_Coherent {G G' : GEnv} {D D' : DEnv}
    {senderEp : Endpoint} {receiverRole : Role} {chosen : Label}
    (hSpec : SelectSpec G G' D D' senderEp receiverRole chosen)
    (hCoh : Coherent G D)
    (hReady : SelectReady G D) :
    Coherent G' D' := by
  -- Extract sender type from spec
  obtain ⟨branches, L', hSenderType, hFind⟩ := hSpec.sender_type
  -- SelectReady gives us the receiver readiness condition
  have hTargetReady : ∀ Ltarget, lookupG G { sid := senderEp.sid, role := receiverRole } = some Ltarget →
      ∃ L'', Consume senderEp.role Ltarget
        (lookupD D { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole }) = some L'' ∧
        (Consume senderEp.role L'' [.string]).isSome := by
    intro Ltarget hLtarget
    exact hReady senderEp receiverRole branches chosen L' hSenderType hFind Ltarget hLtarget
  -- Apply Protocol-level preservation
  have hResult := Coherent_select_preserved G D senderEp receiverRole branches chosen L'
    hCoh hSenderType hFind hTargetReady
  -- The spec tells us G' and D' are the result of the update
  have hGUpdate : G' = updateG G senderEp L' := hSpec.type_updated branches L' hSenderType hFind
  rw [hGUpdate, hSpec.trace_extended]
  exact hResult

/-! ### Branch Preservation -/

/-- Branch preserves Coherence.

    Similar to receive, but the buffer head is a label (.string) value. -/
theorem BranchSpec_preserves_Coherent {G G' : GEnv} {D D' : DEnv}
    {receiverEp : Endpoint} {senderRole : Role} {received : Label}
    (hSpec : BranchSpec G G' D D' receiverEp senderRole received)
    (hCoh : Coherent G D) :
    Coherent G' D' := by
  -- Extract receiver type and buffer data from spec
  obtain ⟨branches, L', hRecvType, hFind⟩ := hSpec.receiver_type
  obtain ⟨rest, hBuffer⟩ := hSpec.buffer_has_label
  -- Construct the trace head evidence
  let edge : Edge := { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role }
  have hTraceHead : (lookupD D edge).head? = some .string := by
    simp only [edge, hBuffer, List.head?_cons]
  -- Apply Protocol-level preservation
  have hResult := Coherent_branch_preserved G D receiverEp senderRole branches received L'
    hCoh hRecvType hFind hTraceHead
  -- The spec tells us G' and D' are the result of the update
  have hGUpdate : G' = updateG G receiverEp L' := hSpec.type_updated branches L' hRecvType hFind
  obtain ⟨rest', hTraceEq, hDUpdate⟩ := hSpec.trace_consumed
  -- Show rest = rest'
  have hRestEq : rest = rest' := by
    have h1 : ValType.string :: rest = lookupD D edge := hBuffer.symm
    have h2 : ValType.string :: rest' = lookupD D edge := hTraceEq.symm
    have h3 : ValType.string :: rest = ValType.string :: rest' := h1.trans h2.symm
    exact List.tail_eq_of_cons_eq h3
  rw [hGUpdate, hDUpdate, ← hRestEq]
  simpa [edge, hBuffer, List.tail_cons] using hResult

/-! ## Open/Close Preservation -/

/-- Open preserves Coherence (new session is Coherent by construction).

    The key insight is that:
    1. Old edges (in sessions ≠ s) are unchanged by the frame property
    2. New edges (in session s) have empty traces, so Consume L [] = some L -/
theorem OpenSpec_preserves_Coherent {G G' : GEnv} {D D' : DEnv}
    {s : SessionId} {roles : List Role}
    (hSpec : OpenSpec G G' D D' s roles)
    (hCoh : Coherent G D) :
    Coherent G' D' := by
  intro e hActive
  -- Case split: is this edge in the new session or an old session?
  by_cases hSid : e.sid = s
  · -- New session edge: trace is empty, so EdgeCoherent is trivial
    intro Lrecv hGrecv
    -- Trace is empty for new session edges
    have hTraceEmpty : lookupD D' e = [] := hSpec.traces_empty e hSid
    -- Sender exists in G' (by ActiveEdge)
    rcases (Option.isSome_iff_exists).1 hActive.1 with ⟨Lsender, hLsender⟩
    -- EdgeCoherent with empty trace: Consume L [] = some L
    refine ⟨Lsender, hLsender, ?_⟩
    simp [hTraceEmpty, Consume]
  · -- Old session edge: preserved by frame property
    -- G' agrees with G on old sessions
    have hGFrame : lookupG G' { sid := e.sid, role := e.receiver } =
        lookupG G { sid := e.sid, role := e.receiver } := hSpec.frame_G _ (by simp [hSid])
    have hGFrameSender : lookupG G' { sid := e.sid, role := e.sender } =
        lookupG G { sid := e.sid, role := e.sender } := hSpec.frame_G _ (by simp [hSid])
    have hDFrame : lookupD D' e = lookupD D e := hSpec.frame_D e hSid
    -- ActiveEdge in G' implies ActiveEdge in G
    have hActiveOld : ActiveEdge G e := by
      simp only [ActiveEdge] at hActive ⊢
      rw [hGFrame, hGFrameSender] at hActive
      exact hActive
    -- Apply original coherence
    intro Lrecv hGrecv
    rw [hGFrame] at hGrecv
    obtain ⟨Lsender, hLsender, hConsume⟩ := hCoh e hActiveOld Lrecv hGrecv
    use Lsender
    constructor
    · rw [hGFrameSender]; exact hLsender
    · rw [hDFrame]; exact hConsume

/-! ### Close Preservation -/

/-- Helper: an edge targeting the removed endpoint cannot stay active after close. -/
private lemma close_target_removed_contra {G G' : GEnv} {D : DEnv}
    {ep : Endpoint} {e : Edge}
    (hSpec : CloseSpec G G' D ep)
    (hActive : ActiveEdge G' e)
    (hRecv : e.sid = ep.sid ∧ e.receiver = ep.role) : False := by
  simp only [ActiveEdge] at hActive
  obtain ⟨hSid, hRole⟩ := hRecv
  have hEpRemoved : lookupG G' ep = none := hSpec.endpoint_removed
  have hRecvEp : { sid := e.sid, role := e.receiver : Endpoint } = ep := by
    cases ep with
    | mk epSid epRole =>
        cases e with
        | mk sid sender receiver =>
            cases hSid
            cases hRole
            rfl
  rw [hRecvEp] at hActive
  simp [hEpRemoved] at hActive

/-! ## Close Preservation Theorem -/

/-- Close preserves Coherence (edges become inactive).

    Removing an endpoint at `End` with empty traces makes edges involving
    that endpoint inactive (no receiver in G'), so they're skipped in Coherent. -/
theorem CloseSpec_preserves_Coherent {G G' : GEnv} {D : DEnv}
    {ep : Endpoint}
    (hSpec : CloseSpec G G' D ep)
    (hCoh : Coherent G D) :
    Coherent G' D := by
  intro e hActive
  -- If edge involves ep as receiver, then ActiveEdge fails after close
  by_cases hRecv : e.sid = ep.sid ∧ e.receiver = ep.role
  · -- Edge has ep as receiver, but ep is removed
    exact False.elim (close_target_removed_contra hSpec hActive hRecv)
  · -- Edge doesn't have ep as receiver, preserved by frame
    push_neg at hRecv
    have hFrame : lookupG G' { sid := e.sid, role := e.receiver } =
        lookupG G { sid := e.sid, role := e.receiver } := by
      apply hSpec.frame_G
      intro hEq
      have hSid : e.sid = ep.sid := by
        simpa using congrArg Endpoint.sid hEq
      have hRole : e.receiver = ep.role := by
        simpa using congrArg Endpoint.role hEq
      exact (hRecv hSid) (by simpa using hRole)
    have hFrameSender : lookupG G' { sid := e.sid, role := e.sender } =
        lookupG G { sid := e.sid, role := e.sender } := by
      apply hSpec.frame_G
      intro hEq
      -- If sender = ep, then G'[ep] = none (endpoint removed)
      -- But ActiveEdge requires lookupG G' sender to be some _, contradiction
      exfalso
      simp only [ActiveEdge] at hActive
      have hEpRemoved : lookupG G' ep = none := hSpec.endpoint_removed
      have hSenderEp : { sid := e.sid, role := e.sender : Endpoint } = ep := hEq
      rw [hSenderEp] at hActive
      simp [hEpRemoved] at hActive
    -- ActiveEdge in G' implies ActiveEdge in G
    have hActiveOld : ActiveEdge G e := by
      simp only [ActiveEdge] at hActive ⊢
      rw [hFrame, hFrameSender] at hActive
      exact hActive
    -- Apply original coherence
    intro Lrecv hGrecv
    rw [hFrame] at hGrecv
    obtain ⟨Lsender, hLsender, hConsume⟩ := hCoh e hActiveOld Lrecv hGrecv
    use Lsender
    constructor
    · rw [hFrameSender]; exact hLsender
    · exact hConsume

/-! ## Acquire Preservation -/

/-- Acquire preserves Coherence (uses delegation_preserves_coherent).

    The spec includes a DelegationStep, which directly provides coherence
    preservation via the proved `delegation_preserves_coherent` theorem. -/
theorem AcquireSpec_preserves_Coherent {G G' : GEnv} {D D' : DEnv}
    {receiverEp : Endpoint} {senderRole : Role}
    {delegatedSession : SessionId} {delegatedRole : Role}
    (hSpec : AcquireSpec G G' D D' receiverEp senderRole delegatedSession delegatedRole)
    (hCoh : Coherent G D) :
    Coherent G' D' := by
  -- The spec includes a DelegationStep, which preserves coherence
  exact delegation_preserves_coherent G G' D D' delegatedSession senderRole receiverEp.role
    hCoh hSpec.delegation_applied


end
