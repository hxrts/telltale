import Protocol.Coherence.EdgeCoherence
import Protocol.Coherence.Preservation

/-!
# Instruction Denotational Specifications

This module defines the denotational semantics for VM instructions in terms of
Protocol-level GEnv and DEnv updates. Each instruction has:

1. **Spec** — what the instruction does to G/D (environment changes)
2. **Footprint** — which sessions the instruction affects (for frame rule)
3. **Preservation** — the instruction preserves Coherence

These specifications serve as the bridge between VM operational semantics
(in ExecComm.lean, ExecSession.lean, etc.) and Protocol-level theorems.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Classical

noncomputable section

/-! ## Send Instruction -/

/-- Denotational specification for send: appends a value to the edge trace
    and advances the sender's local type.

    Pre:  G[senderEp] = send(r, T, L')
          Coherent G D
          SendReady G D  (receiver can accept after consuming current trace)
    Post: G'[senderEp] = L'
          D'[sender→r] = D[sender→r] ++ [T]
          Coherent G' D'  (from SendReady + Coherent_send_preserved) -/
structure SendSpec (G G' : GEnv) (D D' : DEnv)
    (senderEp : Endpoint) (receiverRole : Role) (T : ValType) where
  /-- Sender has the expected send type. -/
  sender_type : ∃ L', lookupG G senderEp = some (.send receiverRole T L')
  /-- Sender's type is updated to continuation. -/
  type_updated : ∃ L', G' = updateG G senderEp L'
  /-- Trace is extended with the sent value. -/
  trace_extended :
    let edge := { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole }
    D' = updateD D edge (lookupD D edge ++ [T])
  /-- Other endpoints unchanged. -/
  frame_G : ∀ ep', ep' ≠ senderEp → lookupG G' ep' = lookupG G ep'
  /-- Other traces unchanged. -/
  frame_D : ∀ e,
    e ≠ { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole } →
    lookupD D' e = lookupD D e

/-- Footprint for send: the sender's session. -/
def SendFootprint (senderEp : Endpoint) : Set SessionId :=
  {senderEp.sid}

/-! ## Receive Instruction -/

/-- Denotational specification for receive: dequeues a value from the edge buffer
    and advances the receiver's local type.

    Pre:  G[receiverEp] = recv(s, T, L')
          D[s→receiver] = T :: rest
          Coherent G D
    Post: G'[receiverEp] = L'
          D'[s→receiver] = rest
          Coherent G' D'  (from Coherent_recv_preserved) -/
structure RecvSpec (G G' : GEnv) (D D' : DEnv)
    (receiverEp : Endpoint) (senderRole : Role) (T : ValType) where
  /-- Receiver has the expected recv type. -/
  receiver_type : ∃ L', lookupG G receiverEp = some (.recv senderRole T L')
  /-- Buffer has expected value at head. -/
  buffer_has_data :
    let edge := { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role }
    ∃ rest, lookupD D edge = T :: rest
  /-- Receiver's type is updated to continuation. -/
  type_updated : ∃ L', G' = updateG G receiverEp L'
  /-- Trace head is consumed. -/
  trace_consumed :
    let edge := { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role }
    ∃ rest, lookupD D edge = T :: rest ∧ D' = updateD D edge rest
  /-- Other endpoints unchanged. -/
  frame_G : ∀ ep', ep' ≠ receiverEp → lookupG G' ep' = lookupG G ep'
  /-- Other traces unchanged. -/
  frame_D : ∀ e,
    e ≠ { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role } →
    lookupD D' e = lookupD D e

/-- Footprint for receive: the receiver's session. -/
def RecvFootprint (receiverEp : Endpoint) : Set SessionId :=
  {receiverEp.sid}

/-! ## Select Instruction -/

/-- Denotational specification for select: chooses a branch and sends a label
    to the receiver.

    Pre:  G[senderEp] = select(r, branches)
          (ℓ, L') ∈ branches
          Coherent G D
    Post: G'[senderEp] = L'
          D'[sender→r] = D[sender→r] ++ [.string]  (label encoding)
          Coherent G' D' -/
structure SelectSpec (G G' : GEnv) (D D' : DEnv)
    (senderEp : Endpoint) (receiverRole : Role) (chosen : Label) where
  /-- Sender has the expected select type with the chosen branch. -/
  sender_type : ∃ branches L',
    lookupG G senderEp = some (.select receiverRole branches) ∧
    branches.find? (fun b => b.1 == chosen) = some (chosen, L')
  /-- Sender's type is updated to chosen continuation. -/
  type_updated : ∃ L', G' = updateG G senderEp L'
  /-- Trace is extended with the label (encoded as .string). -/
  trace_extended :
    let edge := { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole }
    D' = updateD D edge (lookupD D edge ++ [.string])
  /-- Other endpoints unchanged. -/
  frame_G : ∀ ep', ep' ≠ senderEp → lookupG G' ep' = lookupG G ep'
  /-- Other traces unchanged. -/
  frame_D : ∀ e,
    e ≠ { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole } →
    lookupD D' e = lookupD D e

/-- Footprint for select: the sender's session. -/
def SelectFootprint (senderEp : Endpoint) : Set SessionId :=
  {senderEp.sid}

/-! ## Branch Instruction -/

/-- Denotational specification for branch: receives a label and continues
    with the corresponding branch.

    Pre:  G[receiverEp] = branch(s, branches)
          D[s→receiver] = .string :: rest  (label at head)
          (received_label, L') ∈ branches
          Coherent G D
    Post: G'[receiverEp] = L'
          D'[s→receiver] = rest
          Coherent G' D' -/
structure BranchSpec (G G' : GEnv) (D D' : DEnv)
    (receiverEp : Endpoint) (senderRole : Role) (received : Label) where
  /-- Receiver has the expected branch type with the received label. -/
  receiver_type : ∃ branches L',
    lookupG G receiverEp = some (.branch senderRole branches) ∧
    branches.find? (fun b => b.1 == received) = some (received, L')
  /-- Buffer has label at head. -/
  buffer_has_label :
    let edge := { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role }
    ∃ rest, lookupD D edge = .string :: rest
  /-- Receiver's type is updated to chosen continuation. -/
  type_updated : ∃ L', G' = updateG G receiverEp L'
  /-- Trace head is consumed. -/
  trace_consumed :
    let edge := { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role }
    ∃ rest, lookupD D edge = .string :: rest ∧ D' = updateD D edge rest
  /-- Other endpoints unchanged. -/
  frame_G : ∀ ep', ep' ≠ receiverEp → lookupG G' ep' = lookupG G ep'
  /-- Other traces unchanged. -/
  frame_D : ∀ e,
    e ≠ { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role } →
    lookupD D' e = lookupD D e

/-- Footprint for branch: the receiver's session. -/
def BranchFootprint (receiverEp : Endpoint) : Set SessionId :=
  {receiverEp.sid}

/-! ## Open Instruction -/

/-- Denotational specification for open: creates a new session with fresh ID.

    Pre:  Coherent G D
          s is fresh (not used in G or D)
    Post: G' = G ∪ { (s,r) ↦ project(globalType, r) | r ∈ roles }
          D' = D ∪ { (s,p,q) ↦ [] | p,q ∈ roles }
          Coherent G' D'  (new session is Coherent by construction) -/
structure OpenSpec (G G' : GEnv) (D D' : DEnv)
    (s : SessionId) (roles : List Role) where
  /-- Session ID is fresh. -/
  fresh : ∀ ep, lookupG G ep = some _ → ep.sid ≠ s
  /-- New session endpoints added. -/
  endpoints_added : ∀ r ∈ roles, (lookupG G' { sid := s, role := r }).isSome
  /-- Existing endpoints unchanged. -/
  frame_G : ∀ ep, ep.sid ≠ s → lookupG G' ep = lookupG G ep
  /-- New session traces are empty. -/
  traces_empty : ∀ e, e.sid = s → lookupD D' e = []
  /-- Existing traces unchanged. -/
  frame_D : ∀ e, e.sid ≠ s → lookupD D' e = lookupD D e

/-- Footprint for open: the new session. -/
def OpenFootprint (s : SessionId) : Set SessionId :=
  {s}

/-! ## Close Instruction -/

/-- Denotational specification for close: removes an endpoint that has reached End.

    Pre:  G[ep] = End
          All edges involving ep have empty traces
          Coherent G D
    Post: G' = G \ {ep}
          Coherent G' D  (edges become inactive) -/
structure CloseSpec (G G' : GEnv) (D : DEnv) (ep : Endpoint) where
  /-- Endpoint has End type. -/
  endpoint_at_end : lookupG G ep = some .end_
  /-- Outgoing traces empty. -/
  outgoing_empty : ∀ other, lookupD D { sid := ep.sid, sender := ep.role, receiver := other } = []
  /-- Incoming traces empty. -/
  incoming_empty : ∀ other, lookupD D { sid := ep.sid, sender := other, receiver := ep.role } = []
  /-- Endpoint removed. -/
  endpoint_removed : lookupG G' ep = none
  /-- Other endpoints unchanged. -/
  frame_G : ∀ ep', ep' ≠ ep → lookupG G' ep' = lookupG G ep'

/-- Footprint for close: the closed endpoint's session. -/
def CloseFootprint (ep : Endpoint) : Set SessionId :=
  {ep.sid}

/-! ## Delegation Instructions -/

/-- Denotational specification for transfer (send endpoint): sends an endpoint
    capability to another role.

    This is higher-order send where the value is a session capability.

    Pre:  G[senderEp] = send(r, chan(s', L_delegated), L')
          senderEp owns endpoint (s', delegatedRole)
          Coherent G D
    Post: G'[senderEp] = L'
          D'[sender→r] = D[sender→r] ++ [chan(s', L_delegated)]
          Ownership of (s', delegatedRole) transfers to receiver
          Coherent G' D' -/
structure TransferSpec (G G' : GEnv) (D D' : DEnv)
    (senderEp : Endpoint) (receiverRole : Role)
    (delegatedSession : SessionId) (delegatedType : LocalType) where
  /-- Sender has send type with channel value. -/
  sender_type : ∃ L',
    lookupG G senderEp = some (.send receiverRole (.chan delegatedSession delegatedType) L')
  /-- Sender's type is updated to continuation. -/
  type_updated : ∃ L', G' = updateG G senderEp L'
  /-- Trace is extended with the capability. -/
  trace_extended :
    let edge := { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole }
    D' = updateD D edge (lookupD D edge ++ [.chan delegatedSession delegatedType])
  /-- Other endpoints unchanged. -/
  frame_G : ∀ ep', ep' ≠ senderEp → lookupG G' ep' = lookupG G ep'
  /-- Other traces unchanged. -/
  frame_D : ∀ e,
    e ≠ { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole } →
    lookupD D' e = lookupD D e

/-- Footprint for transfer: sender's session AND delegated session. -/
def TransferFootprint (senderEp : Endpoint) (delegatedSession : SessionId) : Set SessionId :=
  {senderEp.sid, delegatedSession}

/-- Denotational specification for acquire (receive endpoint): receives an endpoint
    capability from another role.

    This triggers a DelegationStep on the delegated session.

    Pre:  G[receiverEp] = recv(s, chan(s', L_delegated), L')
          D[s→receiver] = chan(s', L_delegated) :: rest
          Coherent G D
    Post: G'[receiverEp] = L'
          D'[s→receiver] = rest
          Receiver now owns endpoint (s', delegatedRole) with type L_delegated
          Edges in session s' are redirected via DelegationStep
          Coherent G' D' -/
structure AcquireSpec (G G' : GEnv) (D D' : DEnv)
    (receiverEp : Endpoint) (senderRole : Role)
    (delegatedSession : SessionId) (delegatedType : LocalType) where
  /-- Receiver has recv type with channel value. -/
  receiver_type : ∃ L',
    lookupG G receiverEp = some (.recv senderRole (.chan delegatedSession delegatedType) L')
  /-- Buffer has capability at head. -/
  buffer_has_capability :
    let edge := { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role }
    ∃ rest, lookupD D edge = .chan delegatedSession delegatedType :: rest
  /-- Receiver's type is updated to continuation. -/
  type_updated : ∃ L', G' = updateG G receiverEp L'
  /-- Delegation step occurred (uses delegation_preserves_coherent). -/
  delegation_applied :
    DelegationStep G G' D D' delegatedSession senderRole receiverEp.role

/-- Footprint for acquire: receiver's session (footprint grows after!). -/
def AcquireFootprint (receiverEp : Endpoint) : Set SessionId :=
  {receiverEp.sid}

/-! ## Instruction Footprint Function -/

/-- Compute the footprint of an instruction given the endpoint it operates on. -/
def instrFootprint (ep : Endpoint) (delegatedSession : Option SessionId) : Set SessionId :=
  match delegatedSession with
  | none => {ep.sid}
  | some s => {ep.sid, s}

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
  obtain ⟨_, hGUpdate⟩ := hSpec.type_updated
  rw [hGUpdate, hSpec.trace_extended]
  exact hResult

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
  let edge := { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role }
  have hTraceHead : (lookupD D edge).head? = some T := by
    simp only [edge, hBuffer, List.head?_cons]
  -- Apply Protocol-level preservation
  have hResult := Coherent_recv_preserved G D receiverEp senderRole T L' hCoh hRecvType hTraceHead
  -- The spec tells us G' and D' are the result of the update
  obtain ⟨_, hGUpdate⟩ := hSpec.type_updated
  obtain ⟨rest', hTraceEq, hDUpdate⟩ := hSpec.trace_consumed
  -- Show rest = rest' (both come from the same buffer)
  have hRestEq : rest = rest' := by
    have h1 : T :: rest = lookupD D edge := hBuffer.symm
    have h2 : T :: rest' = lookupD D edge := hTraceEq.symm
    have h3 : T :: rest = T :: rest' := h1.trans h2.symm
    exact List.tail_eq_of_cons_eq h3
  rw [hGUpdate, hDUpdate, ← hRestEq]
  -- Show (lookupD D edge).tail = rest
  simp only [edge, hBuffer, List.tail_cons]
  exact hResult

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
  obtain ⟨_, hGUpdate⟩ := hSpec.type_updated
  rw [hGUpdate, hSpec.trace_extended]
  exact hResult

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
  let edge := { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role }
  have hTraceHead : (lookupD D edge).head? = some .string := by
    simp only [edge, hBuffer, List.head?_cons]
  -- Apply Protocol-level preservation
  have hResult := Coherent_branch_preserved G D receiverEp senderRole branches received L'
    hCoh hRecvType hFind hTraceHead
  -- The spec tells us G' and D' are the result of the update
  obtain ⟨_, hGUpdate⟩ := hSpec.type_updated
  obtain ⟨rest', hTraceEq, hDUpdate⟩ := hSpec.trace_consumed
  -- Show rest = rest'
  have hRestEq : rest = rest' := by
    have h1 : ValType.string :: rest = lookupD D edge := hBuffer.symm
    have h2 : ValType.string :: rest' = lookupD D edge := hTraceEq.symm
    have h3 : ValType.string :: rest = ValType.string :: rest' := h1.trans h2.symm
    exact List.tail_eq_of_cons_eq h3
  rw [hGUpdate, hDUpdate, ← hRestEq]
  simp only [edge, hBuffer, List.tail_cons]
  exact hResult

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
    -- The sender must exist (by ActiveEdge)
    have hSenderActive := ActiveEdge_sender_exists hActive
    -- Trace is empty for new session edges
    have hTraceEmpty : lookupD D' e = [] := hSpec.traces_empty e hSid
    -- EdgeCoherent with empty trace: Consume L [] = some L
    use Lrecv
    constructor
    · -- Sender exists in G'
      obtain ⟨Lsender, hLsender⟩ := hSenderActive
      exact ⟨Lsender, hLsender⟩
    · -- Consume with empty trace succeeds
      simp only [hTraceEmpty, Consume]
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
    · rw [← hGFrameSender]; exact hLsender
    · rw [hDFrame]; exact hConsume

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
    exfalso
    simp only [ActiveEdge] at hActive
    obtain ⟨hSid, hRole⟩ := hRecv
    have hEpRemoved : lookupG G' ep = none := hSpec.endpoint_removed
    have hRecvEp : { sid := e.sid, role := e.receiver : Endpoint } = ep := by
      ext <;> simp [hSid, hRole]
    rw [hRecvEp] at hActive
    simp [hEpRemoved] at hActive
  · -- Edge doesn't have ep as receiver, preserved by frame
    push_neg at hRecv
    have hFrame : lookupG G' { sid := e.sid, role := e.receiver } =
        lookupG G { sid := e.sid, role := e.receiver } := by
      apply hSpec.frame_G
      intro hEq
      have : e.sid = ep.sid ∧ e.receiver = ep.role := ⟨congrArg Endpoint.sid hEq, congrArg Endpoint.role hEq⟩
      exact hRecv this
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
    · rw [← hFrameSender]; exact hLsender
    · exact hConsume

/-- Acquire preserves Coherence (uses delegation_preserves_coherent).

    The spec includes a DelegationStep, which directly provides coherence
    preservation via the proved `delegation_preserves_coherent` theorem. -/
theorem AcquireSpec_preserves_Coherent {G G' : GEnv} {D D' : DEnv}
    {receiverEp : Endpoint} {senderRole : Role}
    {delegatedSession : SessionId} {delegatedType : LocalType}
    (hSpec : AcquireSpec G G' D D' receiverEp senderRole delegatedSession delegatedType)
    (hCoh : Coherent G D) :
    Coherent G' D' := by
  -- The spec includes a DelegationStep, which preserves coherence
  exact delegation_preserves_coherent G G' D D' delegatedSession senderRole receiverEp.role
    hCoh hSpec.delegation_applied

end
