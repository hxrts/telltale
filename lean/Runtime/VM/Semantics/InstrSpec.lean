import Protocol.Coherence.Delegation

/-! # Instruction Denotational Specifications

This module defines denotational instruction specs for VM operations in terms of
Protocol-level GEnv and DEnv updates. Each instruction has:

1. **Spec** — what the instruction does to G/D (environment changes)
2. **Footprint** — which sessions the instruction affects (for frame rule)
3. **Delegation bridge hook** — `acquire` carries a `DelegationStep` witness

These specs are the Rust-portable VM layer. Proof theorems live in
`Runtime.Proofs.VM.InstrSpec`. -/

/-
The Problem. VM instructions must be specified in terms of Protocol-level environment
updates (GEnv, DEnv) to enable coherence preservation proofs. Each instruction needs
a clear contract specifying preconditions, postconditions, and footprint.

Solution Structure. For each instruction type (send, recv, select, branch, acquire),
defines a `*Spec` structure with: sender/receiver type conditions, update equations
for G'/D', frame conditions for unchanged entries, and footprint (affected sessions).
The specs are used by `Runtime.Proofs.VM.InstrSpec` to prove preservation theorems.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

section

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
  type_updated :
    ∀ L', lookupG G senderEp = some (.send receiverRole T L') →
      G' = updateG G senderEp L'
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
  type_updated :
    ∀ L', lookupG G receiverEp = some (.recv senderRole T L') →
      G' = updateG G receiverEp L'
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
  type_updated :
    ∀ branches L',
      lookupG G senderEp = some (.select receiverRole branches) →
      branches.find? (fun b => b.1 == chosen) = some (chosen, L') →
      G' = updateG G senderEp L'
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
  type_updated :
    ∀ branches L',
      lookupG G receiverEp = some (.branch senderRole branches) →
      branches.find? (fun b => b.1 == received) = some (received, L') →
      G' = updateG G receiverEp L'
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
  fresh : ∀ ep, (lookupG G ep).isSome → ep.sid ≠ s
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
    (delegatedSession : SessionId) (delegatedRole : Role) where
  /-- Sender has send type with channel value. -/
  sender_type : ∃ L',
    lookupG G senderEp = some (.send receiverRole (.chan delegatedSession delegatedRole) L')
  /-- Sender's type is updated to continuation. -/
  type_updated :
    ∀ L', lookupG G senderEp = some (.send receiverRole (.chan delegatedSession delegatedRole) L') →
      G' = updateG G senderEp L'
  /-- Trace is extended with the capability. -/
  trace_extended :
    let edge := { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole }
    D' = updateD D edge (lookupD D edge ++ [.chan delegatedSession delegatedRole])
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
    (delegatedSession : SessionId) (delegatedRole : Role) where
  /-- Receiver has recv type with channel value. -/
  receiver_type : ∃ L',
    lookupG G receiverEp = some (.recv senderRole (.chan delegatedSession delegatedRole) L')
  /-- Buffer has capability at head. -/
  buffer_has_capability :
    let edge := { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role }
    ∃ rest, lookupD D edge = .chan delegatedSession delegatedRole :: rest
  /-- Receiver's type is updated to continuation. -/
  type_updated :
    ∀ L', lookupG G receiverEp = some (.recv senderRole (.chan delegatedSession delegatedRole) L') →
      G' = updateG G receiverEp L'
  /-- Delegation step occurred (uses delegation_preserves_coherent). -/
  delegation_applied :
    DelegationStep G G' D D' delegatedSession senderRole receiverEp.role

/-- VM-level `receive` of a delegated endpoint corresponds to a Protocol-level
    `DelegationStep` on the delegated session. -/
def vm_receive_delegation_corresponds_protocol
    {G G' : GEnv} {D D' : DEnv}
    {receiverEp : Endpoint} {senderRole : Role}
    {delegatedSession : SessionId} {delegatedRole : Role}
    (hSpec : AcquireSpec G G' D D' receiverEp senderRole delegatedSession delegatedRole) :
    DelegationStep G G' D D' delegatedSession senderRole receiverEp.role :=
  hSpec.delegation_applied

/-- Footprint for acquire: receiver's session (footprint grows after!). -/
def AcquireFootprint (receiverEp : Endpoint) : Set SessionId :=
  {receiverEp.sid}

/-! ## Instruction Footprint Function -/

/-- Compute the footprint of an instruction given the endpoint it operates on. -/
def instrFootprint (ep : Endpoint) (delegatedSession : Option SessionId) : Set SessionId :=
  match delegatedSession with
  | none => {ep.sid}
  | some s => {ep.sid, s}


/-!
Proof-only preservation and quotient-respecting theorems for instruction specs
live in `Runtime.Proofs.VM.InstrSpec`.
-/

end
