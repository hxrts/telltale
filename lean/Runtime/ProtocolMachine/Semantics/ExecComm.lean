import Protocol.Environments.Core
import Runtime.Resources.ResourceModel
import Runtime.ProtocolMachine.Semantics.ExecHelpers
/-! # Communication Instruction Semantics
Step functions for the four communication instructions: `send`, `receive`, `offer`, `choose`.
Each is decomposed into a pipeline of private helpers (operand decoding → ownership check →
session type lookup → edge validation → handler lookup → buffer operation → transport spec
check → session store update → event emission) so that individual stages stay short and
testable.
Send/offer sign outgoing values with the role's signing key before enqueueing.
Recv/choose verify the sender's signature, consume a progress token, and dequeue from
the buffer. All four update the session store's local type and trace on success. -/
/-! ## Communication identity and replay semantics
Canonical communication identity fields (matched with Rust runtime docs):
- domain tag: `telltale.comm.identity.v1`
- session id (`sid`)
- directed edge endpoints (`sender`, `receiver`)
- protocol step context (`send`/`recv`/`offer`/`choose`) with label context
- message label (`label`)
- payload digest (domain-separated hash of serialized payload)
- sequence number (`seqNo`)
Replay semantics by mode:
- `off`: no replay-consumption enforcement.
- `sequence`: receive must consume exactly the next expected sequence number on each edge.
- `nullifier`: receive must consume an unseen nullifier derived from canonical identity.
Expected outcomes:
- duplicate delivery: rejected in `sequence` and `nullifier`, accepted in `off`
- reordered delivery: rejected in `sequence`; allowed in `nullifier` when identity is unseen
- cross-session reuse: rejected in `sequence` and `nullifier` because `sid` is part of identity
-/
/-
The Problem. The four communication instructions (send, recv, offer, choose) share a
complex pipeline: operand decoding, ownership checks, type lookup, edge validation,
handler lookup, buffer operations, transport spec checks, and state updates. Each
stage can fail with different fault types.
Solution Structure. Decomposes each instruction into a pipeline of private helpers.
`sendUpdateSessions`/`sendCommit`/`sendAfterEnqueue` handle send stages. Similar
helpers exist for recv, offer, choose. Each helper is small enough to test independently.
Final stage updates session store (type, trace, buffers) and emits observable events.
-/
set_option autoImplicit false
universe u
private def payloadByteEstimate (v : Value) : Nat :=
  (reprStr v).length
def payloadSizeViolation? {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (context : String) (v : Value) : Option String :=
  if st.config.payloadValidationMode = .off then
    none
  else
    let bytes := payloadByteEstimate v
    if bytes ≤ st.config.maxPayloadBytes then
      none
    else
      some s!"{context} payload exceeds max_payload_bytes={st.config.maxPayloadBytes} (actual={bytes})"
private def recvIdentityLabel (T : ValType) : Label :=
  s!"recv:{reprStr T}"

private def payloadLabelOrFallback (fallback : Label) (payload : Value) : Label :=
  match payload with
  | .string lbl => lbl
  | _ => fallback
private def strictSchemaAnnotationMessage (role context label : String) : String :=
  s!"{role}: {context} payload '{label}' requires explicit ValType annotation in strict_schema mode"
private def strictSchemaMissingAnnotationSend?
    {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (role : Role) (choices : List (Label × LocalType)) : Option String :=
  if st.config.payloadValidationMode = .strictSchema then
    match choices with
    | (lbl, _) :: [] => some (strictSchemaAnnotationMessage role "send" lbl)
    | _ => none
  else
    none
private def strictSchemaMissingAnnotationRecv?
    {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (role : Role) (choices : List (Label × LocalType)) : Option String :=
  if st.config.payloadValidationMode = .strictSchema then
    match choices with
    | (lbl, _) :: [] => some (strictSchemaAnnotationMessage role "receive" lbl)
    | _ => none
  else
    none
/-! ## Send semantics -/
def sendUpdateSessions {ν : Type u} [VerificationModel ν]
    (sessions : SessionStore ν) (ep : Endpoint) (edge : Edge)
    (bufs' : SignedBuffers ν) (T : ValType) (L' : LocalType) : SessionStore ν :=
  let sessions1 := updateSessBuffers sessions ep.sid bufs'
  let trace := SessionStore.lookupTrace sessions1 edge
  let sessions2 := SessionStore.updateTrace sessions1 edge (trace ++ [T])
  SessionStore.updateType sessions2 ep L'
def sendCommit {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (bufs' : SignedBuffers ν) (T : ValType) (L' : LocalType) (v : Value) (seqNo : Nat)
    (lbl : Option Label) : StepPack ι γ π ε ν :=
  let sessions' := sendUpdateSessions st.sessions ep edge bufs' T L'
  let st' := { st with buffers := bufs', sessions := sessions' }
  continuePack st' coro (some (.obs (.sent edge v seqNo lbl)))
def sendAfterEnqueue {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (T : ValType) (L' : LocalType) (v : Value) (h : HandlerId) (seqNo : Nat)
    (res : SignedEnqueueResult) (bufs' : SignedBuffers ν) (lbl : Option Label) :
    StepPack ι γ π ε ν :=
  match res with
  | .ok =>
      if st.config.transportOk h bufs' = false then
        faultPack st coro (.specFault "handler spec failed") "handler spec failed"
      else
        sendCommit st coro ep edge bufs' T L' v seqNo lbl
  | .blocked =>
      blockPack st coro (.sendWait edge)
  | .dropped =>
      faultPack st coro (.flowViolation "buffer drop") "buffer drop"
  | .error =>
      faultPack st coro (.flowViolation "buffer overflow") "buffer overflow"
def sendOnHandler {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (T : ValType) (L' : LocalType) (v : Value) (h : HandlerId) (lbl : Option Label) :
    StepPack ι γ π ε ν :=
  let (seqNo, st') := commAllocSendSeq st edge
  let signed := signValueWithSeq (st'.config.roleSigningKey ep.role) v seqNo
  let cfg := st'.config.bufferConfig edge
  let (res, bufs') := bufEnqueue cfg st'.buffers edge signed
  sendAfterEnqueue st' coro ep edge T L' v h seqNo res bufs' lbl
/-! ## Send semantics: edge and endpoint dispatch -/
def sendOnEdge {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint)
    (edge : Edge) (T : ValType) (L' : LocalType) (v : Value) (lbl : Option Label) :
    StepPack ι γ π ε ν :=
  if edgePartitioned st edge then
    blockPack st coro (.sendWait edge)
  else if edgeCrashed st edge then
    faultPack st coro (.specFault "edge crashed") "edge crashed"
  else
    match SessionStore.lookupHandler st.sessions edge with
    | none => faultPack st coro (.specFault "no handler bound") "no handler bound"
    | some h => sendOnHandler st coro ep edge T L' v h lbl
def sendWithType {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε)
    (ep : Endpoint) (r : Role) (T : ValType) (L' : LocalType) (v : Value) (lbl : Option Label) :
    StepPack ι γ π ε ν :=
  if decide (valTypeOf v = T) then
    match payloadSizeViolation? st "send" v with
    | some msg => faultPack st coro (.specFault msg) msg
    | none =>
        let edge := edgeTo ep r
        sendOnEdge st coro ep edge T L' v lbl
  else
    faultPack st coro (.typeViolation T (valTypeOf v)) "bad send payload"
def sendWithEndpoint {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε)
    (ep : Endpoint) (v : Value) : StepPack ι γ π ε ν :=
  if owns coro ep then
    match (SessionStore.lookupType st.sessions ep).map LocalType.unfold with
    | some (.send r T L') => sendWithType st coro ep r T L' v none
    | some (.select r choices) =>
        match strictSchemaMissingAnnotationSend? st ep.role choices with
        | some msg => faultPack st coro (.specFault msg) msg
        | none =>
            match choices with
            | [(lbl, L')] => sendWithType st coro ep r (valTypeOf v) L' v (some lbl)
            | _ => faultPack st coro (.specFault "send not permitted") "send not permitted"
    | _ => faultPack st coro (.specFault "send not permitted") "send not permitted"
  else
    faultPack st coro (.channelClosed ep) "endpoint not owned"
/-! ## Send semantics: instruction entrypoint -/
def stepSend {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε)
    (chan val : Reg) : StepPack ι γ π ε ν :=
  match readReg coro.regs chan, readReg coro.regs val with
  | some (.chan ep), some v => sendWithEndpoint st coro ep v
  | some (.chan _), none => faultPack st coro .outOfRegisters "missing send value"
  | some v, _ => faultPack st coro (.typeViolation (.chan 0 "") (valTypeOf v)) "bad send channel"
  | none, _ => faultPack st coro .outOfRegisters "missing send channel"
/-! ## Receive semantics -/
def recvUpdateSessions {ν : Type u} [VerificationModel ν]
    (sessions : SessionStore ν) (ep : Endpoint) (edge : Edge)
    (bufs' : SignedBuffers ν) (L' : LocalType) : SessionStore ν :=
  let sessions1 := updateSessBuffers sessions ep.sid bufs'
  let trace := SessionStore.lookupTrace sessions1 edge
  let trace' := match trace with | [] => [] | _ :: ts => ts
  let sessions2 := SessionStore.updateTrace sessions1 edge trace'
  SessionStore.updateType sessions2 ep L'
def recvCommit {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (bufs' : SignedBuffers ν) (L' : LocalType) (payload : Value) (tokens' : List ProgressToken)
    (dst : Reg) (seqNo : Nat) (lbl : Option Label) : StepPack ι γ π ε ν :=
  match setReg coro.regs dst payload with
  | none => faultPack st coro .outOfRegisters "bad dst reg"
  | some regs' =>
      let sessions' := recvUpdateSessions st.sessions ep edge bufs' L'
      let st' := { st with buffers := bufs', sessions := sessions' }
      let coro' := { coro with regs := regs', progressTokens := tokens' }
      continuePack st' coro' (some (.obs (.received edge payload seqNo lbl)))

/-! ## Receive semantics: validation and replay-consumption -/

def recvAfterDequeue {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (T : ValType) (L' : LocalType) (dst : Reg) (h : HandlerId)
    (tokens' : List ProgressToken) (sv : SignedValue ν) (bufs' : SignedBuffers ν)
    (lbl : Option Label) : StepPack ι γ π ε ν :=
  match payloadSizeViolation? st "receive" sv.payload with
  | some msg =>
      faultPack st coro (.specFault msg) msg
  | none =>
      if st.config.transportOk h bufs' = false then
        faultPack st coro (.specFault "handler spec failed") "handler spec failed"
      else
        let vk := VerificationModel.verifyKeyOf (st.config.roleSigningKey edge.sender)
        if verifySignedValue vk sv then
          let ident : CommunicationIdentity := {
            sid := edge.sid
            sender := edge.sender
            receiver := edge.receiver
            stepKind := .receive
            label := payloadLabelOrFallback (recvIdentityLabel T) sv.payload
            payloadDigest := communicationIdentityPayloadDigest sv.payload
            seqNo := sv.seqNo
          }
          match commConsumeReceiveIdentity st st.clock ident with
          | .error msg => faultPack st coro (.flowViolation msg) msg
          | .ok (_, st') =>
              if decide (valTypeOf sv.payload = T) then
                recvCommit st' coro ep edge bufs' L' sv.payload tokens' dst sv.seqNo lbl
              else
                faultPack st' coro (.typeViolation T (valTypeOf sv.payload)) "bad recv payload"
        else
          faultPack st coro (.invalidSignature edge) "invalid signature"
/-! ## Receive semantics: dequeue and edge checks -/
def recvWithHandler {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (T : ValType) (L' : LocalType) (dst : Reg) (h : HandlerId)
    (tokens' : List ProgressToken) (lbl : Option Label) : StepPack ι γ π ε ν :=
  match bufDequeue st.buffers edge with
  | none =>
      let coro' := { coro with progressTokens := tokens' }
      blockPack st coro' (.recvWait edge { sid := edge.sid, endpoint := { sid := edge.sid, role := edge.receiver } })
  | some (sv, bufs') =>
      recvAfterDequeue st coro ep edge T L' dst h tokens' sv bufs' lbl
def recvOnEdge {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint)
    (edge : Edge) (T : ValType) (L' : LocalType) (dst : Reg)
    (token : ProgressToken) (lbl : Option Label) : StepPack ι γ π ε ν :=
  if edgePartitioned st edge then
    blockPack st coro (.recvWait edge token)
  else if edgeCrashed st edge then
    faultPack st coro (.specFault "edge crashed") "edge crashed"
  else
    match SessionStore.lookupHandler st.sessions edge with
    | none => faultPack st coro (.specFault "no handler bound") "no handler bound"
    | some h => recvWithHandler st coro ep edge T L' dst h coro.progressTokens lbl
/-- Type of the payload at the head of `edge`'s buffer (`unit` when empty).
A label-only receive (one-entry `branch`) accepts whatever payload type the
sender used, as the Rust runtime does for un-annotated messages. -/
def headPayloadType {ν : Type u} [VerificationModel ν]
    (bufs : SignedBuffers ν) (edge : Edge) : ValType :=
  match bufDequeue bufs edge with
  | some (sv, _) => valTypeOf sv.payload
  | none => .unit
def recvWithEndpoint {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε)
    (ep : Endpoint) (dst : Reg) : StepPack ι γ π ε ν :=
  if owns coro ep then
    match (SessionStore.lookupType st.sessions ep).map LocalType.unfold with
    | some (.recv r T L') =>
        let edge := edgeFrom r ep
        let token := { sid := edge.sid, endpoint := { sid := edge.sid, role := edge.receiver } }
        recvOnEdge st coro ep edge T L' dst token none
    | some (.branch r choices) =>
        match strictSchemaMissingAnnotationRecv? st ep.role choices with
        | some msg => faultPack st coro (.specFault msg) msg
        | none =>
            match choices with
            | [(lbl, L')] =>
                let edge := edgeFrom r ep
                let token := { sid := edge.sid, endpoint := { sid := edge.sid, role := edge.receiver } }
                recvOnEdge st coro ep edge (headPayloadType st.buffers edge) L' dst token (some lbl)
            | _ => faultPack st coro (.specFault "recv not permitted") "recv not permitted"
    | _ => faultPack st coro (.specFault "recv not permitted") "recv not permitted"
  else
    faultPack st coro (.channelClosed ep) "endpoint not owned"
/-! ## Receive semantics: instruction entrypoint -/
def stepReceive {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε)
    (chan dst : Reg) : StepPack ι γ π ε ν :=
  match readReg coro.regs chan with
  | some (.chan ep) => recvWithEndpoint st coro ep dst
  | some v => faultPack st coro (.typeViolation (.chan 0 "") (valTypeOf v)) "bad recv channel"
  | none => faultPack st coro .outOfRegisters "missing recv channel"
