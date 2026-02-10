import Protocol.Environments.Core
import Runtime.Resources.ResourceModel
import Runtime.VM.Semantics.ExecHelpers

/-!
# Communication Instruction Semantics

Step functions for the four communication instructions: `send`, `receive`, `offer`, `choose`.
Each is decomposed into a pipeline of private helpers (operand decoding → ownership check →
session type lookup → edge validation → handler lookup → buffer operation → transport spec
check → session store update → event emission) so that individual stages stay short and
testable.

Send/offer sign outgoing values with the role's signing key before enqueueing.
Recv/choose verify the sender's signature, consume a progress token, and dequeue from
the buffer. All four update the session store's local type and trace on success.
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

/-! ## Send semantics -/

private def sendUpdateSessions {ν : Type u} [VerificationModel ν]
    (sessions : SessionStore ν) (ep : Endpoint) (edge : Edge)
    (bufs' : SignedBuffers ν) (T : ValType) (L' : LocalType) : SessionStore ν :=
  -- Update buffers, trace, and local type after a send.
  let sessions1 := updateSessBuffers sessions ep.sid bufs'
  let trace := SessionStore.lookupTrace sessions1 edge
  let sessions2 := SessionStore.updateTrace sessions1 edge (trace ++ [T])
  SessionStore.updateType sessions2 ep L'

private def sendCommit {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (bufs' : SignedBuffers ν) (T : ValType) (L' : LocalType) (v : Value) : StepPack ι γ π ε ν :=
  -- Commit a successful send to state and trace.
  let sessions' := sendUpdateSessions st.sessions ep edge bufs' T L'
  let st' := { st with buffers := bufs', sessions := sessions' }
  continuePack st' coro (some (.obs (.sent edge v 0)))

private def sendAfterEnqueue {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (T : ValType) (L' : LocalType) (v : Value) (h : HandlerId)
    (res : SignedEnqueueResult) (bufs' : SignedBuffers ν) : StepPack ι γ π ε ν :=
  -- Resolve enqueue results and enforce transport checks.
  match res with
  | .ok =>
      if st.config.transportOk h bufs' = false then
        faultPack st coro (.specFault "handler spec failed") "handler spec failed"
      else
        sendCommit st coro ep edge bufs' T L' v
  | .blocked =>
      blockPack st coro (.sendWait edge)
  | .dropped =>
      faultPack st coro (.flowViolation "buffer drop") "buffer drop"
  | .error =>
      faultPack st coro (.flowViolation "buffer overflow") "buffer overflow"

private def sendOnHandler {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (T : ValType) (L' : LocalType) (v : Value) (h : HandlerId) : StepPack ι γ π ε ν :=
  -- Sign and enqueue the payload for the edge handler.
  let signed := signValue (st.config.roleSigningKey ep.role) v
  let cfg := st.config.bufferConfig edge
  let (res, bufs') := bufEnqueue cfg st.buffers edge signed
  sendAfterEnqueue st coro ep edge T L' v h res bufs'

private def sendOnEdge {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint)
    (edge : Edge) (T : ValType) (L' : LocalType) (v : Value) : StepPack ι γ π ε ν :=
  -- Validate edge status and handler binding.
  if edgePartitioned st edge then
    blockPack st coro (.sendWait edge)
  else if edgeCrashed st edge then
    faultPack st coro (.specFault "edge crashed") "edge crashed"
  else
    match SessionStore.lookupHandler st.sessions edge with
    | none => faultPack st coro (.specFault "no handler bound") "no handler bound"
    | some h => sendOnHandler st coro ep edge T L' v h

private def sendWithType {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (ep : Endpoint) (r : Role) (T : ValType) (L' : LocalType) (v : Value) : StepPack ι γ π ε ν :=
  -- Type-check payload and dispatch to edge handling.
  if decide (valTypeOf v = T) then
    let edge := edgeTo ep r
    sendOnEdge st coro ep edge T L' v
  else
    faultPack st coro (.typeViolation T (valTypeOf v)) "bad send payload"

private def sendWithEndpoint {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (ep : Endpoint) (v : Value) : StepPack ι γ π ε ν :=
  -- Ensure ownership and session typing before sending.
  if owns coro ep then
    match SessionStore.lookupType st.sessions ep with
    | some (.send r T L') => sendWithType st coro ep r T L' v
    | _ => faultPack st coro (.specFault "send not permitted") "send not permitted"
  else
    faultPack st coro (.channelClosed ep) "endpoint not owned"


def stepSend {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (chan val : Reg) : StepPack ι γ π ε ν :=
  -- Decode operands then delegate to the send pipeline.
  match readReg coro.regs chan, readReg coro.regs val with
  | some (.chan ep), some v => sendWithEndpoint st coro ep v
  | some (.chan _), none => faultPack st coro .outOfRegisters "missing send value"
  | some v, _ => faultPack st coro (.typeViolation (.chan 0 "") (valTypeOf v)) "bad send channel"
  | none, _ => faultPack st coro .outOfRegisters "missing send channel"

/-! ## Receive semantics -/

private def recvUpdateSessions {ν : Type u} [VerificationModel ν]
    (sessions : SessionStore ν) (ep : Endpoint) (edge : Edge)
    (bufs' : SignedBuffers ν) (L' : LocalType) : SessionStore ν :=
  -- Update buffers, trace, and local type after a receive.
  let sessions1 := updateSessBuffers sessions ep.sid bufs'
  let trace := SessionStore.lookupTrace sessions1 edge
  let trace' := match trace with | [] => [] | _ :: ts => ts
  let sessions2 := SessionStore.updateTrace sessions1 edge trace'
  SessionStore.updateType sessions2 ep L'

private def recvCommit {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (bufs' : SignedBuffers ν) (L' : LocalType) (payload : Value) (tokens' : List ProgressToken)
    (dst : Reg) : StepPack ι γ π ε ν :=
  -- Commit a successful receive to state and registers.
  match setReg coro.regs dst payload with
  | none => faultPack st coro .outOfRegisters "bad dst reg"
  | some regs' =>
      let sessions' := recvUpdateSessions st.sessions ep edge bufs' L'
      let st' := { st with buffers := bufs', sessions := sessions' }
      let coro' := { coro with regs := regs', progressTokens := tokens' }
      continuePack st' coro' (some (.obs (.received edge payload 0)))

private def recvAfterDequeue {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (T : ValType) (L' : LocalType) (dst : Reg) (h : HandlerId)
    (tokens' : List ProgressToken) (sv : SignedValue ν) (bufs' : SignedBuffers ν) : StepPack ι γ π ε ν :=
  -- Verify signatures, types, and apply transport spec.
  if st.config.transportOk h bufs' = false then
    faultPack st coro (.specFault "handler spec failed") "handler spec failed"
  else
    let vk := VerificationModel.verifyKeyOf (st.config.roleSigningKey edge.sender)
    if verifySignedValue vk sv then
      if decide (valTypeOf sv.payload = T) then
        recvCommit st coro ep edge bufs' L' sv.payload tokens' dst
      else
        faultPack st coro (.typeViolation T (valTypeOf sv.payload)) "bad recv payload"
    else
      faultPack st coro (.invalidSignature edge) "invalid signature"

private def recvWithHandler {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (T : ValType) (L' : LocalType) (dst : Reg) (h : HandlerId)
    (tokens' : List ProgressToken) : StepPack ι γ π ε ν :=
  -- Consume from the buffer and handle progress tokens.
  match bufDequeue st.buffers edge with
  | none =>
      let coro' := { coro with progressTokens := tokens' }
      blockPack st coro' (.recvWait edge { sid := edge.sid, endpoint := { sid := edge.sid, role := edge.receiver } })
  | some (sv, bufs') =>
      recvAfterDequeue st coro ep edge T L' dst h tokens' sv bufs'

private def recvOnEdge {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint)
    (edge : Edge) (T : ValType) (L' : LocalType) (dst : Reg)
    (token : ProgressToken) : StepPack ι γ π ε ν :=
  -- Check edge status, handler bindings, and progress tokens.
  if edgePartitioned st edge then
    blockPack st coro (.recvWait edge token)
  else if edgeCrashed st edge then
    faultPack st coro (.specFault "edge crashed") "edge crashed"
  else
    match SessionStore.lookupHandler st.sessions edge with
    | none => faultPack st coro (.specFault "no handler bound") "no handler bound"
    | some h =>
        match consumeProgressToken coro.progressTokens token with
        | none => faultPack st coro (.noProgressToken edge) "missing progress token"
        | some tokens' => recvWithHandler st coro ep edge T L' dst h tokens'

private def recvWithEndpoint {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (ep : Endpoint) (dst : Reg) : StepPack ι γ π ε ν :=
  -- Ensure ownership and session typing before receiving.
  if owns coro ep then
    match SessionStore.lookupType st.sessions ep with
    | some (.recv r T L') =>
        let edge := edgeFrom r ep
        let token := { sid := edge.sid, endpoint := { sid := edge.sid, role := edge.receiver } }
        recvOnEdge st coro ep edge T L' dst token
    | _ => faultPack st coro (.specFault "recv not permitted") "recv not permitted"
  else
    faultPack st coro (.channelClosed ep) "endpoint not owned"


def stepReceive {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (chan dst : Reg) : StepPack ι γ π ε ν :=
  -- Decode operands then delegate to the receive pipeline.
  match readReg coro.regs chan with
  | some (.chan ep) => recvWithEndpoint st coro ep dst
  | some v => faultPack st coro (.typeViolation (.chan 0 "") (valTypeOf v)) "bad recv channel"
  | none => faultPack st coro .outOfRegisters "missing recv channel"

/-! ## Offer semantics -/

private def offerUpdate {ν : Type u} [VerificationModel ν]
    (sessions : SessionStore ν) (ep : Endpoint) (edge : Edge)
    (bufs' : SignedBuffers ν) (L' : LocalType) : SessionStore ν :=
  -- Update buffers, trace, and local type after an offer.
  let sessions1 := updateSessBuffers sessions ep.sid bufs'
  let trace := SessionStore.lookupTrace sessions1 edge
  let sessions2 := SessionStore.updateTrace sessions1 edge (trace ++ [.string])
  SessionStore.updateType sessions2 ep L'

private def offerCommit {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (bufs' : SignedBuffers ν) (L' : LocalType) (lbl : Label) : StepPack ι γ π ε ν :=
  -- Commit a successful offer to state and trace.
  let sessions' := offerUpdate st.sessions ep edge bufs' L'
  let st' := { st with buffers := bufs', sessions := sessions' }
  continuePack st' coro (some (.obs (.offered edge lbl)))

private def offerAfterEnqueue {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (L' : LocalType) (lbl : Label) (h : HandlerId)
    (res : SignedEnqueueResult) (bufs' : SignedBuffers ν) : StepPack ι γ π ε ν :=
  -- Resolve enqueue results and enforce transport checks.
  match res with
  | .ok =>
      if st.config.transportOk h bufs' = false then
        faultPack st coro (.specFault "handler spec failed") "handler spec failed"
      else
        offerCommit st coro ep edge bufs' L' lbl
  | .blocked =>
      blockPack st coro (.sendWait edge)
  | .dropped =>
      faultPack st coro (.flowViolation "buffer drop") "buffer drop"
  | .error =>
      faultPack st coro (.flowViolation "buffer overflow") "buffer overflow"

private def offerOnHandler {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (L' : LocalType) (lbl : Label) (h : HandlerId) : StepPack ι γ π ε ν :=
  -- Sign and enqueue the label payload.
  let v := Value.string lbl
  let signed := signValue (st.config.roleSigningKey ep.role) v
  let cfg := st.config.bufferConfig edge
  let (res, bufs') := bufEnqueue cfg st.buffers edge signed
  offerAfterEnqueue st coro ep edge L' lbl h res bufs'

private def offerOnEdge {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint)
    (edge : Edge) (L' : LocalType) (lbl : Label) : StepPack ι γ π ε ν :=
  -- Validate edge status and handler binding.
  if edgePartitioned st edge then
    blockPack st coro (.sendWait edge)
  else if edgeCrashed st edge then
    faultPack st coro (.specFault "edge crashed") "edge crashed"
  else
    match SessionStore.lookupHandler st.sessions edge with
    | none => faultPack st coro (.specFault "no handler bound") "no handler bound"
    | some h => offerOnHandler st coro ep edge L' lbl h

private def offerWithEndpoint {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (lbl : Label) : StepPack ι γ π ε ν :=
  -- Ensure ownership and session typing before offering.
  if owns coro ep then
    match SessionStore.lookupType st.sessions ep with
    | some (.select r choices) =>
        match choices.find? (fun p => p.fst == lbl) with
        | none => faultPack st coro (.unknownLabel lbl) "unknown label"
        | some (_, L') => offerOnEdge st coro ep (edgeTo ep r) L' lbl
    | _ => faultPack st coro (.specFault "offer not permitted") "offer not permitted"
  else
    faultPack st coro (.channelClosed ep) "endpoint not owned"


def stepOffer {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (chan : Reg) (lbl : Label) : StepPack ι γ π ε ν :=
  -- Decode operands then delegate to the offer pipeline.
  match readReg coro.regs chan with
  | some (.chan ep) => offerWithEndpoint st coro ep lbl
  | some v => faultPack st coro (.typeViolation (.chan 0 "") (valTypeOf v)) "bad offer channel"
  | none => faultPack st coro .outOfRegisters "missing offer channel"

/-! ## Choose semantics -/

private def chooseCommit {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (bufs' : SignedBuffers ν) (L' : LocalType) (pc' : PC) (lbl : Label) : StepPack ι γ π ε ν :=
  -- Commit a successful choose to state, trace, and pc.
  let sessions1 := updateSessBuffers st.sessions ep.sid bufs'
  let trace := SessionStore.lookupTrace sessions1 edge
  let trace' := match trace with | [] => [] | _ :: ts => ts
  let sessions2 := SessionStore.updateTrace sessions1 edge trace'
  let sessions3 := SessionStore.updateType sessions2 ep L'
  let st' := { st with buffers := bufs', sessions := sessions3 }
  let coro' := { coro with pc := pc', status := .ready }
  pack coro' st' (mkRes .continue (some (.obs (.chose edge lbl))))

private def chooseAfterDequeue {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (choices : List (Label × LocalType)) (table : List (Label × PC))
    (h : HandlerId) (sv : SignedValue ν) (bufs' : SignedBuffers ν) : StepPack ι γ π ε ν :=
  -- Verify signatures, types, and select the branch.
  if st.config.transportOk h bufs' = false then
    faultPack st coro (.specFault "handler spec failed") "handler spec failed"
  else
    let vk := VerificationModel.verifyKeyOf (st.config.roleSigningKey edge.sender)
    if verifySignedValue vk sv then
      match sv.payload with
      | .string lbl =>
          match choices.find? (fun p => p.fst == lbl), table.find? (fun p => p.1 == lbl) with
          | some (_, L'), some (_, pc') => chooseCommit st coro ep edge bufs' L' pc' lbl
          | _, _ =>
              let st' := { st with buffers := bufs', sessions := updateSessBuffers st.sessions ep.sid bufs' }
              faultPack st' coro (.unknownLabel lbl) "unknown label"
      | _ =>
          let st' := { st with buffers := bufs', sessions := updateSessBuffers st.sessions ep.sid bufs' }
          faultPack st' coro (.typeViolation .string (valTypeOf sv.payload)) "bad label payload"
    else
      faultPack st coro (.invalidSignature edge) "invalid signature"

private def chooseWithHandler {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (choices : List (Label × LocalType)) (table : List (Label × PC)) (h : HandlerId)
    (token : ProgressToken) : StepPack ι γ π ε ν :=
  -- Dequeue a label and process the branch selection.
  match bufDequeue st.buffers edge with
  | none => blockPack st coro (.recvWait edge token)
  | some (sv, bufs') => chooseAfterDequeue st coro ep edge choices table h sv bufs'

private def chooseOnEdge {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (choices : List (Label × LocalType)) (table : List (Label × PC)) (token : ProgressToken) : StepPack ι γ π ε ν :=
  -- Check edge status and handler bindings before choosing.
  if edgePartitioned st edge then
    blockPack st coro (.recvWait edge token)
  else if edgeCrashed st edge then
    faultPack st coro (.specFault "edge crashed") "edge crashed"
  else
    match SessionStore.lookupHandler st.sessions edge with
    | none => faultPack st coro (.specFault "no handler bound") "no handler bound"
    | some h => chooseWithHandler st coro ep edge choices table h token

private def chooseWithEndpoint {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (ep : Endpoint) (table : List (Label × PC)) : StepPack ι γ π ε ν :=
  -- Ensure ownership and session typing before choosing.
  if owns coro ep then
    match SessionStore.lookupType st.sessions ep with
    | some (.branch r choices) =>
        let edge := edgeFrom r ep
        let token := { sid := edge.sid, endpoint := { sid := edge.sid, role := edge.receiver } }
        chooseOnEdge st coro ep edge choices table token
    | _ => faultPack st coro (.specFault "choose not permitted") "choose not permitted"
  else
    faultPack st coro (.channelClosed ep) "endpoint not owned"


def stepChoose {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (chan : Reg) (table : List (Label × PC)) : StepPack ι γ π ε ν :=
  -- Decode operands then delegate to the choose pipeline.
  match readReg coro.regs chan with
  | some (.chan ep) => chooseWithEndpoint st coro ep table
  | some v => faultPack st coro (.typeViolation (.chan 0 "") (valTypeOf v)) "bad choose channel"
  | none => faultPack st coro .outOfRegisters "missing choose channel"
