import Runtime.ProtocolMachine.Semantics.ExecComm
/-! # Label Instruction Semantics (`offer` / `choose`)
Step functions for the label instructions, split out of `ExecComm.lean` (which
keeps `send`/`receive`). `offer` signs and enqueues the label `.string lbl` on
the edge buffer and emits `offered`; `choose` dequeues a label, verifies it,
consumes a progress token, and jumps through the branch table, emitting `chose`.
Both follow the same staged pipeline as send/receive. -/
set_option autoImplicit false
universe u
/-! ## Offer semantics -/
def offerUpdate {ν : Type u} [VerificationModel ν]
    (sessions : SessionStore ν) (ep : Endpoint) (edge : Edge)
    (bufs' : SignedBuffers ν) (L' : LocalType) : SessionStore ν :=
  let sessions1 := updateSessBuffers sessions ep.sid bufs'
  let trace := SessionStore.lookupTrace sessions1 edge
  let sessions2 := SessionStore.updateTrace sessions1 edge (trace ++ [.string])
  SessionStore.updateType sessions2 ep L'
def offerCommit {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (bufs' : SignedBuffers ν) (L' : LocalType) (lbl : Label) : StepPack ι γ π ε ν :=
  let sessions' := offerUpdate st.sessions ep edge bufs' L'
  let st' := { st with buffers := bufs', sessions := sessions' }
  continuePack st' coro (some (.obs (.offered edge lbl)))
def offerAfterEnqueue {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (L' : LocalType) (lbl : Label) (h : HandlerId)
    (res : SignedEnqueueResult) (bufs' : SignedBuffers ν) : StepPack ι γ π ε ν :=
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
def offerOnHandler {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (L' : LocalType) (lbl : Label) (h : HandlerId) : StepPack ι γ π ε ν :=
  let v := Value.string lbl
  let signed := signValue (st.config.roleSigningKey ep.role) v
  let cfg := st.config.bufferConfig edge
  let (res, bufs') := bufEnqueue cfg st.buffers edge signed
  offerAfterEnqueue st coro ep edge L' lbl h res bufs'
/-! ## Offer semantics: edge and endpoint dispatch -/
def offerOnEdge {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint)
    (edge : Edge) (L' : LocalType) (lbl : Label) : StepPack ι γ π ε ν :=
  if edgePartitioned st edge then
    blockPack st coro (.sendWait edge)
  else if edgeCrashed st edge then
    faultPack st coro (.specFault "edge crashed") "edge crashed"
  else
    match SessionStore.lookupHandler st.sessions edge with
    | none => faultPack st coro (.specFault "no handler bound") "no handler bound"
    | some h => offerOnHandler st coro ep edge L' lbl h
def offerWithEndpoint {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (lbl : Label) : StepPack ι γ π ε ν :=
  if owns coro ep then
    match (SessionStore.lookupType st.sessions ep).map LocalType.unfold with
    | some (.select r choices) =>
        match choices.find? (fun p => p.fst == lbl) with
        | none => faultPack st coro (.unknownLabel lbl) "unknown label"
        | some (_, L') => offerOnEdge st coro ep (edgeTo ep r) L' lbl
    | _ => faultPack st coro (.specFault "offer not permitted") "offer not permitted"
  else
    faultPack st coro (.channelClosed ep) "endpoint not owned"
/-! ## Offer semantics: instruction entrypoint -/
def stepOffer {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε)
    (chan : Reg) (lbl : Label) : StepPack ι γ π ε ν :=
  match readReg coro.regs chan with
  | some (.chan ep) => offerWithEndpoint st coro ep lbl
  | some v => faultPack st coro (.typeViolation (.chan 0 "") (valTypeOf v)) "bad offer channel"
  | none => faultPack st coro .outOfRegisters "missing offer channel"
/-! ## Choose semantics -/
def chooseCommit {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (bufs' : SignedBuffers ν) (L' : LocalType) (pc' : PC) (lbl : Label) : StepPack ι γ π ε ν :=
  let sessions1 := updateSessBuffers st.sessions ep.sid bufs'
  let trace := SessionStore.lookupTrace sessions1 edge
  let trace' := match trace with | [] => [] | _ :: ts => ts
  let sessions2 := SessionStore.updateTrace sessions1 edge trace'
  let sessions3 := SessionStore.updateType sessions2 ep L'
  let st' := { st with buffers := bufs', sessions := sessions3 }
  let coro' := { coro with pc := pc', status := .ready }
  pack coro' st' (mkRes .continue (some (.obs (.chose edge lbl))))
def chooseAfterDequeue {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (choices : List (Label × LocalType)) (table : List (Label × PC))
    (h : HandlerId) (sv : SignedValue ν) (bufs' : SignedBuffers ν) : StepPack ι γ π ε ν :=
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
/-! ## Choose semantics: dequeue and edge checks -/
def chooseWithHandler {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (choices : List (Label × LocalType)) (table : List (Label × PC)) (h : HandlerId)
    (token : ProgressToken) : StepPack ι γ π ε ν :=
  match bufDequeue st.buffers edge with
  | none => blockPack st coro (.recvWait edge token)
  | some (sv, bufs') => chooseAfterDequeue st coro ep edge choices table h sv bufs'
def chooseOnEdge {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (edge : Edge)
    (choices : List (Label × LocalType)) (table : List (Label × PC)) (token : ProgressToken) : StepPack ι γ π ε ν :=
  if edgePartitioned st edge then
    blockPack st coro (.recvWait edge token)
  else if edgeCrashed st edge then
    faultPack st coro (.specFault "edge crashed") "edge crashed"
  else
    match SessionStore.lookupHandler st.sessions edge with
    | none => faultPack st coro (.specFault "no handler bound") "no handler bound"
    | some h => chooseWithHandler st coro ep edge choices table h token
def chooseWithEndpoint {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε)
    (ep : Endpoint) (table : List (Label × PC)) : StepPack ι γ π ε ν :=
  if owns coro ep then
    match (SessionStore.lookupType st.sessions ep).map LocalType.unfold with
    | some (.branch r choices) =>
        let edge := edgeFrom r ep
        let token := { sid := edge.sid, endpoint := { sid := edge.sid, role := edge.receiver } }
        chooseOnEdge st coro ep edge choices table token
    | _ => faultPack st coro (.specFault "choose not permitted") "choose not permitted"
  else
    faultPack st coro (.channelClosed ep) "endpoint not owned"
/-! ## Choose semantics: instruction entrypoint -/
def stepChoose {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (coro : CoroutineState γ ε)
    (chan : Reg) (table : List (Label × PC)) : StepPack ι γ π ε ν :=
  match readReg coro.regs chan with
  | some (.chan ep) => chooseWithEndpoint st coro ep table
  | some v => faultPack st coro (.typeViolation (.chan 0 "") (valTypeOf v)) "bad choose channel"
  | none => faultPack st coro .outOfRegisters "missing choose channel"
