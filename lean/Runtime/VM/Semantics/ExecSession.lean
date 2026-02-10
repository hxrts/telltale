import Protocol.Environments.Core
import Runtime.Resources.ResourceModel
import Runtime.VM.Semantics.ExecHelpers

/-! # Session Lifecycle Semantics

Step functions for `open` and `close`, plus private helpers for argument alignment,
endpoint installation, handler coverage checking, and resource/transaction construction.

`stepOpen` creates a new session: validates spatial requirements, checks that every
directed edge between roles has a bound handler, allocates fresh endpoints into
destination registers, initializes the session state (scope, roles, local types,
traces, buffers, handlers), creates a resource transaction for the session resource,
applies a persistence delta, and emits an `opened` event.

`stepClose` tears down a session endpoint: advances the epoch, clears buffers and
traces, marks the session phase as closed, consumes the session resource via a
transaction, applies the close persistence delta, removes the endpoint from the
coroutine's owned set, and emits `epochAdvanced` and `closed` events. -/

/-
The Problem. Sessions have a lifecycle (opening → active → closing → closed) that
requires coordinated initialization of endpoints, handlers, buffers, and resources.
Open and close must validate preconditions and update multiple state components
atomically.

Solution Structure. `stepOpen` validates spatial requirements and handler coverage,
allocates endpoints, initializes session state, and emits `opened`. `stepClose`
advances epoch, clears state, marks phase as closed, and emits `closed`. Helpers
`zipOpenArgs`, `writeEndpoints`, and handler checkers factor the validation logic.
-/

set_option autoImplicit false

universe u

/-! ## Session lifecycle helpers -/

private def zipOpenArgs (localTypes : List (Role × LocalType))
    (dsts : List (Role × Reg)) : Option (List (Role × LocalType × Reg)) :=
  -- Align local types with destination registers by role.
  match localTypes, dsts with
  | [], [] => some []
  | (r, lt) :: ls, (r', d) :: ds =>
      if r == r' then
        (zipOpenArgs ls ds).map (fun rest => (r, lt, d) :: rest)
      else
        none
  | _, _ => none

private def writeEndpoints (regs : RegFile) (sid : SessionId)
    (pairs : List (Role × Reg)) : Option RegFile :=
  -- Write fresh endpoints into destination registers.
  let mkEp (r : Role) : Endpoint := { sid := sid, role := r }
  let rec go (rs : List (Role × Reg)) (acc : RegFile) : Option RegFile :=
    match rs with
    | [] => some acc
    | (r, d) :: rest =>
        match setReg acc d (.chan (mkEp r)) with
        | none => none
        | some acc' => go rest acc'
  go pairs regs

private def handlerBound (handlers : List (Edge × HandlerId)) (edge : Edge) : Bool :=
  -- Check whether a handler binding exists for the edge.
  handlers.any (fun h => decide (h.fst = edge))

private def handlersCoverRoles (sid : SessionId) (roles : List Role)
    (handlers : List (Edge × HandlerId)) : Bool :=
  -- Ensure every role's self-edge is bound to some handler.
  roles.all (fun r => handlerBound handlers { sid := sid, sender := r, receiver := r })

private def allEdges (sid : SessionId) (roles : List Role) : List Edge :=
  -- Enumerate all directed edges between roles for a session.
  roles.foldl
    (fun acc r1 => acc ++ roles.map (fun r2 => { sid := sid, sender := r1, receiver := r2 }))
    []

private def handlersCoverEdges (sid : SessionId) (roles : List Role)
    (handlers : List (Edge × HandlerId)) : Bool :=
  -- Ensure every session edge is bound to some handler.
  (allEdges sid roles).all (fun e => handlerBound handlers e)

structure OpenContext (ν : Type u) [VerificationModel ν] where
  -- Derived context for session creation.
  scope : ScopeId
  payload : Value
  endpoints : List Endpoint
  localTypes : List (Endpoint × LocalType)
  edges : List Edge
  buffers : SignedBuffers ν

private def mkOpenContext {ν : Type u} [VerificationModel ν]
    (sid : SessionId) (roles : RoleSet) (triples : List (Role × LocalType × Reg))
    (bufs : SignedBuffers ν) : OpenContext ν :=
  -- Assemble the computed session context.
  let scope := { id := sid }
  let payload := Value.prod (.nat sid) (.string (String.intercalate "," roles))
  let endpoints := roles.map (fun r => { sid := sid, role := r })
  let localTypes := triples.map (fun p => ({ sid := sid, role := p.1 }, p.2.1))
  let edges := allEdges sid roles
  let buffers := signedBuffersEnsure bufs edges
  { scope := scope, payload := payload, endpoints := endpoints
  , localTypes := localTypes, edges := edges, buffers := buffers }

private def mkOpenSession {ν : Type u} [VerificationModel ν]
    (sid : SessionId) (roles : RoleSet) (ctx : OpenContext ν)
    (handlers : List (Edge × HandlerId)) : SessionState ν :=
  -- Build the session-state record for a newly opened session.
  { scope := ctx.scope
  , sid := sid
  , roles := roles
  , endpoints := ctx.endpoints
  , localTypes := ctx.localTypes
  , traces := initDEnv sid roles
  , buffers := buffersFor ctx.buffers sid
  , handlers := handlers
  , epoch := 0
  , phase := .active }

private def mkOpenResource {ν : Type u} [VerificationModel ν]
    (payload : Value) : Resource ν :=
  -- Create the V1 resource token for a new session.
  { logic := VerificationModel.hashTagged .resourceKind payload
  , label := VerificationModel.hashTagged .contentId payload
  , quantity := 1
  , value := payload
  , nonce := VerificationModel.defaultNonce
  , ckey := VerificationModel.defaultCommitmentKey
  , nullifierKey := VerificationModel.defaultNullifierKey
  , isEphemeral := false }

private def mkOpenTx {ν : Type u} [VerificationModel ν] [AccumulatedSet ν]
    (res : Resource ν) (proof : ComplianceProof ν) : Transaction ν :=
  -- Build the open transaction for a session resource.
  { created := [res]
  , consumed := []
  , deltaProof := ()
  , logicProofs := []
  , complianceProofs := [proof]
  , authorizedImbalance := true }

private def openCommit {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (sid : SessionId)
    (ctx : OpenContext ν) (sess : SessionState ν) (tx : Transaction ν) : StepPack ι γ π ε ν :=
  -- Apply the resource transaction and persist the session.
  match applyTransactionAtScope st.resourceStates ctx.scope tx with
  | none =>
      faultPack st coro (.specFault "resource transaction failed") "resource transaction failed"
  | some resources' =>
      let persist' := PersistenceModel.apply st.persistent (PersistenceModel.openDelta sid)
      let st' :=
        { st with nextSessionId := st.nextSessionId + 1
                , sessions := (sid, sess) :: st.sessions
                , resourceStates := resources'
                , buffers := ctx.buffers
                , persistent := persist' }
      pack coro st' (mkRes .continue (some (.obs (.opened sid sess.roles))))

private def openWithRegs {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (sid : SessionId)
    (roles : RoleSet) (triples : List (Role × LocalType × Reg))
    (regs' : RegFile) (handlers : List (Edge × HandlerId)) : StepPack ι γ π ε ν :=
  -- Build session state, resource, and transaction for open.
  let ctx := mkOpenContext sid roles triples st.buffers
  let sess := mkOpenSession sid roles ctx handlers
  let coro' := advancePc ({ coro with regs := regs', status := .ready
                                    , ownedEndpoints := ctx.endpoints ++ coro.ownedEndpoints })
  let res := mkOpenResource ctx.payload
  let tx := mkOpenTx res (st.config.complianceProof res)
  openCommit st coro' sid ctx sess tx

private def openWithTriples {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (triples : List (Role × LocalType × Reg)) (handlers : List (Edge × HandlerId)) : StepPack ι γ π ε ν :=
  -- Validate roles and handler coverage, then write endpoints.
  let sid := st.nextSessionId
  let roles := triples.map (fun p => p.1)
  let dstRegs := triples.map (fun p => p.2.2)
  let pairs := List.zip roles dstRegs
  if st.config.spatialOk roles = false then
    faultPack st coro (.specFault "spatial requirements failed") "spatial requirements failed"
  else if !handlersCoverEdges sid roles handlers then
    faultPack st coro (.specFault "handler bindings missing") "handler bindings missing"
  else
    match writeEndpoints coro.regs sid pairs with
    | none => faultPack st coro .outOfRegisters "bad dst reg"
    | some regs' => openWithRegs st coro sid roles triples regs' handlers


def stepOpen {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (localTypes : List (Role × LocalType))
    (handlers : List (Edge × HandlerId))
    (dsts : List (Role × Reg)) : StepPack ι γ π ε ν :=
  -- Create a new session and install endpoints in registers.
  match zipOpenArgs localTypes dsts with
  | none => faultPack st coro (.closeFault "open arity mismatch") "open arity mismatch"
  | some triples => openWithTriples st coro triples handlers

/-! ## Close semantics -/

private def findEpoch {ν : Type u} [VerificationModel ν]
    (sid : SessionId) (ss : SessionStore ν) : Nat :=
  -- Lookup the epoch for the session id.
  match ss with
  | [] => 0
  | (sid', s) :: rest => if sid' = sid then s.epoch else findEpoch sid rest

private def findRoles {ν : Type u} [VerificationModel ν]
    (sid : SessionId) (ss : SessionStore ν) : RoleSet :=
  -- Lookup the role set for the session id.
  match ss with
  | [] => []
  | (sid', s) :: rest => if sid' = sid then s.roles else findRoles sid rest

private def closeSess {ν : Type u} [VerificationModel ν]
    (sid : SessionId) (epoch' : Nat) (ss : SessionStore ν) : SessionStore ν :=
  -- Mark the matching session closed and clear buffers/traces.
  let updatePhase (s : SessionState ν) : SessionState ν :=
    { s with phase := .closed, buffers := [], traces := (∅ : DEnv), epoch := epoch' }
  match ss with
  | [] => []
  | (sid', s) :: rest =>
      if _h : sid' = sid then
        (sid', updatePhase s) :: rest
      else
        (sid', s) :: closeSess sid epoch' rest

private def mkCloseResource {ν : Type u} [VerificationModel ν]
    (payload : Value) : Resource ν :=
  -- Create the V1 resource token for a session close.
  { logic := VerificationModel.hashTagged .resourceKind payload
  , label := VerificationModel.hashTagged .contentId payload
  , quantity := 1
  , value := payload
  , nonce := VerificationModel.defaultNonce
  , ckey := VerificationModel.defaultCommitmentKey
  , nullifierKey := VerificationModel.defaultNullifierKey
  , isEphemeral := false }

private def mkCloseTx {ν : Type u} [VerificationModel ν] [AccumulatedSet ν]
    (res : Resource ν) (proof : ComplianceProof ν) : Transaction ν :=
  -- Build the close transaction for a session resource.
  { created := []
  , consumed := [res]
  , deltaProof := ()
  , logicProofs := []
  , complianceProofs := [proof]
  , authorizedImbalance := true }

private def closeCommit {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint)
    (epoch' : Nat) (tx : Transaction ν) : StepPack ι γ π ε ν :=
  -- Apply the close transaction and update state.
  match applyTransactionAtScope st.resourceStates { id := ep.sid } tx with
  | none =>
      faultPack st coro (.closeFault "resource transaction failed") "resource transaction failed"
  | some resources' =>
      let persist' := PersistenceModel.apply st.persistent (PersistenceModel.closeDelta ep.sid)
      let st' := { st with sessions := closeSess ep.sid epoch' st.sessions
                          , resourceStates := resources'
                          , persistent := persist' }
      let st'' := appendEvent st' (some (StepEvent.obs (.epochAdvanced ep.sid epoch')))
      let owned' := coro.ownedEndpoints.filter (fun e => decide (e ≠ ep))
      let coro' := advancePc { coro with status := .ready, ownedEndpoints := owned' }
      pack coro' st'' (mkRes .continue (some (.obs (.closed ep.sid))))

private def closeWithEndpoint {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) : StepPack ι γ π ε ν :=
  -- Prepare resources and commit the close step.
  let epoch' := findEpoch ep.sid st.sessions + 1
  let roles := findRoles ep.sid st.sessions
  let payload := Value.prod (.nat ep.sid) (.string (String.intercalate "," roles))
  let res := mkCloseResource payload
  let tx := mkCloseTx res (st.config.complianceProof res)
  closeCommit st coro ep epoch' tx


def stepClose {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (session : Reg) : StepPack ι γ π ε ν :=
  -- Close a session endpoint and clear its buffers.
  match readReg coro.regs session with
  | some (.chan ep) =>
      if owns coro ep then
        closeWithEndpoint st coro ep
      else
        faultPack st coro (.closeFault "endpoint not owned") "endpoint not owned"
  | some v =>
      faultPack st coro (.typeViolation (.chan 0 "") (valTypeOf v)) "bad close operand"
  | none =>
      faultPack st coro .outOfRegisters "missing close operand"
