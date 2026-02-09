import Std
import Runtime.VM.Model.State

/-!
# Execution Helpers

Shared utility functions used by all per-instruction step functions. Organized into:

- **Buffer helpers**: signed-value enqueue/dequeue, edge lookup, buffer-config capacity,
  latest-value and FIFO modes with backpressure policy.
- **Guard resource helpers**: lookup and update guard-layer resources by layer tag.
- **Resource state helpers**: default state construction, scoped transaction application,
  session buffer refresh.
- **Persistence helpers**: session reconstruction from persistent state.
- **Register helpers**: safe read/write, PC advancement, endpoint ownership check,
  progress token consumption, value type recovery.
- **Result helpers**: `StepPack` construction for continue/fault/block/halt outcomes,
  cost charging.
- **Coroutine updates**: write-back of modified coroutine state into the VM state array.

Every `Exec*.lean` file imports this module. The helpers are intentionally small and
pure so that the per-instruction semantics files stay focused on control flow.
-/

set_option autoImplicit false

universe u

/-! ## Helper bundles -/

structure StepPack (ι γ π ε ν : Type u)
    [IdentityModel ι] [GuardLayer γ] [PersistenceModel π] [EffectRuntime ε]
    [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν] where
  -- Bundle updated coroutine/state/result from a single step.
  coro : CoroutineState γ ε
  st : VMState ι γ π ε ν
  res : ExecResult γ ε

/-! ## Buffer helpers -/

def signValue {ν : Type u} [VerificationModel ν]
    (sk : VerificationModel.SigningKey ν) (v : Value) : SignedValue ν :=
  -- Create a signed payload using the verification model.
  { payload := v, signature := VerificationModel.sign sk v }

def verifySignedValue {ν : Type u} [VerificationModel ν]
    (vk : VerificationModel.VerifyKey ν) (sv : SignedValue ν) : Bool :=
  -- Check the signature against the payload.
  VerificationModel.verifySignature vk sv.payload sv.signature

def edgeOf (ep : Endpoint) : Edge :=
  -- Build a self-edge for single-endpoint buffering.
  { sid := ep.sid, sender := ep.role, receiver := ep.role }

def edgeTo (ep : Endpoint) (target : Role) : Edge :=
  -- Build a directed edge from this endpoint to a target role.
  { sid := ep.sid, sender := ep.role, receiver := target }

def edgeFrom (sender : Role) (ep : Endpoint) : Edge :=
  -- Build a directed edge to this endpoint from a sender.
  { sid := ep.sid, sender := sender, receiver := ep.role }

def edgePartitioned {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (edge : Edge) : Bool :=
  -- An edge is partitioned when it appears in the VM state.
  st.partitionedEdges.any (fun e => decide (e = edge))

def edgeCrashed {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (edge : Edge) : Bool :=
  -- An edge is crashed if either endpoint maps to a crashed site.
  let _ : DecidableEq (IdentityModel.SiteId ι) := IdentityModel.decEqS (ι:=ι)
  let senderCrashed :=
    match IdentityModel.siteOf (ι:=ι) edge.sender with
    | some sid => decide (sid ∈ st.crashedSites)
    | none => false
  let receiverCrashed :=
    match IdentityModel.siteOf (ι:=ι) edge.receiver with
    | some sid => decide (sid ∈ st.crashedSites)
    | none => false
  senderCrashed || receiverCrashed

def bufDequeue {ν : Type u} [VerificationModel ν]
    (bufs : SignedBuffers ν) (edge : Edge) :
    Option (SignedValue ν × SignedBuffers ν) :=
  -- Remove the oldest signed value for the edge, if any.
  match bufs with
  | [] => none
  | (e, vs) :: rest =>
      if _h : e = edge then
        match vs with
        | [] => none
        | v :: vs' => some (v, (e, vs') :: rest)
      else
        match bufDequeue rest edge with
        | none => none
        | some (v, rest') => some (v, (e, vs) :: rest')

def buffersFor {ν : Type u} [VerificationModel ν]
    (bufs : SignedBuffers ν) (sid : SessionId) :
    SignedBuffers ν :=
  -- Project signed buffers for a given session id.
  bufs.filter (fun p => decide (p.fst.sid = sid))

/-! ## Signed buffer helpers -/

inductive SignedEnqueueResult where
  -- Outcomes for signed-buffer enqueue operations.
  | ok
  | blocked
  | dropped
  | error
  deriving Repr, DecidableEq

def signedBufferLookup {ν : Type u} [VerificationModel ν]
    (bufs : SignedBuffers ν) (edge : Edge) : SignedBuffer ν :=
  -- Lookup a signed buffer by edge (default empty).
  match bufs with
  | [] => []
  | (e, vs) :: rest => if decide (e = edge) then vs else signedBufferLookup rest edge

def signedBufferFind? {ν : Type u} [VerificationModel ν]
    (bufs : SignedBuffers ν) (edge : Edge) : Option (SignedBuffer ν) :=
  -- Lookup a signed buffer by edge (option form).
  match bufs with
  | [] => none
  | (e, vs) :: rest => if decide (e = edge) then some vs else signedBufferFind? rest edge

def signedBufferSet {ν : Type u} [VerificationModel ν]
    (bufs : SignedBuffers ν) (edge : Edge) (trace : SignedBuffer ν) :
    SignedBuffers ν :=
  -- Replace or insert the signed buffer for an edge.
  match bufs with
  | [] => [(edge, trace)]
  | (e, vs) :: rest =>
      if decide (e = edge) then
        (e, trace) :: rest
      else
        (e, vs) :: signedBufferSet rest edge trace

def signedBufferEnsure {ν : Type u} [VerificationModel ν]
    (bufs : SignedBuffers ν) (edge : Edge) : SignedBuffers ν :=
  -- Ensure an empty buffer entry exists for the edge.
  match signedBufferFind? bufs edge with
  | some _ => bufs
  | none => (edge, []) :: bufs

def signedBuffersEnsure {ν : Type u} [VerificationModel ν]
    (bufs : SignedBuffers ν) (edges : List Edge) : SignedBuffers ν :=
  -- Ensure empty entries for a list of edges.
  edges.foldl (fun acc e => signedBufferEnsure acc e) bufs

def bufferEffectiveCapacity (cfg : BufferConfig) : Nat :=
  -- V1 treats resize as "preallocated to max".
  match cfg.policy with
  | .resize maxCap => maxCap
  | _ => BufferConfig.capacity cfg

def bufEnqueue {ν : Type u} [VerificationModel ν]
    (cfg : BufferConfig) (bufs : SignedBuffers ν) (edge : Edge)
    (v : SignedValue ν) : SignedEnqueueResult × SignedBuffers ν :=
  -- Enqueue a signed value with backpressure policy.
  match cfg.mode with
  | .latestValue =>
      (SignedEnqueueResult.ok, signedBufferSet bufs edge [v])
  | .fifo =>
      let trace := signedBufferLookup bufs edge
      let cap := bufferEffectiveCapacity cfg
      if trace.length < cap then
        (SignedEnqueueResult.ok, signedBufferSet bufs edge (trace ++ [v]))
      else
        match cfg.policy with
        | .block => (SignedEnqueueResult.blocked, bufs)
        | .drop => (SignedEnqueueResult.dropped, bufs)
        | .error => (SignedEnqueueResult.error, bufs)
        | .resize _ => (SignedEnqueueResult.blocked, bufs)

/-! ## Guard resource helpers -/

def guardResourceLookup {γ : Type u} [GuardLayer γ]
    (rs : List (γ × GuardLayer.Resource γ)) (layer : γ) :
    Option (GuardLayer.Resource γ) :=
  -- Lookup a guard-layer resource by layer tag.
  match rs with
  | [] => none
  | (g, r) :: rest => if decide (g = layer) then some r else guardResourceLookup rest layer

def guardResourceUpdate {γ : Type u} [GuardLayer γ]
    (rs : List (γ × GuardLayer.Resource γ)) (layer : γ)
    (f : GuardLayer.Resource γ → GuardLayer.Resource γ) :
    List (γ × GuardLayer.Resource γ) :=
  -- Update a guard-layer resource by layer tag.
  match rs with
  | [] => []
  | (g, r) :: rest =>
      if decide (g = layer) then
        (g, f r) :: rest
      else
        (g, r) :: guardResourceUpdate rest layer f

/-! ## Resource-state helpers -/

def defaultResourceState {ν : Type u} [VerificationModel ν] [AccumulatedSet ν]
    (scope : ScopeId) : ResourceState ν :=
  -- Empty resource state for a new scope.
  { scope := scope
  , commitments := AccumulatedSet.empty
  , nullifiers := AccumulatedSet.empty }

/-! ## Persistence helpers -/

def reconstructSession {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (sid : SessionId) :
    Option (PersistenceModel.SessionState π) :=
  -- Reconstruct a session from persistent state.
  PersistenceModel.derive st.persistent sid

def updateResourceStates {ν : Type u} [VerificationModel ν] [AccumulatedSet ν]
    (states : List (ScopeId × ResourceState ν)) (scope : ScopeId)
    (f : ResourceState ν → ResourceState ν) : List (ScopeId × ResourceState ν) :=
  -- Update or insert the resource state for a scope.
  match states with
  | [] => [(scope, f (defaultResourceState scope))]
  | (sid, st) :: rest =>
      if sid = scope then
        (sid, f st) :: rest
      else
        (sid, st) :: updateResourceStates rest scope f

def applyTransactionAtScope {ν : Type u} [VerificationModel ν] [AccumulatedSet ν]
    (states : List (ScopeId × ResourceState ν)) (scope : ScopeId)
    (tx : Transaction ν) : Option (List (ScopeId × ResourceState ν)) :=
  -- Apply a transaction to a scope, inserting default state if needed.
  match states with
  | [] =>
      match applyTransaction tx (defaultResourceState scope) with
      | some st' => some [(scope, st')]
      | none => none
  | (sid, st) :: rest =>
      if sid = scope then
        match applyTransaction tx st with
        | some st' => some ((sid, st') :: rest)
        | none => none
      else
        match applyTransactionAtScope rest scope tx with
        | some rest' => some ((sid, st) :: rest')
        | none => none

def updateSessBuffers {ν : Type u} [VerificationModel ν]
    (store : SessionStore ν) (sid : SessionId)
    (bufs : SignedBuffers ν) : SessionStore ν :=
  -- Refresh the signed buffers for a specific session.
  match store with
  | [] => []
  | (sid', s) :: rest =>
      if _h : sid' = sid then
        (sid', { s with buffers := buffersFor bufs sid }) :: rest
      else
        (sid', s) :: updateSessBuffers rest sid bufs

def appendEvent {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν)
    (ev : Option (StepEvent ε)) : VMState ι γ π ε ν :=
  -- Record an event in the observable trace.
  match ev with
  | none => st
  | some StepEvent.internal => st
  | some (StepEvent.obs e) =>
      { st with obsTrace := st.obsTrace ++ [{ tick := st.clock, event := e }] }

/-! ## Register helpers -/

def advancePc {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (coro : CoroutineState γ ε) : CoroutineState γ ε :=
  -- Advance the program counter to the next instruction.
  { coro with pc := coro.pc + 1 }

def readReg (regs : RegFile) (r : Reg) : Option Value :=
  -- Safe register read.
  regs[r]?

def setReg (regs : RegFile) (r : Reg) (v : Value) : Option RegFile :=
  -- Safe register write.
  if h : r < regs.size then
    some (regs.set (i := r) (v := v) (h := h))
  else
    none

def owns {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (c : CoroutineState γ ε) (ep : Endpoint) : Bool :=
  -- Check endpoint ownership for linear use.
  c.ownedEndpoints.any (fun e => e == ep)

def consumeProgressToken (tokens : List ProgressToken) (tok : ProgressToken) :
    Option (List ProgressToken) :=
  -- Remove a progress token if it is available.
  if tokens.contains tok then some (tokens.erase tok) else none

def valTypeOf (v : Value) : ValType :=
  -- Recover a value type for diagnostics only.
  match v with
  | .unit => .unit
  | .bool _ => .bool
  | .nat _ => .nat
  | .string _ => .string
  | .prod v1 v2 => .prod (valTypeOf v1) (valTypeOf v2)
  | .chan ep => .chan ep.sid ep.role

/-! ## Result helpers -/

def mkRes {γ ε : Type u} [EffectRuntime ε] (status : ExecStatus γ)
    (event : Option (StepEvent ε)) : ExecResult γ ε :=
  -- Build an execution result.
  { status := status, event := event }

def pack {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (coro : CoroutineState γ ε) (st : VMState ι γ π ε ν)
    (res : ExecResult γ ε) : StepPack ι γ π ε ν :=
  -- Bundle the updated coroutine, state, and result.
  { coro := coro, st := st, res := res }

def faultPack {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (err : Fault γ) (msg : String) : StepPack ι γ π ε ν :=
  -- Mark the coroutine as faulted and emit a fault event.
  let coro' := { coro with status := .faulted err }
  let _ := msg
  pack coro' st (mkRes (.faulted err) (some StepEvent.internal))

def blockPack {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (reason : BlockReason γ) : StepPack ι γ π ε ν :=
  -- Mark the coroutine as blocked without producing an event.
  let coro' := { coro with status := .blocked reason }
  pack coro' st (mkRes (.blocked reason) none)

def continuePack {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (ev : Option (StepEvent ε)) : StepPack ι γ π ε ν :=
  -- Mark the coroutine ready and continue.
  let coro' := advancePc { coro with status := .ready }
  pack coro' st (mkRes .continue ev)

def haltPack {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) : StepPack ι γ π ε ν :=
  -- Mark the coroutine as done.
  let coro' := advancePc { coro with status := .done }
  pack coro' st (mkRes .halted none)

def chargeCost {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (cfg : VMConfig ι γ π ε ν) (coro : CoroutineState γ ε)
    (i : Instr γ ε) : Option (CoroutineState γ ε) :=
  -- Deduct instruction cost from the budget when possible.
  let cost := cfg.costModel.stepCost i
  if _h : cost ≤ coro.costBudget then
    some { coro with costBudget := coro.costBudget - cost }
  else
    none

/-! ## Coroutine updates -/

def updateCoro {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coroId : CoroutineId)
    (coro : CoroutineState γ ε) : VMState ι γ π ε ν :=
  -- Update the coroutine array at the given index.
  if h : coroId < st.coroutines.size then
    { st with coroutines := st.coroutines.set (i := coroId) (v := coro) (h := h) }
  else
    st
