import Std
import Runtime.ProtocolMachine.Model.Core
import Runtime.ProtocolMachine.Model.SemanticObjects.OutstandingEffects
import Runtime.ProtocolMachine.Model.OutputCondition
import Runtime.ProtocolMachine.Model.Config
import Runtime.ProtocolMachine.Model.Domain
import Runtime.ProtocolMachine.Model.Knowledge
import Runtime.ProtocolMachine.Model.Program
import Runtime.ProtocolMachine.Runtime.Monitor
import Runtime.Resources.Arena
import Runtime.Resources.ResourceModel
import Runtime.ProtocolMachine.Model.State.Core
/-! # protocol machine Runtime State
The mutable state of a running protocol machine instance. Defines per-coroutine state (`CoroutineState`
with registers, program counter, owned endpoints, progress tokens, knowledge set, cost
budget, and speculation state), blocking and fault reasons, observable and internal events,
execution result containers, scheduler bookkeeping (`SchedState`), and the top-level
`ProtocolMachineState` record that ties everything together.
`ProtocolMachineState` holds the configuration, loaded programs, coroutine array, signed buffers,
persistent state, session store, scoped resource states, guard resources, the session
monitor, the observable trace, failure model state (crashed sites, partitioned edges),
and reserved fields for ghost sessions and progress supply.
This is the Lean specification of state that will be reimplemented in Rust. The
`WFVMState` predicate captures basic well-formedness (PC bounds, session id validity). -/
/-
The Problem. The protocol machine executes multiple concurrent coroutines, each with its own
registers, program counter, owned endpoints, and cost budget. We need a state
representation that captures all runtime information for execution, scheduling,
monitoring, and failure handling.
Solution Structure. Defines `CoroutineState` for per-coroutine state (registers, PC,
endpoints, knowledge set, speculation). `ProtocolMachineState` aggregates coroutines with global
state: configuration, loaded programs, session store, scheduler state, failure model.
`WFVMState` predicate captures well-formedness invariants (PC bounds, session validity).
-/
set_option autoImplicit false
universe u
/-! ## Scheduler state -/
abbrev SchedQueue := List CoroutineId -- FIFO queue of runnable coroutines.
abbrev BlockedSet (γ : Type u) := Std.HashMap CoroutineId (BlockReason γ)
abbrev OwnershipKey := SessionId × Role
abbrev LaneQueue := SchedQueue
abbrev LaneOfMap := Std.HashMap CoroutineId LaneId
abbrev LaneQueueMap := Std.HashMap LaneId LaneQueue
abbrev LaneBlockedMap (γ : Type u) := Std.HashMap LaneId (BlockedSet γ)
/-! ## Scheduler state: handoff metadata -/
structure CrossLaneHandoff where
  fromCoro : CoroutineId
  toCoro : CoroutineId
  fromLane : LaneId
  toLane : LaneId
  step : Nat
  reason : String
  delegationWitness : String := ""
  deriving Repr
/-- Metadata for a persisted checkpoint used by deterministic restart/replay. -/
structure CheckpointMeta where
  checkpointId : Nat
  tick : Nat
  sessionAnchor : Option SessionId := none
  digest : String := ""
  deriving Repr, DecidableEq, Inhabited
/-- Restart anchor into a previously recorded checkpoint. -/
structure RestartAnchor where
  checkpointId : Nat
  restartTick : Nat
  reason : String := ""
  deriving Repr, DecidableEq, Inhabited
/-- Deterministic trace tags for topology/failure/recovery ingress events. -/
inductive FailureTraceTag where
  | topology
  | failure
  | recovery
  | reconciliation
  deriving Repr, DecidableEq, Inhabited
/-- Deterministic ingress-trace event for topology/failure/recovery updates. -/
structure FailureTraceEvent where
  tick : Nat
  seqNo : Nat
  tag : FailureTraceTag
  detail : String
  deriving Repr, DecidableEq, Inhabited
/-! ## Scheduler state: structured error taxonomy -/
/-- Commit certainty level used by structured error reporting. -/
inductive ErrorCertainty where
  | certain
  | boundedDiff
  | unknown
  deriving Repr, DecidableEq, Inhabited
/-- Recovery-action tag used by structured error reporting. -/
inductive ErrorActionTag where
  | continue
  | retryAfter
  | closeSession
  | quarantineEdge
  | reconcileThenRetry
  | abort
  deriving Repr, DecidableEq, Inhabited
/-- Structured error event retained for deterministic cross-target diagnostics. -/
structure StructuredErrorEvent where
  tick : Nat
  seqNo : Nat
  faultClass : String
  certainty : ErrorCertainty
  action : ErrorActionTag
  evidenceId : Nat
  detail : String
  deriving Repr, DecidableEq, Inhabited
/-! ## Communication replay-consumption state -/
inductive CommunicationStepKind where
  | send
  | receive
  | offer
  | choose
  deriving Repr, DecidableEq, Inhabited
def communicationIdentityDomainTag : String :=
  "telltale.comm.identity.v1"
structure CommunicationIdentity where
  domainTag : String := communicationIdentityDomainTag
  sid : SessionId
  sender : Role
  receiver : Role
  stepKind : CommunicationStepKind
  label : Label
  payloadDigest : String
  seqNo : Nat
  deriving Repr, DecidableEq, Inhabited
structure CommunicationConsumeArtifact where
  tick : Nat
  identity : CommunicationIdentity
  mode : CommunicationReplayMode
  preRoot : String
  postRoot : String
  deriving Repr, DecidableEq, Inhabited
/-! ## Scheduler state: runtime record -/
structure SchedState (γ : Type u) where
  policy : SchedPolicy
  readyQueue : SchedQueue
  blockedSet : BlockedSet γ
  ownershipIndex : Std.HashMap OwnershipKey LaneId := {}
  laneOf : LaneOfMap := {}
  laneQueues : LaneQueueMap := {}
  laneBlocked : LaneBlockedMap γ := {}
  crossLaneHandoffs : List CrossLaneHandoff := []
  timeslice : Nat
  stepCount : Nat
/-! ## protocol machine state -/
structure ProtocolMachineState (ι γ π ε ν : Type u) [ProtocolMachineDomain ι γ π ε ν] where
  config : ProtocolMachineConfig ι γ π ε ν
  code : Program γ ε
  programs : Array (Program γ ε)
  coroutines : Array (CoroutineState γ ε)
  buffers : SignedBuffers ν
  persistent : PersistenceModel.PState π
  nextCoroId : CoroutineId
  nextSessionId : SessionId
  arena : Arena
  sessions : SessionStore ν
  resourceStates : Std.HashMap ScopeId (ResourceState ν) -- Scoped resource views.
  guardResources : List (γ × GuardLayer.Resource γ)
  sched : SchedState γ
  monitor : SessionMonitor γ
  obsTrace : List (TickedObsEvent ε)
  outputConditionChecks : List OutputConditionCheck := []
  clock : Nat
  crashedSites : List (IdentityModel.SiteId ι)
  partitionedEdges : List Edge
  checkpointLog : List CheckpointMeta := []
  restartAnchor : Option RestartAnchor := none
  /-- The canonical semantic owners mirrored by both Rust backends. -/
  outstandingEffects : List Runtime.ProtocolMachine.Model.OutstandingEffect := []
  operationInstances : List Runtime.ProtocolMachine.Model.OperationInstance := []
  progressContracts : List Runtime.ProtocolMachine.Model.ProgressContract := []
  nextEffectId : Nat := 0
  /-- Raw typed observations; never a reconstructed live host owner. -/
  effectExchanges : List Runtime.ProtocolMachine.Model.EffectExchangeRecord := []
  nextEffectNonce : Nat := 0
  usedEffectNonces : List Nat := []
  needsReconciliation : Bool := false
  failureTrace : List FailureTraceEvent := []
  structuredErrorEvents : List StructuredErrorEvent := []
  nextFailureSeqNo : Nat := 0
  commNextSendSeq : List (Edge × Nat) := []
  commNextRecvSeq : List (Edge × Nat) := []
  commConsumedNullifiers : List String := []
  commConsumptionArtifacts : List CommunicationConsumeArtifact := []
  mask : Unit
  ghostSessions : GhostRuntimeState
  progressSupply : Unit
/-! ## protocol machine state helpers and invariants -/
/-- Allocate a fresh externally-visible effect nonce. -/
def allocEffectNonce {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) : Nat × ProtocolMachineState ι γ π ε ν :=
  let nonce := st.nextEffectNonce
  (nonce, { st with nextEffectNonce := nonce + 1 })
/-- Check whether an externally-visible effect nonce was already used. -/
def effectNonceUsed {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (nonce : Nat) : Bool :=
  nonce ∈ st.usedEffectNonces
/-- Register an externally-visible effect nonce as consumed (idempotency key). -/
def registerEffectNonce {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (nonce : Nat) : ProtocolMachineState ι γ π ε ν :=
  if nonce ∈ st.usedEffectNonces then
    st
  else
    { st with usedEffectNonces := nonce :: st.usedEffectNonces }
/-- Append checkpoint metadata deterministically to protocol machine state. -/
def recordCheckpointMeta {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (checkpoint : CheckpointMeta) : ProtocolMachineState ι γ π ε ν :=
  { st with checkpointLog := st.checkpointLog ++ [checkpoint] }
/-- Install/update a restart anchor for replay/recovery entry. -/
def setRestartAnchor {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (anchor : RestartAnchor) : ProtocolMachineState ι γ π ε ν :=
  { st with restartAnchor := some anchor }

/-! ## protocol machine state helpers: communication identity and sequence state -/

def communicationIdentityPayloadDigest (v : Value) : String :=
  reprStr v
/-- Receive nullifier for `ident`. Rust hashes the same preimage with its configured
`HashModel`; the model keeps the injective preimage string. -/
def communicationIdentityNullifier (scope : CommunicationNullifierIdentity)
    (ident : CommunicationIdentity) : String :=
  match scope with
  | .sequenceBound => reprStr ident
  | .contentOnly =>
      "content:" ++ reprStr (ident.domainTag, ident.sid, ident.sender, ident.receiver,
        ident.stepKind, ident.label, ident.payloadDigest)
def communicationReplayRoot {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) : String :=
  reprStr (st.commNextSendSeq, st.commNextRecvSeq, st.commConsumedNullifiers)
def commSeqLookup (entries : List (Edge × Nat)) (edge : Edge) : Nat :=
  match entries.find? (fun p => decide (p.fst = edge)) with
  | some (_, n) => n
  | none => 0
def commSeqSet (entries : List (Edge × Nat)) (edge : Edge) (next : Nat) :
    List (Edge × Nat) :=
  let rec go (xs : List (Edge × Nat)) : List (Edge × Nat) :=
    match xs with
    | [] => [(edge, next)]
    | (edge', n') :: rest =>
        if edge' = edge then
          (edge, next) :: rest
        else
          (edge', n') :: go rest
  go entries
def commAllocSendSeq {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (edge : Edge) : Nat × ProtocolMachineState ι γ π ε ν :=
  let seqNo := commSeqLookup st.commNextSendSeq edge
  let nextSend := commSeqSet st.commNextSendSeq edge (seqNo + 1)
  (seqNo, { st with commNextSendSeq := nextSend })

/-! ## protocol machine state helpers: replay-consumption transition -/

def commConsumeReceiveIdentity {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) (tick : Nat) (ident : CommunicationIdentity) :
    Except String (CommunicationConsumeArtifact × ProtocolMachineState ι γ π ε ν) :=
  let preRoot := communicationReplayRoot st
  match st.config.communicationReplayMode with
  | .off =>
      let postRoot := preRoot
      let artifact : CommunicationConsumeArtifact := {
        tick := tick, identity := ident, mode := .off, preRoot := preRoot, postRoot := postRoot
      }
      let st' := { st with commConsumptionArtifacts := st.commConsumptionArtifacts ++ [artifact] }
      .ok (artifact, st')
  | .sequence =>
      let edge : Edge := { sid := ident.sid, sender := ident.sender, receiver := ident.receiver }
      let expected := commSeqLookup st.commNextRecvSeq edge
      if ident.seqNo = expected then
        let nextRecv := commSeqSet st.commNextRecvSeq edge (expected + 1)
        let st1 := { st with commNextRecvSeq := nextRecv }
        let postRoot := communicationReplayRoot st1
        let artifact : CommunicationConsumeArtifact := {
          tick := tick
          identity := ident
          mode := .sequence
          preRoot := preRoot
          postRoot := postRoot
        }
        let st' := { st1 with commConsumptionArtifacts := st1.commConsumptionArtifacts ++ [artifact] }
        .ok (artifact, st')
      else
        .error s!"comm_replay.sequence_mismatch: expected={expected}, actual={ident.seqNo}"
  | .nullifier =>
      let nullifier :=
        communicationIdentityNullifier st.config.communicationNullifierIdentity ident
      if nullifier ∈ st.commConsumedNullifiers then
        .error "comm_replay.duplicate"
      else
        let st1 := { st with commConsumedNullifiers := st.commConsumedNullifiers ++ [nullifier] }
        let postRoot := communicationReplayRoot st1
        let artifact : CommunicationConsumeArtifact := {
          tick := tick
          identity := ident
          mode := .nullifier
          preRoot := preRoot
          postRoot := postRoot
        }
        let st' := { st1 with commConsumptionArtifacts := st1.commConsumptionArtifacts ++ [artifact] }
        .ok (artifact, st')

/-! ## protocol machine state invariants -/

/-- Well-formedness: coroutine PCs are in range and sessions are bounded. -/
def WFVMState {ι γ π ε ν : Type u} [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) : Prop :=
  (∀ i (h : i < st.coroutines.size),
    let c := st.coroutines[i]'h
    ∃ prog, st.programs[c.programId]? = some prog ∧ c.pc < prog.code.size) ∧
  (∀ s ∈ st.sessions, s.fst < st.nextSessionId) ∧
  List.Nodup st.sched.readyQueue ∧
  (∀ cid ∈ st.sched.readyQueue, cid < st.coroutines.size) ∧
  (∀ cid, st.sched.blockedSet.contains cid = true →
      cid < st.coroutines.size ∧ cid ∉ st.sched.readyQueue) ∧
  (∀ cid, st.sched.laneOf.contains cid = true → cid < st.coroutines.size) ∧
  (∀ sid, st.resourceStates.contains sid = true →
      ∃ rs, st.resourceStates.get? sid = some rs ∧ rs.scope = sid)
