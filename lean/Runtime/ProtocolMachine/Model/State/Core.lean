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

/-! # protocol machine Runtime State: coroutines, events, traces
Per-coroutine state (`CoroutineState`), blocking and fault reasons, observable and
internal step events, trace helpers (`filterBySid`, `normalizeVmTrace`), and
execution status/result containers. Re-exported by `Runtime.ProtocolMachine.Model.State`. -/
set_option autoImplicit false
universe u
/-! ## Coroutine state -/
abbrev NamespaceRef := String -- Opaque namespace name for guard faults.
structure ProgressToken where
  sid : SessionId
  endpoint : Endpoint
  deriving Repr, DecidableEq
structure SpeculationState where
  ghostSid : GhostSessionId
  depth : Nat
  deriving Repr
structure ProtocolMachineGhostSession where
  ghostSid : GhostSessionId
  realSid : SessionId
  owner : CoroutineId
  projectedLocalTypes : List (Endpoint × LocalType) := []
  createdTick : Nat
  deriving Repr
structure ProtocolMachineSpeculationCheckpoint where
  ghostSid : GhostSessionId
  tick : Nat
  coroId : CoroutineId
  traceLen : Nat
  nextEffectNonce : Nat
  needsReconciliation : Bool
  deriving Repr, DecidableEq, Inhabited
abbrev ProtocolMachineGhostSessionStore := Std.HashMap GhostSessionId ProtocolMachineGhostSession
abbrev ProtocolMachineSpeculationCheckpointStore := Std.HashMap GhostSessionId ProtocolMachineSpeculationCheckpoint
structure GhostRuntimeState where
  sessions : ProtocolMachineGhostSessionStore := {}
  checkpoints : ProtocolMachineSpeculationCheckpointStore := {}
  deriving Repr, Inhabited
structure HandlerSession where
  sid : SessionId
  performer : Endpoint
  handler : Endpoint
  sessionType : LocalType
  deriving Repr
/-! ## Coroutine state: blocking and faults -/
inductive BlockReason (γ : Type u) where
  | recvWait (edge : Edge) (token : ProgressToken)
  | sendWait (edge : Edge)
  | acquireDenied (layer : γ)
  | invokeWait (handler : HandlerId)
  | consensusWait (tag : Nat)
  | spawnWait
  | closeWait (sid : SessionId)
  | operationAwait (operationId : String)
  deriving Repr
inductive Fault (γ : Type u) where
  | typeViolation (expected actual : ValType)
  | unknownLabel (label : Label)
  | channelClosed (endpoint : Endpoint)
  | invalidSignature (edge : Edge)
  | acquireFault (layer : NamespaceRef) (msg : String)
  | invokeFault (msg : String)
  /-- Actual typed semantic host failure; distinct from an application Err. -/
  | effectFault (kind message : String)
  | outputCondition (predicateRef : String)
  | transferFault (msg : String)
  | closeFault (msg : String)
  | specFault (msg : String)
  | flowViolation (msg : String)
  | noProgressToken (edge : Edge)
  | outOfCredits
  | outOfRegisters
  deriving Repr
inductive CoroStatus (γ : Type u) where
  | ready
  | blocked (reason : BlockReason γ)
  | done
  | faulted (err : Fault γ)
  | speculating
  deriving Repr
structure CoroutineState (γ ε : Type u) [GuardLayer γ] [EffectRuntime ε] where
  id : CoroutineId
  programId : Nat
  /-- Fixed role selected by the actual image entry; endpoint transfer does not change it. -/
  role : Role := ""
  pc : PC
  regs : RegFile
  status : CoroStatus γ
  effectCtx : EffectRuntime.EffectCtx ε
  ownedEndpoints : List Endpoint
  progressTokens : List ProgressToken
  knowledgeSet : KnowledgeSet
  costBudget : Nat
  specState : Option SpeculationState
  /-- Protocol occurrence only; Rust issued host handles remain runtime-only. -/
  nominalContinuation : Option Runtime.ProtocolMachine.Model.NominalCommandContinuation := none
  /-- Original owner admitted by the owning load boundary; current registry
  data cannot reconstruct this coroutine-held grant after transfer. -/
  issuedModelOwner : Option SessionTypes.ModelOwner := none
  /-- Original enclosing source operation, distinct from its host-effect children. -/
  operationContinuation : Option Runtime.ProtocolMachine.Model.OriginalOperationContinuation := none
  /-- First actual typed source-operation execution failure; independent of
  application resolution and retained even when semantic children are revoked. -/
  operationFailure : Option (Fault γ) := none

abbrev AuthorityWitnessId := Nat
abbrev FragmentOwnerId := String

inductive OwnershipTerminalReason where
  | ownerDied (ownerId : FragmentOwnerId)
  | transferAbandoned (ownerId : FragmentOwnerId) (claimId : Nat)
  | transferCommitFailed (ownerId : FragmentOwnerId) (claimId : Nat) (reason : String)
  deriving Repr, DecidableEq

inductive SessionTerminalReason where
  | closed (reason : String)
  | cancelled (reason : String)
  | aborted (reason : String)
  | faulted (reason : String)
  deriving Repr, DecidableEq

/-! ## Execution results and events -/
inductive ObsEvent (ε : Type u) [EffectRuntime ε] where
  /-- A value sent on `edge`. `label` is the session-type label when the step
  ran on a one-entry `select` (a label-only message compiled to `send`); it is
  `none` for typed value sends. Known gap: the runtime `LocalType.send` has no
  label, so value-send labels (which Rust reports from `LocalTypeR`) are not
  recorded. -/
  | sent (edge : Edge) (val : Value) (seqNo : Nat) (label : Option Label)
  /-- A value received on `edge`; `label` as for `sent` (one-entry `branch`). -/
  | received (edge : Edge) (val : Value) (seqNo : Nat) (label : Option Label)
  | offered (edge : Edge) (label : Label)
  | chose (edge : Edge) (label : Label)
  | acquired (layer : LayerId) (endpoint : Endpoint)
  | released (layer : LayerId) (endpoint : Endpoint)
  | invoked (endpoint : Endpoint) (action : EffectRuntime.EffectAction ε)
  | opened (sid : SessionId) (roles : RoleSet)
  | closed (sid : SessionId)
  | epochAdvanced (sid : SessionId) (epoch : Nat)
  | transferred (endpoint : Endpoint) (fromCoro toCoro : Nat)
  | forked (sid : SessionId) (ghostSid : GhostSessionId)
  | joined (sid : SessionId)
  | aborted (sid : SessionId)
  | sessionTerminal (sid : SessionId) (reason : SessionTerminalReason)
  | tagged (fact : Knowledge)
  | checked (target : Role) (permitted : Bool)
  | failureBranchEntered (sid : SessionId) (coroId : CoroutineId) (faultClass : String)
  | timeoutIssued (site : Site) (untilTick : Nat) (witnessId : AuthorityWitnessId)
  | cancellationRequested (sid : SessionId)
      (witnessId : AuthorityWitnessId) (ownerId : FragmentOwnerId)
      (reason : OwnershipTerminalReason)
  | cancelled (sid : SessionId) (witnessId : AuthorityWitnessId)
      (reason : OwnershipTerminalReason)
structure TickedObsEvent (ε : Type u) [EffectRuntime ε] where
  tick : Nat
  event : ObsEvent ε
inductive StepEvent (ε : Type u) [EffectRuntime ε] where
  | obs (ev : ObsEvent ε)
  | internal
/-! ## Trace helpers -/
/-- Extract a session id from an observable event when present. -/
def obsSid? {ε : Type u} [EffectRuntime ε] : ObsEvent ε → Option SessionId
  | .sent edge _ _ _ => some edge.sid
  | .received edge _ _ _ => some edge.sid
  | .offered edge _ => some edge.sid
  | .chose edge _ => some edge.sid
  | .acquired _ ep => some ep.sid
  | .released _ ep => some ep.sid
  | .invoked ep _ => some ep.sid
  | .opened sid _ => some sid
  | .closed sid => some sid
  | .epochAdvanced sid _ => some sid
  | .transferred ep _ _ => some ep.sid
  | .forked sid _ => some sid
  | .joined sid => some sid
  | .aborted sid => some sid
  | .sessionTerminal sid _ => some sid
  | .tagged _ => none
  | .checked _ _ => none
  | .failureBranchEntered sid _ _ => some sid
  | .timeoutIssued _ _ _ => none
  | .cancellationRequested sid _ _ _ => some sid
  | .cancelled sid _ _ => some sid
/-- Filter observable events by session id. -/
def filterBySid {ε : Type u} [EffectRuntime ε] (sid : SessionId)
    (trace : List (TickedObsEvent ε)) : List (TickedObsEvent ε) :=
  trace.filter (fun ev => obsSid? ev.event = some sid)
private def getTick (sid : SessionId) (ticks : List (SessionId × Nat)) : Nat :=
  match ticks.find? (fun p => decide (p.fst = sid)) with
  | some (_, t) => t
  | none => 0
private def setTick (sid : SessionId) (t : Nat) (ticks : List (SessionId × Nat)) :
    List (SessionId × Nat) :=
  let rec go (xs : List (SessionId × Nat)) : List (SessionId × Nat) :=
    match xs with
    | [] => [(sid, t)]
    | (sid', t') :: rest =>
        if sid' = sid then
          (sid, t) :: rest
        else
          (sid', t') :: go rest
  go ticks
/-! ## Trace helpers: normalization -/
/-- Normalize a protocol machine trace by assigning session-local ticks. -/
def normalizeVmTrace {ε : Type u} [EffectRuntime ε]
    (trace : List (TickedObsEvent ε)) : List (TickedObsEvent ε) :=
  let step :=
    fun (acc : List (TickedObsEvent ε) × List (SessionId × Nat)) (ev : TickedObsEvent ε) =>
      match obsSid? ev.event with
      | some sid =>
          let t := getTick sid acc.2
          let ticks' := setTick sid (t + 1) acc.2
          ({ tick := t, event := ev.event } :: acc.1, ticks')
      | none =>
          (ev :: acc.1, acc.2)
  let (revTrace, _) := trace.foldl step ([], [])
  revTrace.reverse
namespace Runtime.ProtocolMachine
abbrev normalizeTrace {ε : Type u} [EffectRuntime ε]
    (trace : List (TickedObsEvent ε)) : List (TickedObsEvent ε) :=
  normalizeVmTrace trace
abbrev strictTrace {ε : Type u} [EffectRuntime ε]
    (trace : List (TickedObsEvent ε)) : List (TickedObsEvent ε) :=
  trace
end Runtime.ProtocolMachine
inductive ExecStatus (γ : Type u) where
  | continue
  | yielded
  | blocked (reason : BlockReason γ)
  | halted
  | faulted (err : Fault γ)
  | spawned (newId : Nat)
  | transferred (endpoint : Endpoint) (targetId : Nat)
  | closed (sid : SessionId)
  | forked (ghostSid : GhostSessionId)
  | joined
  | aborted
  deriving Repr
structure ExecResult (γ ε : Type u) [EffectRuntime ε] where
  status : ExecStatus γ
  event : Option (StepEvent ε)
