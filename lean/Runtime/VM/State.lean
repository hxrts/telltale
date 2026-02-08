import Std
import Runtime.VM.Core
import Runtime.VM.Config
import Runtime.VM.Knowledge
import Runtime.VM.Program
import Runtime.VM.Monitor
import Runtime.Resources.Arena
import Runtime.Resources.ResourceModel

/-!
# VM Runtime State

The mutable state of a running VM instance. Defines per-coroutine state (`CoroutineState`
with registers, program counter, owned endpoints, progress tokens, knowledge set, cost
budget, and speculation state), blocking and fault reasons, observable and internal events,
execution result containers, scheduler bookkeeping (`SchedState`), and the top-level
`VMState` record that ties everything together.

`VMState` holds the configuration, loaded programs, coroutine array, signed buffers,
persistent state, session store, scoped resource states, guard resources, the session
monitor, the observable trace, failure model state (crashed sites, partitioned edges),
and placeholder fields for ghost sessions and progress supply.

This is the Lean specification of state that will be reimplemented in Rust. The
`WFVMState` predicate captures basic well-formedness (PC bounds, session id validity).
-/

set_option autoImplicit false

universe u

/-! ## Coroutine state -/

abbrev NamespaceRef := String -- Opaque namespace name for guard faults.


structure ProgressToken where
  -- Token ties a session to an endpoint for liveness reasoning.
  sid : SessionId
  endpoint : Endpoint
  deriving Repr, DecidableEq

structure SpeculationState where
  -- Minimal speculation metadata (placeholder for section 17).
  ghostSid : GhostSessionId
  depth : Nat
  deriving Repr

structure HandlerSession where
  -- Internal session between a coroutine and its effect handler.
  sid : SessionId
  performer : Endpoint
  handler : Endpoint
  sessionType : LocalType
  deriving Repr

inductive BlockReason (γ : Type u) where
  -- Reasons a coroutine can block.
  | recvWait (edge : Edge) (token : ProgressToken)
  | sendWait (edge : Edge)
  | acquireDenied (layer : γ)
  | invokeWait (handler : HandlerId)
  | consensusWait (tag : Nat)
  | spawnWait
  | closeWait (sid : SessionId)
  deriving Repr

inductive Fault (γ : Type u) where
  -- Faults represent hard failures in execution.
  | typeViolation (expected actual : ValType)
  | unknownLabel (label : Label)
  | channelClosed (endpoint : Endpoint)
  | invalidSignature (edge : Edge)
  | acquireFault (layer : NamespaceRef) (msg : String)
  | invokeFault (msg : String)
  | transferFault (msg : String)
  | closeFault (msg : String)
  | specFault (msg : String)
  | flowViolation (msg : String)
  | noProgressToken (edge : Edge)
  | outOfCredits
  | outOfRegisters
  deriving Repr

inductive CoroStatus (γ : Type u) where
  -- Coroutine status for scheduling.
  | ready
  | blocked (reason : BlockReason γ)
  | done
  | faulted (err : Fault γ)
  | speculating
  deriving Repr

structure CoroutineState (γ ε : Type u) [GuardLayer γ] [EffectRuntime ε] where
  -- Per-coroutine execution state.
  id : CoroutineId
  programId : Nat
  pc : PC
  regs : RegFile
  status : CoroStatus γ
  effectCtx : EffectRuntime.EffectCtx ε
  ownedEndpoints : List Endpoint
  progressTokens : List ProgressToken
  knowledgeSet : KnowledgeSet
  costBudget : Nat
  specState : Option SpeculationState

/-! ## Execution results and events -/

inductive ObsEvent (ε : Type u) [EffectRuntime ε] where
  -- Observable events emitted by VM execution.
  | sent (edge : Edge) (val : Value) (seqNo : Nat)
  | received (edge : Edge) (val : Value) (seqNo : Nat)
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
  | tagged (fact : KnowledgeFact)
  | checked (target : Role) (permitted : Bool)

structure TickedObsEvent (ε : Type u) [EffectRuntime ε] where
  -- Observable event paired with a global or session-local tick.
  tick : Nat
  event : ObsEvent ε

inductive StepEvent (ε : Type u) [EffectRuntime ε] where
  -- Step events are either observable or internal.
  | obs (ev : ObsEvent ε)
  | internal

/-! ## Trace helpers -/

/-- Extract a session id from an observable event when present. -/
def obsSid? {ε : Type u} [EffectRuntime ε] : ObsEvent ε → Option SessionId
  | .sent edge _ _ => some edge.sid
  | .received edge _ _ => some edge.sid
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
  | .tagged _ => none
  | .checked _ _ => none

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

/-- Normalize a VM trace by assigning session-local ticks. -/
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

namespace Runtime.VM

abbrev normalizeTrace {ε : Type u} [EffectRuntime ε]
    (trace : List (TickedObsEvent ε)) : List (TickedObsEvent ε) :=
  normalizeVmTrace trace

abbrev strictTrace {ε : Type u} [EffectRuntime ε]
    (trace : List (TickedObsEvent ε)) : List (TickedObsEvent ε) :=
  trace

end Runtime.VM

inductive ExecStatus (γ : Type u) where
  -- Result status of a single instruction step.
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
  -- Execution result with optional observable event.
  status : ExecStatus γ
  event : Option (StepEvent ε)

/-! ## Scheduler state -/

abbrev SchedQueue := List CoroutineId -- FIFO queue of runnable coroutines.
abbrev BlockedSet (γ : Type u) := List (CoroutineId × BlockReason γ) -- Blocked map stub.

structure SchedState (γ : Type u) where
  -- Scheduler policy and bookkeeping queues.
  policy : SchedPolicy
  readyQueue : SchedQueue
  blockedSet : BlockedSet γ
  timeslice : Nat
  stepCount : Nat

/-! ## VM state -/

structure VMState (ι γ π ε ν : Type u) [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν] where
  -- Configuration and programs.
  config : VMConfig ι γ π ε ν
  code : Program γ ε
  programs : Array (Program γ ε)
  coroutines : Array (CoroutineState γ ε)
  buffers : SignedBuffers ν
  persistent : PersistenceModel.PState π
  nextCoroId : CoroutineId
  nextSessionId : SessionId
  arena : Arena
  sessions : SessionStore ν
  resourceStates : List (ScopeId × ResourceState ν) -- Scoped resource views.
  guardResources : List (γ × GuardLayer.Resource γ)
  sched : SchedState γ
  monitor : SessionMonitor γ
  obsTrace : List (TickedObsEvent ε)
  clock : Nat
  crashedSites : List (IdentityModel.SiteId ι)
  partitionedEdges : List Edge
  mask : Unit
  ghostSessions : Unit
  progressSupply : Unit

/-- Well-formedness: coroutine PCs are in range and sessions are bounded. -/
def WFVMState {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : Prop :=
  -- Check PC bounds (per-coroutine program) and session ids against the next counter.
  (∀ i (h : i < st.coroutines.size),
    let c := st.coroutines[i]'h
    ∃ prog, st.programs[c.programId]? = some prog ∧ c.pc < prog.code.size) ∧
  (∀ s ∈ st.sessions, s.fst < st.nextSessionId)
