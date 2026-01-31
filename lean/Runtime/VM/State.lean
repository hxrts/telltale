import Std
import Runtime.VM.Core
import Runtime.VM.Config
import Runtime.VM.Program
import Runtime.Monitor.UnifiedMonitor
import Runtime.Resources.Arena

/-
The Problem. Specify the runtime state and execution outcomes for the
session-type VM in a form that can be reimplemented in Rust.

Solution Structure. Define coroutine state, VM state, and result/event
containers that the instruction stepper updates.
-/

set_option autoImplicit false

universe u

/-! ## Coroutine state -/

abbrev NamespaceRef := String -- Opaque namespace name for guard faults.

abbrev KnowledgeFact := String -- Atom for knowledge tracking.
abbrev KnowledgeSet := List KnowledgeFact -- Snapshot of learned facts.

structure ProgressToken where
  -- Token ties a session to an endpoint for liveness reasoning.
  sid : SessionId
  endpoint : Endpoint
  deriving Repr

structure SpeculationState where
  -- Minimal speculation metadata (placeholder for section 17).
  ghostSid : GhostSessionId
  depth : Nat
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

structure CoroutineState (γ ε : Type u) [GuardLayer γ] [EffectModel ε] where
  -- Per-coroutine execution state.
  id : CoroutineId
  pc : PC
  regs : RegFile
  status : CoroStatus γ
  effectCtx : EffectModel.EffectCtx ε
  ownedEndpoints : List Endpoint
  progressTokens : List ProgressToken
  knowledgeSet : KnowledgeSet
  costBudget : Nat
  specState : Option SpeculationState

/-! ## Execution results and events -/

inductive StepEvent where
  -- Step events used by the VM trace (placeholder; refined in Task 11).
  | send (edge : Edge) (label : Label) (val : Value)
  | recv (edge : Edge) (label : Label) (val : Value)
  | open (sid : SessionId)
  | close (sid : SessionId)
  | fault (msg : String)
  deriving Repr

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

structure ExecResult (γ : Type u) where
  -- Execution result with optional observable event.
  status : ExecStatus γ
  event : Option StepEvent
  deriving Repr

/-! ## Scheduler state -/

structure SchedState (γ : Type u) where
  -- Scheduler policy and bookkeeping queues.
  policy : SchedPolicy
  readyQueue : List CoroutineId
  blockedSet : List (CoroutineId × BlockReason γ)
  timeslice : Nat
  stepCount : Nat

/-! ## VM state -/

structure VMState (ι γ π ε : Type u) [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] where
  -- Configuration and programs.
  config : VMConfig ι γ π ε
  code : Program γ ε
  programs : Array (Program γ ε)
  coroutines : Array (CoroutineState γ ε)
  buffers : List (Edge × List Value)
  persistent : PersistenceModel.PState π
  nextCoroId : CoroutineId
  nextSessionId : SessionId
  arena : Arena
  sessions : SessionStore
  guardResources : List (γ × GuardLayer.Resource γ)
  sched : SchedState γ
  monitor : SessionMonitor γ
  obsTrace : List StepEvent
  mask : Unit
  ghostSessions : Unit
  progressSupply : Unit

/-- Well-formedness: coroutine PCs are in range and sessions are bounded. -/
def WFVMState {ι γ π ε : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    (st : VMState ι γ π ε) : Prop :=
  -- Check PC bounds and session ids against the next counter.
  (∀ i (h : i < st.coroutines.size),
    (st.coroutines[i]'h).pc < st.code.code.size) ∧
  (∀ s ∈ st.sessions, s.fst < st.nextSessionId)
