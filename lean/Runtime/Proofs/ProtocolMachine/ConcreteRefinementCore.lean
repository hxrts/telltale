import Runtime.ProtocolMachine.Semantics.ExecHelpers
import Runtime.ProtocolMachine.Runtime.SchedulerStep
import Runtime.ProtocolMachine.Runtime.Runner
import Runtime.Proofs.ProtocolMachine.InstrSpec.ConfigEquivSendRecv
import Runtime.Proofs.ProtocolMachine.Scheduler
import Runtime.Proofs.SchedulerApi
import Runtime.Proofs.ConcurrencyThreaded

/-! # Runtime.Proofs.ProtocolMachine.ConcreteRefinementCore

Concrete slice records and projection helpers for the implementation-facing
protocol-machine refinement slice: coroutine/session/scheduler slices, status and
fault tags, concrete trace-event projection, and its trace-shape lemmas.
Scheduled-step projections and refinement theorems live in
`Runtime.Proofs.ProtocolMachine.ConcreteRefinement`.
-/

set_option autoImplicit false

universe u

namespace Runtime
namespace Proofs

section

variable {ι γ π ε ν : Type u}
variable [IdentityModel ι] [GuardLayer γ]
variable [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
variable [AuthTree ν] [AccumulatedSet ν]
variable [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
variable [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
variable [IdentityVerificationBridge ι ν]

structure ConcreteCoroutineSlice where
  coroId : CoroutineId
  sessionId : SessionId
  pc : PC
  statusTag : String
  ownedEndpointCount : Nat
  progressTokenCount : Nat
  deriving Repr, DecidableEq

structure ConcreteSessionSlice where
  sid : SessionId
  roleCount : Nat
  localTypeCount : Nat
  bufferEdgeCount : Nat
  bufferedMessageCount : Nat
  statusTag : String
  epoch : Nat
  deriving Repr, DecidableEq

structure ConcreteSchedulerSlice where
  readyQueue : List CoroutineId
  blocked : List (CoroutineId × String)
  stepCount : Nat
  deriving Repr, DecidableEq

structure ConcreteProtocolMachineSlice where
  coroutines : List ConcreteCoroutineSlice
  sessions : List ConcreteSessionSlice
  scheduler : ConcreteSchedulerSlice
  deriving Repr, DecidableEq

structure ConcreteTransitionSlice where
  selectedCoro : CoroutineId
  selectedPc : Nat
  selectedType : Option LocalType
  execStatusTag : String
  sessionTypeCounts : List (SessionId × Nat)
  bufferedMessageCounts : List (SessionId × Nat)
  readyQueue : List CoroutineId
  blocked : List (CoroutineId × String)
  deriving Repr

structure ConcreteTraceEvent where
  kind : String
  tick : Nat
  session : Option SessionId := none
  sender : Option String := none
  receiver : Option String := none
  label : Option String := none
  role : Option String := none
  target : Option String := none
  reason : Option String := none
  deriving Repr, DecidableEq

structure ConcreteScheduledStep where
  preState : ConcreteProtocolMachineSlice
  postState : ConcreteProtocolMachineSlice
  transition : ConcreteTransitionSlice
  event : Option ConcreteTraceEvent
  deriving Repr

def concreteCoroStatusTag : CoroStatus γ → String
  | .ready => "ready"
  | .blocked _ => "blocked"
  | .done => "done"
  | .faulted _ => "faulted"
  | .speculating => "speculating"

def concreteBlockReasonTag : BlockReason γ → String
  | .recvWait _ _ => "recv_wait"
  | .sendWait _ => "send_wait"
  | .acquireDenied _ => "acquire_denied"
  | .invokeWait _ => "invoke_wait"
  | .consensusWait _ => "consensus_wait"
  | .spawnWait => "spawn_wait"
  | .closeWait _ => "close_wait"
  | .operationAwait _ => "operation_await"

def projectConcreteCoroutineSlice (coro : CoroutineState γ ε) : ConcreteCoroutineSlice :=
  { coroId := coro.id
  , sessionId := match coro.ownedEndpoints.head? with
      | some ep => ep.sid
      | none => 0
  , pc := coro.pc
  , statusTag := concreteCoroStatusTag coro.status
  , ownedEndpointCount := coro.ownedEndpoints.length
  , progressTokenCount := coro.progressTokens.length
  }

def projectConcreteSessionSlice (entry : SessionId × SessionState ν) : ConcreteSessionSlice :=
  { sid := entry.1
  , roleCount := entry.2.roles.length
  , localTypeCount := entry.2.localTypes.length
  , bufferEdgeCount := entry.2.buffers.length
  , bufferedMessageCount := entry.2.buffers.foldl (fun acc p => acc + p.2.length) 0
  , statusTag := match entry.2.phase with
      | .opening => "draining"
      | .active => "active"
      | .closing => "draining"
      | .closed => "closed"
  , epoch := entry.2.epoch
  }

def projectConcreteSchedulerSlice (sched : SchedState γ) : ConcreteSchedulerSlice :=
  { readyQueue := sched.readyQueue
  , blocked := sched.blockedSet.toList.map (fun p => (p.1, concreteBlockReasonTag p.2))
  , stepCount := sched.stepCount
  }

def concreteExecStatusTag : ExecStatus γ → String
  | .continue => "continue"
  | .yielded => "yielded"
  | .blocked _ => "blocked"
  | .halted => "halted"
  | .faulted _ => "faulted"
  | .spawned _ => "spawned"
  | .transferred _ _ => "transferred"
  | .closed _ => "closed"
  | .forked _ => "forked"
  | .joined => "joined"
  | .aborted => "aborted"

def concreteFaultTag : Fault γ → String
  | .typeViolation expected actual =>
      s!"type_violation:{reprStr expected}->{reprStr actual}"
  | .unknownLabel lbl => s!"unknown_label:{lbl}"
  | .channelClosed ep => s!"channel_closed:{ep.role}"
  | .invalidSignature edge => s!"invalid_signature:{edge.sender}->{edge.receiver}"
  | .acquireFault _ msg => s!"acquire_fault:{msg}"
  | .invokeFault msg => s!"invoke_fault:{msg}"
  | .effectFault kind message => s!"invoke_fault:{kind}:{message}"
  | .outputCondition predicate => s!"output_condition_fault:{predicate}"
  | .transferFault msg => s!"transfer_fault:{msg}"
  | .closeFault msg => s!"close_fault:{msg}"
  | .specFault msg => s!"spec_fault:{msg}"
  | .flowViolation msg => s!"flow_violation:{msg}"
  | .noProgressToken edge => s!"no_progress_token:{edge.sender}->{edge.receiver}"
  | .outOfCredits => "out_of_credits"
  | .outOfRegisters => "out_of_registers"

def projectConcreteObsEvent?
    (tick : Nat)
    (ev : ObsEvent ε) : Option ConcreteTraceEvent :=
  match ev with
  | .sent edge val _seqNo lbl =>
      let label :=
        match lbl, val with
        | some l, _ => some l
        | none, .string s => some s
        | none, _ => none
      some
        { kind := "sent"
        , tick := tick
        , session := some edge.sid
        , sender := some edge.sender
        , receiver := some edge.receiver
        , label := label }
  | .received edge val _seqNo lbl =>
      let label :=
        match lbl, val with
        | some l, _ => some l
        | none, .string s => some s
        | none, _ => none
      some
        { kind := "received"
        , tick := tick
        , session := some edge.sid
        , sender := some edge.sender
        , receiver := some edge.receiver
        , label := label }
  | .offered edge lbl =>
      some
        { kind := "sent"
        , tick := tick
        , session := some edge.sid
        , sender := some edge.sender
        , receiver := some edge.receiver
        , label := some lbl }
  | .chose edge lbl =>
      some
        { kind := "received"
        , tick := tick
        , session := some edge.sid
        , sender := some edge.sender
        , receiver := some edge.receiver
        , label := some lbl }
  | .opened sid roles =>
      some
        { kind := "opened"
        , tick := tick
        , session := some sid
        , role := some (String.intercalate "," roles) }
  | .closed sid =>
      some
        { kind := "closed"
        , tick := tick
        , session := some sid }
  | _ => none

def projectConcreteTraceEvent?
    (tick cid : Nat)
    (status : ExecStatus γ)
    (ev : Option (StepEvent ε)) : Option ConcreteTraceEvent :=
  match ev with
  | some (.obs obs) => projectConcreteObsEvent? tick obs
  | _ =>
      match status with
      | .halted =>
          some
            { kind := "halted"
            , tick := tick
            , target := some (toString cid) }
      | .faulted err =>
          some
            { kind := "faulted"
            , tick := tick
            , target := some (toString cid)
            , reason := some (concreteFaultTag err) }
      | _ => none

theorem project_concrete_trace_event_obs
    (tick cid : Nat)
    (status : ExecStatus γ)
    (obs : ObsEvent ε) :
    projectConcreteTraceEvent? tick cid status (some (StepEvent.obs obs)) =
      projectConcreteObsEvent? tick obs := by
  simp [projectConcreteTraceEvent?]

theorem project_concrete_trace_event_none
    (tick cid : Nat)
    (status : ExecStatus γ) :
    projectConcreteTraceEvent? tick cid status (none : Option (StepEvent ε)) =
      match status with
      | .halted =>
          some
            { kind := "halted"
            , tick := tick
            , target := some (toString cid) }
      | .faulted err =>
          some
            { kind := "faulted"
            , tick := tick
            , target := some (toString cid)
            , reason := some (concreteFaultTag err) }
      | _ => none := by
  cases status <;> simp [projectConcreteTraceEvent?, concreteFaultTag]

theorem project_concrete_trace_event_internal
    (tick cid : Nat)
    (status : ExecStatus γ) :
    projectConcreteTraceEvent? tick cid status (some (StepEvent.internal : StepEvent ε)) =
      match status with
      | .halted =>
          some
            { kind := "halted"
            , tick := tick
            , target := some (toString cid) }
      | .faulted err =>
          some
            { kind := "faulted"
            , tick := tick
            , target := some (toString cid)
            , reason := some (concreteFaultTag err) }
      | _ => none := by
  cases status <;> simp [projectConcreteTraceEvent?, concreteFaultTag]

theorem append_event_none_trace_shape
    (st : ProtocolMachineState ι γ π ε ν) :
    (appendEvent st none).obsTrace = st.obsTrace := by
  simp [appendEvent]

theorem append_event_internal_trace_shape
    (st : ProtocolMachineState ι γ π ε ν) :
    (appendEvent st (some StepEvent.internal)).obsTrace = st.obsTrace := by
  simp [appendEvent]

theorem append_event_obs_trace_shape
    (st : ProtocolMachineState ι γ π ε ν)
    (obs : ObsEvent ε) :
    (appendEvent st (some (StepEvent.obs obs))).obsTrace =
      st.obsTrace ++ [{ tick := st.clock, event := obs }] := by
  simp [appendEvent]

theorem project_concrete_trace_event_obs_matches_appended_trace
    (st : ProtocolMachineState ι γ π ε ν)
    (cid : CoroutineId)
    (status : ExecStatus γ)
    (obs : ObsEvent ε) :
    projectConcreteTraceEvent? st.clock cid status (some (StepEvent.obs obs)) =
      ((appendEvent st (some (StepEvent.obs obs))).obsTrace.reverse.head?.map
        (fun ev => projectConcreteObsEvent? ev.tick ev.event)).join := by
  rw [append_event_obs_trace_shape]
  simp [project_concrete_trace_event_obs]

end

end Proofs
end Runtime
