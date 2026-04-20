import Runtime.ProtocolMachine.Semantics.ExecHelpers
import Runtime.ProtocolMachine.Runtime.SchedulerStep
import Runtime.ProtocolMachine.Runtime.Runner
import Runtime.Proofs.ProtocolMachine.InstrSpec.ConfigEquivSendRecv
import Runtime.Proofs.ProtocolMachine.Scheduler
import Runtime.Proofs.SchedulerApi
import Runtime.Proofs.ConcurrencyThreaded

/-! # Runtime.Proofs.ProtocolMachine.ConcreteRefinement

Concrete projection helpers for the first implementation-facing protocol-machine
refinement slice. The slice intentionally tracks only:

- session-local type counts
- buffered message counts
- scheduler ready / blocked state
- coroutine-local program counters and status tags

This is the smallest nontrivial state surface that the Rust runtime, Lean
runner, and threaded runtime can compare exactly today.

LONG_FILE_JUSTIFICATION: The refinement lemmas thread the same concrete slice
through multiple projection views. Splitting the file would duplicate the slice
surface and make the cross-target audit trail harder to review.
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
  | .sent edge val _seqNo =>
      let label :=
        match val with
        | .string s => some s
        | _ => none
      some
        { kind := "sent"
        , tick := tick
        , session := some edge.sid
        , sender := some edge.sender
        , receiver := some edge.receiver
        , label := label }
  | .received edge val _seqNo =>
      let label :=
        match val with
        | .string s => some s
        | _ => none
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

def projectSessionTypeCounts (sessions : SessionStore ν) : List (SessionId × Nat) :=
  sessions.map (fun entry => (entry.1, entry.2.localTypes.length))

def projectBufferedMessageCounts (sessions : SessionStore ν) : List (SessionId × Nat) :=
  sessions.map (fun entry =>
    (entry.1, entry.2.buffers.foldl (fun acc p => acc + p.2.length) 0))

def projectSelectedEndpointType?
    (st : ProtocolMachineState ι γ π ε ν) (cid : CoroutineId) : Option LocalType :=
  match st.coroutines[cid]? with
  | none => none
  | some coro =>
      match coro.regs[0]? with
      | some (Value.chan ep) => SessionStore.lookupType st.sessions ep
      | _ => none

def projectConcreteTransitionSlice
    (st : ProtocolMachineState ι γ π ε ν)
    (cid : CoroutineId)
    (status : ExecStatus γ) : ConcreteTransitionSlice :=
  { selectedCoro := cid
  , selectedPc := match st.coroutines[cid]? with | some coro => coro.pc | none => 0
  , selectedType := projectSelectedEndpointType? st cid
  , execStatusTag := concreteExecStatusTag status
  , sessionTypeCounts := projectSessionTypeCounts st.sessions
  , bufferedMessageCounts := projectBufferedMessageCounts st.sessions
  , readyQueue := st.sched.readyQueue
  , blocked := st.sched.blockedSet.toList.map (fun p => (p.1, concreteBlockReasonTag p.2))
  }

def projectConcreteProtocolMachineSlice
    (st : ProtocolMachineState ι γ π ε ν) : ConcreteProtocolMachineSlice :=
  { coroutines := st.coroutines.toList.map projectConcreteCoroutineSlice
  , sessions := st.sessions.map projectConcreteSessionSlice
  , scheduler := projectConcreteSchedulerSlice st.sched
  }

def mkConcreteScheduledStep
    (tick : Nat)
    (pre post : ProtocolMachineState ι γ π ε ν)
    (cid : CoroutineId)
    (status : ExecStatus γ)
    (ev : Option (StepEvent ε)) : ConcreteScheduledStep :=
  { preState := projectConcreteProtocolMachineSlice pre
  , postState := projectConcreteProtocolMachineSlice post
  , transition := projectConcreteTransitionSlice post cid status
  , event := projectConcreteTraceEvent? tick cid status ev
  }

def projectConcreteScheduledStep?
    (st : ProtocolMachineState ι γ π ε ν) : Option ConcreteScheduledStep :=
  match schedule st with
  | none => none
  | some (cid, stSched) =>
      let (stExec, res) := execInstr stSched cid
      let sched' := updateAfterStep stExec.sched cid res.status
      let stNext : ProtocolMachineState ι γ π ε ν := { stExec with sched := sched' }
      some (mkConcreteScheduledStep st.clock st stNext cid res.status res.event)

theorem project_concrete_scheduled_step_none_iff
    (st : ProtocolMachineState ι γ π ε ν) :
    projectConcreteScheduledStep? st = none ↔ schedule st = none := by
  cases hSched : schedule st with
  | none =>
      simp [projectConcreteScheduledStep?, hSched]
  | some pair =>
      simp [projectConcreteScheduledStep?, hSched]

theorem project_concrete_scheduled_step_some
    (st stSched stExec stNext : ProtocolMachineState ι γ π ε ν)
    (cid : CoroutineId)
    (status : ExecStatus γ)
    (ev : Option (StepEvent ε))
    (hSchedule : schedule st = some (cid, stSched))
    (hExec : execInstr stSched cid = (stExec, { status := status, event := ev }))
    (hNext : stNext = { stExec with sched := updateAfterStep stExec.sched cid status }) :
    projectConcreteScheduledStep? st =
      some (mkConcreteScheduledStep st.clock st stNext cid status ev) := by
  subst hNext
  unfold projectConcreteScheduledStep?
  simp [hSchedule, hExec]

theorem project_concrete_scheduled_step_post_state_eq_sched_step
    (st : ProtocolMachineState ι γ π ε ν) :
    Option.map ConcreteScheduledStep.postState (projectConcreteScheduledStep? st) =
      Option.map projectConcreteProtocolMachineSlice (schedStep st) := by
  unfold projectConcreteScheduledStep? schedStep
  cases hSched : schedule st with
  | none =>
      simp
  | some pair =>
      cases pair with
      | mk cid stSched =>
          cases hExec : execInstr stSched cid with
          | mk stExec res =>
              rfl

theorem project_concrete_scheduled_step_pre_state_eq_schedule_source
    (st : ProtocolMachineState ι γ π ε ν) :
    Option.map ConcreteScheduledStep.preState (projectConcreteScheduledStep? st) =
      (match schedule st with
      | none => none
      | some _ => some (projectConcreteProtocolMachineSlice st)) := by
  unfold projectConcreteScheduledStep?
  cases hSched : schedule st with
  | none =>
      simp
    | some pair =>
      cases pair with
      | mk cid stSched =>
          simp [mkConcreteScheduledStep]

theorem project_concrete_scheduled_step_transition_eq_sched_step
    (st : ProtocolMachineState ι γ π ε ν) :
    Option.map ConcreteScheduledStep.transition (projectConcreteScheduledStep? st) =
      (match schedule st with
      | none => none
      | some (cid, stSched) =>
          let (stExec, res) := execInstr stSched cid
          let sched' := updateAfterStep stExec.sched cid res.status
          let stNext : ProtocolMachineState ι γ π ε ν := { stExec with sched := sched' }
          some (projectConcreteTransitionSlice stNext cid res.status)) := by
  unfold projectConcreteScheduledStep?
  cases hSched : schedule st with
  | none =>
      simp
  | some pair =>
      cases pair with
      | mk cid stSched =>
          cases hExec : execInstr stSched cid with
          | mk stExec res =>
              rfl

theorem project_concrete_scheduled_step_event_eq_sched_step
    (st : ProtocolMachineState ι γ π ε ν) :
    Option.map ConcreteScheduledStep.event (projectConcreteScheduledStep? st) =
      (match schedule st with
      | none => none
      | some (cid, stSched) =>
          let (_stExec, res) := execInstr stSched cid
          some (projectConcreteTraceEvent? st.clock cid res.status res.event)) := by
  unfold projectConcreteScheduledStep?
  cases hSched : schedule st with
  | none =>
      simp
  | some pair =>
      cases pair with
      | mk cid stSched =>
          simp [mkConcreteScheduledStep, projectConcreteTransitionSlice]

theorem project_concrete_scheduled_step_eq_schedule_exec
    (st : ProtocolMachineState ι γ π ε ν) :
    projectConcreteScheduledStep? st =
      (match schedule st with
      | none => none
      | some (cid, stSched) =>
          let (stExec, res) := execInstr stSched cid
          let sched' := updateAfterStep stExec.sched cid res.status
          let stNext : ProtocolMachineState ι γ π ε ν := { stExec with sched := sched' }
          some (mkConcreteScheduledStep st.clock st stNext cid res.status res.event)) := by
  unfold projectConcreteScheduledStep?
  cases hSched : schedule st with
  | none =>
      simp
  | some pair =>
      cases pair with
      | mk cid stSched =>
          simp [mkConcreteScheduledStep, projectConcreteTransitionSlice]

def concreteSessionTypeCountsOfStateSlice
    (slice : ConcreteProtocolMachineSlice) : List (SessionId × Nat) :=
  slice.sessions.map (fun sess => (sess.sid, sess.localTypeCount))

def concreteBufferedMessageCountsOfStateSlice
    (slice : ConcreteProtocolMachineSlice) : List (SessionId × Nat) :=
  slice.sessions.map (fun sess => (sess.sid, sess.bufferedMessageCount))

theorem project_concrete_scheduler_slice_syncLaneViews
    (sched : SchedState γ) :
    projectConcreteSchedulerSlice (syncLaneViews sched) =
      projectConcreteSchedulerSlice sched := by
  simp [projectConcreteSchedulerSlice, syncLaneViews]

theorem project_transition_ready_queue_eq_state_slice
    (st : ProtocolMachineState ι γ π ε ν) (cid : CoroutineId) (status : ExecStatus γ) :
    (projectConcreteTransitionSlice st cid status).readyQueue =
      (projectConcreteProtocolMachineSlice st).scheduler.readyQueue := by
  rfl

theorem project_transition_selected_pc_eq_state
    (st : ProtocolMachineState ι γ π ε ν) (cid : CoroutineId) (status : ExecStatus γ) :
    (projectConcreteTransitionSlice st cid status).selectedPc =
      match st.coroutines[cid]? with
      | some coro => coro.pc
      | none => 0 := by
  rfl

theorem project_transition_selected_type_eq_lookup
    (st : ProtocolMachineState ι γ π ε ν) (cid : CoroutineId) (status : ExecStatus γ) :
    (projectConcreteTransitionSlice st cid status).selectedType =
      projectSelectedEndpointType? st cid := by
  rfl

theorem project_transition_blocked_eq_state_slice
    (st : ProtocolMachineState ι γ π ε ν) (cid : CoroutineId) (status : ExecStatus γ) :
    (projectConcreteTransitionSlice st cid status).blocked =
      (projectConcreteProtocolMachineSlice st).scheduler.blocked := by
  rfl

theorem project_transition_session_type_counts_eq_state_slice
    (st : ProtocolMachineState ι γ π ε ν) (cid : CoroutineId) (status : ExecStatus γ) :
    (projectConcreteTransitionSlice st cid status).sessionTypeCounts =
      concreteSessionTypeCountsOfStateSlice (projectConcreteProtocolMachineSlice st) := by
  simp [projectConcreteTransitionSlice, projectConcreteProtocolMachineSlice,
    concreteSessionTypeCountsOfStateSlice, projectSessionTypeCounts, projectConcreteSessionSlice]

theorem project_transition_buffered_message_counts_eq_state_slice
    (st : ProtocolMachineState ι γ π ε ν) (cid : CoroutineId) (status : ExecStatus γ) :
    (projectConcreteTransitionSlice st cid status).bufferedMessageCounts =
      concreteBufferedMessageCountsOfStateSlice (projectConcreteProtocolMachineSlice st) := by
  simp [projectConcreteTransitionSlice, projectConcreteProtocolMachineSlice,
    concreteBufferedMessageCountsOfStateSlice, projectBufferedMessageCounts,
    projectConcreteSessionSlice]

theorem project_concrete_scheduled_step_ready_queue_matches_post_state
    (st : ProtocolMachineState ι γ π ε ν) :
    Option.map (fun step => step.transition.readyQueue) (projectConcreteScheduledStep? st) =
      Option.map (fun step => step.postState.scheduler.readyQueue) (projectConcreteScheduledStep? st) := by
  unfold projectConcreteScheduledStep?
  cases hSched : schedule st with
  | none =>
      simp
  | some pair =>
      cases pair with
      | mk cid stSched =>
          simp [mkConcreteScheduledStep, project_transition_ready_queue_eq_state_slice]

theorem project_concrete_scheduled_step_blocked_matches_post_state
    (st : ProtocolMachineState ι γ π ε ν) :
    Option.map (fun step => step.transition.blocked) (projectConcreteScheduledStep? st) =
      Option.map (fun step => step.postState.scheduler.blocked) (projectConcreteScheduledStep? st) := by
  unfold projectConcreteScheduledStep?
  cases hSched : schedule st with
  | none =>
      simp
  | some pair =>
      cases pair with
      | mk cid stSched =>
          simp [mkConcreteScheduledStep, project_transition_blocked_eq_state_slice]

theorem project_concrete_scheduled_step_session_type_counts_match_post_state
    (st : ProtocolMachineState ι γ π ε ν) :
    Option.map (fun step => step.transition.sessionTypeCounts) (projectConcreteScheduledStep? st) =
      Option.map (fun step => concreteSessionTypeCountsOfStateSlice step.postState) (projectConcreteScheduledStep? st) := by
  unfold projectConcreteScheduledStep?
  cases hSched : schedule st with
  | none =>
      simp
  | some pair =>
      cases pair with
      | mk cid stSched =>
          simp [mkConcreteScheduledStep, project_transition_session_type_counts_eq_state_slice]

theorem project_concrete_scheduled_step_buffered_message_counts_match_post_state
    (st : ProtocolMachineState ι γ π ε ν) :
    Option.map (fun step => step.transition.bufferedMessageCounts) (projectConcreteScheduledStep? st) =
      Option.map (fun step => concreteBufferedMessageCountsOfStateSlice step.postState) (projectConcreteScheduledStep? st) := by
  unfold projectConcreteScheduledStep?
  cases hSched : schedule st with
  | none =>
      simp
  | some pair =>
      cases pair with
      | mk cid stSched =>
          simp [mkConcreteScheduledStep, project_transition_buffered_message_counts_eq_state_slice]

theorem project_concrete_scheduled_step_matches_schedule_exec
    (st : ProtocolMachineState ι γ π ε ν) :
    match projectConcreteScheduledStep? st, schedule st with
    | none, none => True
    | some step, some (cid, stSched) =>
        let (_stExec, res) := execInstr stSched cid
        step.transition.selectedCoro = cid ∧
        step.transition.execStatusTag = concreteExecStatusTag res.status
    | _, _ => False := by
  unfold projectConcreteScheduledStep?
  cases hSched : schedule st with
  | none =>
      simp
  | some pair =>
      cases pair with
      | mk cid stSched =>
          simp [mkConcreteScheduledStep, projectConcreteTransitionSlice]

theorem project_concrete_scheduled_step_claimed_surface_spec
    (st : ProtocolMachineState ι γ π ε ν) :
    match projectConcreteScheduledStep? st, schedule st with
    | none, none => True
    | some step, some (cid, stSched) =>
        let (stExec, res) := execInstr stSched cid
        let sched' := updateAfterStep stExec.sched cid res.status
        let stNext : ProtocolMachineState ι γ π ε ν := { stExec with sched := sched' }
        step.preState = projectConcreteProtocolMachineSlice st ∧
          step.postState = projectConcreteProtocolMachineSlice stNext ∧
          step.transition = projectConcreteTransitionSlice stNext cid res.status ∧
          step.event = projectConcreteTraceEvent? st.clock cid res.status res.event
    | _, _ => False := by
  unfold projectConcreteScheduledStep?
  cases hSched : schedule st with
  | none =>
      simp
  | some pair =>
      cases pair with
      | mk cid stSched =>
          simp [mkConcreteScheduledStep, projectConcreteTransitionSlice]

theorem mk_concrete_scheduled_step_pre_state
    (tick : Nat)
    (pre post : ProtocolMachineState ι γ π ε ν)
    (cid : CoroutineId)
    (status : ExecStatus γ)
    (ev : Option (StepEvent ε)) :
    (mkConcreteScheduledStep tick pre post cid status ev).preState =
      projectConcreteProtocolMachineSlice pre := by
  rfl

theorem mk_concrete_scheduled_step_post_state
    (tick : Nat)
    (pre post : ProtocolMachineState ι γ π ε ν)
    (cid : CoroutineId)
    (status : ExecStatus γ)
    (ev : Option (StepEvent ε)) :
    (mkConcreteScheduledStep tick pre post cid status ev).postState =
      projectConcreteProtocolMachineSlice post := by
  rfl

theorem mk_concrete_scheduled_step_transition
    (tick : Nat)
    (pre post : ProtocolMachineState ι γ π ε ν)
    (cid : CoroutineId)
    (status : ExecStatus γ)
    (ev : Option (StepEvent ε)) :
    (mkConcreteScheduledStep tick pre post cid status ev).transition =
      projectConcreteTransitionSlice post cid status := by
  rfl

theorem mk_concrete_scheduled_step_event
    (tick : Nat)
    (pre post : ProtocolMachineState ι γ π ε ν)
    (cid : CoroutineId)
    (status : ExecStatus γ)
    (ev : Option (StepEvent ε)) :
    (mkConcreteScheduledStep tick pre post cid status ev).event =
      projectConcreteTraceEvent? tick cid status ev := by
  rfl

theorem concrete_send_slice_preserves_coherent
    {G G' : GEnv} {D D' : DEnv}
    {senderEp : Endpoint} {receiverRole : Role} {T : ValType}
    (hSpec : SendSpec G G' D D' senderEp receiverRole T)
    (hCoh : Coherent G D)
    (hReady : SendReady G D) :
    Coherent G' D' :=
  send_spec_preserves_coherent hSpec hCoh hReady

theorem concrete_recv_slice_preserves_coherent
    {G G' : GEnv} {D D' : DEnv}
    {receiverEp : Endpoint} {senderRole : Role} {T : ValType}
    (hSpec : RecvSpec G G' D D' receiverEp senderRole T)
    (hCoh : Coherent G D) :
    Coherent G' D' :=
  recv_spec_preserves_coherent hSpec hCoh

theorem concrete_scheduler_slice_confluent
    (st : ProtocolMachineState ι γ π ε ν) :
    schedule_confluence st :=
  schedule_confluence_holds st

theorem concrete_scheduler_slice_cooperative_refines_concurrent
    (st : ProtocolMachineState ι γ π ε ν) :
    cooperative_refines_concurrent st :=
  cooperative_refines_concurrent_holds st

theorem concrete_slice_threaded_one_refines_canonical
    (fuel : Nat) (st : ProtocolMachineState ι γ π ε ν) :
    runScheduledThreaded fuel 1 st = runScheduled fuel 1 st :=
  run_scheduled_threaded_one_eq_run_scheduled fuel st

end

end Proofs
end Runtime
