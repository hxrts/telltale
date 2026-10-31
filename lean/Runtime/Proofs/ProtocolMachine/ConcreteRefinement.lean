import Runtime.Proofs.ProtocolMachine.ConcreteRefinementCore


/-! # Runtime.Proofs.ProtocolMachine.ConcreteRefinement

Concrete projection helpers for the first implementation-facing protocol-machine
refinement slice. The slice intentionally tracks only:

- session-local type counts
- buffered message counts
- scheduler ready / blocked state
- coroutine-local program counters and status tags

This is the smallest nontrivial state surface that the Rust runtime, Lean
runner, and threaded runtime can compare exactly today.


Slice records and trace-event projections are in
`Runtime.Proofs.ProtocolMachine.ConcreteRefinementCore`.
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

theorem concrete_scheduler_slice_deterministic
    (st : ProtocolMachineState ι γ π ε ν) :
    schedule_deterministic st :=
  schedule_deterministic_holds st

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
