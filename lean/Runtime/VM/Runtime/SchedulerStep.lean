import Runtime.VM.Runtime.SchedulerHelpers

/-! # Runtime.VM.Runtime.SchedulerStep

Scheduler step orchestration and deterministic policy-level contracts.
-/

/-
The Problem. Connect helper-level selection to concrete scheduler transitions and contracts.

Solution Structure. Define `schedule`/`schedStep`, current-instruction views, and deterministic policy properties.
-/

set_option autoImplicit false

universe u
/-! ## Scheduler step -/

/-! ### Core scheduling primitives -/

def schedule {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν] :
    VMState ι γ π ε ν → Option (CoroutineId × VMState ι γ π ε ν) :=
  fun st =>
    -- Pick a runnable coroutine and remove it from the queue.
    let st' := { st with sched := syncLaneViews st.sched }
    match pickRunnable st' with
    | none => none
    | some (cid, rest) =>
        let sched' := syncLaneViews
          { st'.sched with readyQueue := rest, stepCount := st'.sched.stepCount + 1 }
        some (cid, { st' with sched := sched' })

/-- Instruction about to execute under the scheduler. -/
def currentInstr_coro {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coroId : CoroutineId) : Option (Instr γ ε) :=
  -- Use the coroutine PC to fetch the next instruction.
  match st.coroutines[coroId]? with
  | none => none
  | some c =>
      match st.programs[c.programId]? with
      | none => none
      | some prog => prog.code[c.pc]?

/-- Instruction about to execute given a scheduling step. -/
def currentInstr {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (_ : Unit) : Option (Instr γ ε) :=
  -- Determine the instruction selected by the scheduler.
  match schedule st with
  | none => none
  | some (coroId, st') => currentInstr_coro st' coroId

/-- Scheduler step: run a selected coroutine and update queues. -/
def schedStep {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν] :
    VMState ι γ π ε ν → Option (VMState ι γ π ε ν) :=
  fun st =>
    -- Execute a single scheduled coroutine step.
    match schedule st with
    | none => none
      | some (cid, st') =>
          let (st'', res) := execInstr st' cid
          let sched'' := updateAfterStep st''.sched cid res.status
          some { st'' with sched := sched'' }

/-! ### Lane compatibility contracts -/

/-- Compatibility contract when lane metadata snapshots are unchanged. -/
def single_lane_schedule_compat {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν)
    (laneOf' : LaneOfMap)
    (laneQueues' : LaneQueueMap)
    (laneBlocked' : LaneBlockedMap γ)
    (handoffs' : List CrossLaneHandoff) : Prop :=
  schedule { st with
    sched := { st.sched with
      laneOf := laneOf'
      laneQueues := laneQueues'
      laneBlocked := laneBlocked'
      crossLaneHandoffs := handoffs' } } = schedule st

/-! ### Deterministic policy-selection contracts -/

/-- Scheduler choices are confluent: `schedule` is a deterministic function. -/
def schedule_confluence {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : Prop :=
  -- Scheduling is deterministic for a given state.
  ∀ st1 st2, schedule st = some st1 → schedule st = some st2 → st1 = st2

/-- Deterministic scheduler pick invariant under a pinned policy. -/
def policy_selection_deterministic {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (policy : SchedPolicy) (st : VMState ι γ π ε ν) : Prop :=
  st.sched.policy = policy → schedule_confluence st

def roundRobin_selection_deterministic {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : Prop :=
  policy_selection_deterministic .roundRobin st

def cooperative_selection_deterministic {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : Prop :=
  policy_selection_deterministic .cooperative st

def priority_selection_deterministic {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (f : CoroutineId → Nat) (st : VMState ι γ π ε ν) : Prop :=
  policy_selection_deterministic (.priority f) st

def progressAware_selection_deterministic {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : Prop :=
  policy_selection_deterministic .progressAware st

/-! ### Policy refinement and liveness predicates -/

/-- Cooperative scheduling refines round-robin: swapping the policy field before
    queue-level selection under normalized scheduler views. -/
def cooperative_refines_concurrent {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : Prop :=
  let st' := { st with sched := syncLaneViews st.sched }
  -- Cooperative and round-robin choose identically on the same normalized queue.
  st.sched.policy = .cooperative →
    pickRunnableInQueue .roundRobin st' st'.sched.readyQueue =
      pickRunnableInQueue st'.sched.policy st' st'.sched.readyQueue

def starvation_free {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : Prop :=
  -- Scheduling is live: a runnable coroutine in the queue guarantees a scheduled step.
  ∀ cid, cid ∈ st.sched.readyQueue →
    match st.coroutines[cid]? with
    | none => True
    | some c => (c.status = .ready ∨ c.status = .speculating) →
        ∃ cid' st', schedule st = some (cid', st')

/-! Proof witnesses for scheduler properties (`*_holds`) live in
`Runtime.Proofs.VM.Scheduler`. -/
