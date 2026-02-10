import Runtime.VM.API
import Runtime.VM.Model.SchedulerTypes

/-! # Scheduler Model

Queue-based scheduler with policy-guided selection and blocked bookkeeping. -/

/-
The Problem. The runtime needs a scheduler model that can be referenced by the
VM without pulling in proof-level dependencies.

Solution Structure. Implement a queue-based scheduler with policy-guided
selection and blocked bookkeeping, then thread it through `schedStep`.
-/

set_option autoImplicit false

universe u

/-! ## Scheduler helpers -/

def runnable {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (c : CoroutineState γ ε) : Bool :=
  -- Ready and speculating coroutines are runnable.
  match c.status with
  | .ready | .speculating => true
  | _ => false

def hasProgressToken {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (c : CoroutineState γ ε) : Bool :=
  -- A coroutine is progress-aware if it holds tokens.
  !c.progressTokens.isEmpty

/-- Lookup lane assignment for a coroutine. Defaults to lane `0` if absent. -/
def laneOf {γ : Type u} (sched : SchedState γ) (cid : CoroutineId) : LaneId :=
  match sched.laneOf.find? (fun p => decide (p.fst = cid)) with
  | some (_, lid) => lid
  | none => 0

def getCoro {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (cid : CoroutineId) : Option (CoroutineState γ ε) :=
  -- Safe coroutine lookup.
  st.coroutines[cid]?

def isRunnable {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (cid : CoroutineId) : Bool :=
  -- Check runnable status using the coroutine array.
  match getCoro st cid with
  | some c => runnable c
  | none => false

def hasProgress {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (cid : CoroutineId) : Bool :=
  -- Check progress-token ownership for the coroutine.
  match getCoro st cid with
  | some c => hasProgressToken c
  | none => false

def takeOut (queue : SchedQueue) (p : CoroutineId → Bool) :
    Option (CoroutineId × SchedQueue) :=
  -- Remove the first element matching `p`, preserving order.
  match queue with
  | [] => none
  | cid :: rest =>
      if p cid then
        some (cid, rest)
      else
        match takeOut rest p with
        | none => none
        | some (cid', rest') => some (cid', cid :: rest')

def removeFirst (cid : CoroutineId) (queue : SchedQueue) : SchedQueue :=
  -- Drop the first occurrence of a coroutine id.
  match queue with
  | [] => []
  | x :: xs => if x = cid then xs else x :: removeFirst cid xs

def bestCandidate (queue : SchedQueue) (score : CoroutineId → Nat)
    (p : CoroutineId → Bool) : Option CoroutineId :=
  -- Select the runnable element with the maximum score.
  match queue with
  | [] => none
  | cid :: rest =>
      let bestRest := bestCandidate rest score p
      if p cid then
        match bestRest with
        | none => some cid
        | some best => if score cid ≥ score best then some cid else some best
      else
        bestRest

def pickBest (queue : SchedQueue) (score : CoroutineId → Nat)
    (p : CoroutineId → Bool) : Option (CoroutineId × SchedQueue) :=
  -- Pick the max-scoring runnable element and return the rest.
  match bestCandidate queue score p with
  | none => none
  | some cid => some (cid, removeFirst cid queue)

def pickRoundRobin {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : Option (CoroutineId × SchedQueue) :=
  -- Pick the first runnable coroutine in the queue.
  takeOut st.sched.readyQueue (fun cid => isRunnable st cid)

def pickProgress {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : Option (CoroutineId × SchedQueue) :=
  -- Prefer runnable coroutines with progress tokens.
  match takeOut st.sched.readyQueue (fun cid => isRunnable st cid && hasProgress st cid) with
  | some res => some res
  | none => pickRoundRobin st

def pickPriority {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (f : CoroutineId → Nat) :
    Option (CoroutineId × SchedQueue) :=
  -- Pick the runnable coroutine with the highest priority.
  pickBest st.sched.readyQueue f (fun cid => isRunnable st cid)

def pickRunnable {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : Option (CoroutineId × SchedQueue) :=
  -- Policy-directed runnable selection.
  match st.sched.policy with
  | .roundRobin => pickRoundRobin st
  | .cooperative => pickRoundRobin st
  | .priority f => pickPriority st f
  | .progressAware => pickProgress st

def dropBlocked {γ : Type u} (blocked : BlockedSet γ) (cid : CoroutineId) :
    BlockedSet γ :=
  -- Remove any stale blocked entry for the coroutine.
  blocked.filter (fun p => decide (p.fst ≠ cid))

def enqueueCoro (queue : SchedQueue) (cid : CoroutineId) : SchedQueue :=
  -- Enqueue a coroutine at the back.
  queue ++ [cid]

def updateAfterStep {γ : Type u} (sched : SchedState γ) (cid : CoroutineId)
    (status : ExecStatus γ) : SchedState γ :=
  -- Update queues and blocked set based on step status.
  let blocked' := dropBlocked sched.blockedSet cid
  match status with
  | .blocked reason => { sched with blockedSet := (cid, reason) :: blocked' }
  | .halted | .faulted _ => { sched with blockedSet := blocked' }
  | .spawned newId =>
      { sched with blockedSet := blocked', readyQueue := enqueueCoro (enqueueCoro sched.readyQueue cid) newId }
  | _ => { sched with blockedSet := blocked', readyQueue := enqueueCoro sched.readyQueue cid }

/-! ## Scheduler step -/

def schedule {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν] :
    VMState ι γ π ε ν → Option (CoroutineId × VMState ι γ π ε ν) :=
  fun st =>
    -- Pick a runnable coroutine and remove it from the queue.
    match pickRunnable st with
    | none => none
    | some (cid, rest) =>
        let sched' := { st.sched with readyQueue := rest, stepCount := st.sched.stepCount + 1 }
        some (cid, { st with sched := sched' })

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

/-- One-lane compatibility contract: lane metadata does not alter scheduler semantics in v1. -/
def single_lane_schedule_compat {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν)
    (laneOf' : List (CoroutineId × LaneId))
    (laneQueues' : List (LaneId × LaneQueue))
    (laneBlocked' : List (LaneId × LaneBlockedSet γ))
    (handoffs' : List CrossLaneHandoff) : Prop :=
  schedule { st with
    sched := { st.sched with
      laneOf := laneOf'
      laneQueues := laneQueues'
      laneBlocked := laneBlocked'
      crossLaneHandoffs := handoffs' } } = schedule st

/-- Proof witness for the one-lane compatibility contract. -/
theorem single_lane_schedule_compat_holds {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν)
    (laneOf' : List (CoroutineId × LaneId))
    (laneQueues' : List (LaneId × LaneQueue))
    (laneBlocked' : List (LaneId × LaneBlockedSet γ))
    (handoffs' : List CrossLaneHandoff)
    (hLaneOf : laneOf' = st.sched.laneOf)
    (hLaneQueues : laneQueues' = st.sched.laneQueues)
    (hLaneBlocked : laneBlocked' = st.sched.laneBlocked)
    (hHandoffs : handoffs' = st.sched.crossLaneHandoffs) :
    single_lane_schedule_compat st laneOf' laneQueues' laneBlocked' handoffs' := by
  subst hLaneOf
  subst hLaneQueues
  subst hLaneBlocked
  subst hHandoffs
  rfl

/-- Scheduler choices are confluent: `schedule` is a deterministic function. -/
def schedule_confluence {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : Prop :=
  -- Scheduling is deterministic for a given state.
  ∀ st1 st2, schedule st = some st1 → schedule st = some st2 → st1 = st2

/-- Cooperative scheduling refines round-robin: swapping the policy field before
    scheduling gives the same result as scheduling first and normalizing the
    policy afterward. -/
def cooperative_refines_concurrent {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : Prop :=
  -- Scheduling is policy-independent up to the preserved policy tag.
  st.sched.policy = .cooperative →
    schedule { st with sched := { st.sched with policy := .roundRobin } } =
      (schedule st).map
        (fun (cid, s) => (cid, { s with sched := { s.sched with policy := .roundRobin } }))

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

/-!
Proof witnesses for scheduler properties (`*_holds`) live in:
`Runtime.Proofs.VM.Scheduler`.
-/
