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
  sched.laneOf.getD cid 0

private def insertLaneSorted (lane : LaneId) (xs : List LaneId) : List LaneId :=
  match xs with
  | [] => [lane]
  | x :: rest =>
      if lane = x then
        xs
      else if lane < x then
        lane :: xs
      else
        x :: insertLaneSorted lane rest

def orderedLaneIds {γ : Type u} (sched : SchedState γ) : List LaneId :=
  let fromReady := sched.readyQueue.map (fun cid => laneOf sched cid)
  let fromBlocked := (sched.blockedSet.toList.map (fun p => laneOf sched p.1))
  let fromMap := sched.laneQueues.toList.map (fun p => p.1)
  let lanes := (fromMap ++ fromReady ++ fromBlocked).foldl
    (fun acc lane => insertLaneSorted lane acc) []
  if lanes.isEmpty then [0] else lanes

private def canonicalLaneOfMap {γ : Type u} (sched : SchedState γ) : LaneOfMap :=
  let withReady := sched.readyQueue.foldl
    (fun acc cid => if acc.contains cid then acc else acc.insert cid 0)
    sched.laneOf
  sched.blockedSet.toList.foldl
    (fun acc p =>
      let cid := p.1
      if acc.contains cid then acc else acc.insert cid 0)
    withReady

private def laneQueueInsert (laneQueues : LaneQueueMap) (lane : LaneId) (cid : CoroutineId) :
    LaneQueueMap :=
  let queue := laneQueues.getD lane []
  let queue' := if cid ∈ queue then queue else queue ++ [cid]
  laneQueues.insert lane queue'

private def laneBlockedInsert {γ : Type u} (laneBlocked : LaneBlockedMap γ)
    (lane : LaneId) (cid : CoroutineId) (reason : BlockReason γ) : LaneBlockedMap γ :=
  let blocked := laneBlocked.getD lane {}
  laneBlocked.insert lane (blocked.insert cid reason)

/-- Rebuild per-lane queues/maps from the global ready/blocked structures. -/
def syncLaneViews {γ : Type u} (sched : SchedState γ) : SchedState γ :=
  let laneOf' := canonicalLaneOfMap sched
  let laneQueues' :=
    sched.readyQueue.foldl
      (fun acc cid => laneQueueInsert acc (laneOf'.getD cid 0) cid)
      (({} : LaneQueueMap).insert 0 [])
  let laneBlocked' :=
    sched.blockedSet.toList.foldl
      (fun acc p =>
        let cid := p.1
        let reason := p.2
        laneBlockedInsert acc (laneOf'.getD cid 0) cid reason)
      (({} : LaneBlockedMap γ).insert 0 ({} : BlockedSet γ))
  { sched with laneOf := laneOf', laneQueues := laneQueues', laneBlocked := laneBlocked' }

/-- Assign a coroutine to a scheduler lane (default fallback lane `0`). -/
def assignLane {γ : Type u} (sched : SchedState γ) (cid : CoroutineId) (lane : LaneId) :
    SchedState γ :=
  syncLaneViews { sched with laneOf := sched.laneOf.insert cid lane }

/-- Unblock a coroutine: move it from blocked structures back to ready. -/
def unblockCoroutine {γ : Type u} (sched : SchedState γ) (cid : CoroutineId) :
    SchedState γ :=
  if sched.blockedSet.contains cid then
    let ready' :=
      if cid ∈ sched.readyQueue then sched.readyQueue else sched.readyQueue ++ [cid]
    syncLaneViews
      { sched with
          blockedSet := sched.blockedSet.erase cid
          readyQueue := ready' }
  else
    syncLaneViews sched

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

def pickRoundRobinInQueue {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (queue : SchedQueue) : Option (CoroutineId × SchedQueue) :=
  -- Pick the first runnable coroutine in the queue.
  takeOut queue (fun cid => isRunnable st cid)

def pickRoundRobin {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : Option (CoroutineId × SchedQueue) :=
  pickRoundRobinInQueue st st.sched.readyQueue

def pickProgressInQueue {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (queue : SchedQueue) : Option (CoroutineId × SchedQueue) :=
  -- Prefer runnable coroutines with progress tokens.
  match takeOut queue (fun cid => isRunnable st cid && hasProgress st cid) with
  | some res => some res
  | none => pickRoundRobinInQueue st queue

def pickProgress {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : Option (CoroutineId × SchedQueue) :=
  pickProgressInQueue st st.sched.readyQueue

def pickPriorityInQueue {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (queue : SchedQueue) (f : CoroutineId → Nat) :
    Option (CoroutineId × SchedQueue) :=
  -- Pick the runnable coroutine with the highest priority.
  pickBest queue f (fun cid => isRunnable st cid)

def pickPriority {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (f : CoroutineId → Nat) :
    Option (CoroutineId × SchedQueue) :=
  pickPriorityInQueue st st.sched.readyQueue f

def pickRunnableInQueue {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (policy : SchedPolicy) (st : VMState ι γ π ε ν) (queue : SchedQueue) :
    Option (CoroutineId × SchedQueue) :=
  match policy with
  | .roundRobin => pickRoundRobinInQueue st queue
  | .cooperative => pickRoundRobinInQueue st queue
  | .priority f => pickPriorityInQueue st queue f
  | .progressAware => pickProgressInQueue st queue

def pickLaneAux {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (policy : SchedPolicy) (st : VMState ι γ π ε ν) (sched : SchedState γ)
    (lanes : List LaneId) (start offset fuel : Nat) : Option CoroutineId :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      let lane := lanes.getD ((start + offset) % lanes.length) 0
      let queue := sched.laneQueues.getD lane []
      match pickRunnableInQueue policy st queue with
      | some (cid, _) => some cid
      | none => pickLaneAux policy st sched lanes start (offset + 1) fuel'

def pickRunnableFromSched {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (policy : SchedPolicy) (st : VMState ι γ π ε ν) (sched : SchedState γ) :
    Option (CoroutineId × SchedQueue) :=
  let lanes := orderedLaneIds sched
  let start :=
    if lanes.isEmpty then
      0
    else
      (sched.stepCount + 1) % lanes.length
  let picked? := pickLaneAux policy st sched lanes start 0 lanes.length
  match picked? with
  | some cid => some (cid, removeFirst cid sched.readyQueue)
  | none =>
      match pickRunnableInQueue policy st sched.readyQueue with
      | some (cid, _) => some (cid, removeFirst cid sched.readyQueue)
      | none => none

def pickRunnable {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : Option (CoroutineId × SchedQueue) :=
  -- Policy-directed lane-aware runnable selection with global fallback.
  let sched := syncLaneViews st.sched
  let st' := { st with sched := sched }
  pickRunnableFromSched st'.sched.policy st' sched

def dropBlocked {γ : Type u} (blocked : BlockedSet γ) (cid : CoroutineId) :
    BlockedSet γ :=
  -- Remove any stale blocked entry for the coroutine.
  blocked.erase cid

def enqueueCoro (queue : SchedQueue) (cid : CoroutineId) : SchedQueue :=
  -- Enqueue at back while preserving queue uniqueness.
  if cid ∈ queue then queue else queue ++ [cid]

private def transferReason (endpoint : Endpoint) : String :=
  s!"transfer {endpoint.sid}:{endpoint.role}"

private def recordCrossLaneTransfer {γ : Type u}
    (sched : SchedState γ) (fromCoro : CoroutineId) (endpoint : Endpoint)
    (toCoro : CoroutineId) : SchedState γ :=
  let fromLane := laneOf sched fromCoro
  let toLane := laneOf sched toCoro
  if fromLane = toLane then
    sched
  else
    let handoff : CrossLaneHandoff :=
      { fromCoro := fromCoro
      , toCoro := toCoro
      , fromLane := fromLane
      , toLane := toLane
      , step := sched.stepCount
      , reason := transferReason endpoint }
    { sched with crossLaneHandoffs := sched.crossLaneHandoffs ++ [handoff] }

def updateAfterStep {γ : Type u} (sched : SchedState γ) (cid : CoroutineId)
    (status : ExecStatus γ) : SchedState γ :=
  -- Update queues and blocked set based on step status.
  let sched0 := syncLaneViews sched
  let blocked' := dropBlocked sched0.blockedSet cid
  let ready' := removeFirst cid sched0.readyQueue
  match status with
  | .blocked reason =>
      syncLaneViews { sched0 with readyQueue := ready', blockedSet := blocked'.insert cid reason }
  | .halted | .faulted _ =>
      syncLaneViews { sched0 with readyQueue := ready', blockedSet := blocked' }
  | .spawned newId =>
      let laneOf' :=
        if sched0.laneOf.contains newId then sched0.laneOf else sched0.laneOf.insert newId 0
      syncLaneViews
        { sched0 with
            laneOf := laneOf'
            blockedSet := blocked'
            readyQueue := enqueueCoro (enqueueCoro ready' cid) newId }
  | .transferred endpoint targetId =>
      let sched1 :=
        { sched0 with blockedSet := blocked', readyQueue := enqueueCoro ready' cid }
      syncLaneViews (recordCrossLaneTransfer sched1 cid endpoint targetId)
  | _ =>
      syncLaneViews { sched0 with blockedSet := blocked', readyQueue := enqueueCoro ready' cid }

/-! ## Scheduler step -/

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

/-- Proof witness for the one-lane compatibility contract. -/
theorem single_lane_schedule_compat_holds {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν)
    (laneOf' : LaneOfMap)
    (laneQueues' : LaneQueueMap)
    (laneBlocked' : LaneBlockedMap γ)
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

theorem policy_selection_deterministic_holds {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (policy : SchedPolicy) (st : VMState ι γ π ε ν) :
    policy_selection_deterministic policy st := by
  intro _ st1 st2 h1 h2
  exact Option.some.inj (h1.symm.trans h2)

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

/-!
Proof witnesses for scheduler properties (`*_holds`) live in:
`Runtime.Proofs.VM.Scheduler`.
-/
