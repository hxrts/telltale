import Runtime.VM.API
import Runtime.VM.Model.SchedulerTypes

/-! # Runtime.VM.Runtime.SchedulerHelpers

Lane-aware queue and runnable-selection helpers for the VM scheduler.
-/

/-
The Problem. Scheduler selection logic should be reusable and isolated from step orchestration.

Solution Structure. Define runnable predicates, lane normalization, queue utilities, and policy-aware pickers.
-/

set_option autoImplicit false

universe u
/-! ## Scheduler helpers -/

/-! ### Runnable predicates and lane lookup -/

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

/-! ### Canonical lane-map normalization -/

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

/-! ### Lane-view synchronization and edits -/

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

/-! ### Coroutine view predicates -/

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

/-! ### Queue combinators -/

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

/-! ### Policy-specific queue pickers -/

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

/-! #### Policy dispatcher over queue pickers -/

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

/-! ### Lane-aware global selection -/

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

/-! ### Queue updates after execution steps -/

def dropBlocked {γ : Type u} (blocked : BlockedSet γ) (cid : CoroutineId) :
    BlockedSet γ :=
  -- Remove any stale blocked entry for the coroutine.
  blocked.erase cid

def enqueueCoro (queue : SchedQueue) (cid : CoroutineId) : SchedQueue :=
  -- Enqueue at back while preserving queue uniqueness.
  if cid ∈ queue then queue else queue ++ [cid]

private def transferReason (endpoint : Endpoint) : String :=
  s!"transfer {endpoint.sid}:{endpoint.role}"

private def delegationWitness (fromCoro toCoro : CoroutineId) (endpoint : Endpoint) : String :=
  s!"delegation[{endpoint.sid}:{endpoint.role}] {fromCoro}->{toCoro}"

private def delegationHandoffValid (h : CrossLaneHandoff) : Bool :=
  h.fromCoro ≠ h.toCoro &&
  h.reason.startsWith "transfer " &&
  h.delegationWitness.length > 0

private def typedTransferTransitionAllowed {γ : Type u}
    (sched : SchedState γ) (fromCoro : CoroutineId) (endpoint : Endpoint) : Bool :=
  -- Cross-lane ownership transitions are only allowed when the source lane
  -- currently owns the transferred endpoint key (or key is not tracked yet).
  let key : OwnershipKey := (endpoint.sid, endpoint.role)
  let fromLane := laneOf sched fromCoro
  match sched.ownershipIndex.get? key with
  | none => true
  | some ownerLane => ownerLane = fromLane

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
      , reason := transferReason endpoint
      , delegationWitness := delegationWitness fromCoro toCoro endpoint }
    { sched with crossLaneHandoffs := sched.crossLaneHandoffs ++ [handoff] }

def updateAfterStep {γ : Type u} (sched : SchedState γ) (cid : CoroutineId)
    (status : ExecStatus γ) : SchedState γ :=
  -- Update queues and blocked set based on step status.
  let schedFiltered :=
    { sched with crossLaneHandoffs := sched.crossLaneHandoffs.filter delegationHandoffValid }
  let sched0 := syncLaneViews schedFiltered
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
      if typedTransferTransitionAllowed sched1 cid endpoint then
        let toLane := laneOf sched1 targetId
        let ownership' := sched1.ownershipIndex.insert (endpoint.sid, endpoint.role) toLane
        let sched2 := { sched1 with ownershipIndex := ownership' }
        syncLaneViews (recordCrossLaneTransfer sched2 cid endpoint targetId)
      else
        syncLaneViews sched1
  | _ =>
      syncLaneViews { sched0 with blockedSet := blocked', readyQueue := enqueueCoro ready' cid }
