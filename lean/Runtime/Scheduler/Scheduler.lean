import Runtime.VM.Definition
import Runtime.VM.SchedulerTypes

/-
The Problem. The runtime needs a scheduler model that can be referenced by the
VM without pulling in proof-level dependencies.

Solution Structure. Implement a queue-based scheduler with policy-guided
selection and blocked bookkeeping, then thread it through `schedStep`.
-/

set_option autoImplicit false

/-! ## Scheduler helpers -/

private def runnable {γ ε : Type} [GuardLayer γ] [EffectModel ε]
    (c : CoroutineState γ ε) : Bool :=
  -- Ready and speculating coroutines are runnable.
  match c.status with
  | .ready | .speculating => true
  | _ => false

private def hasProgressToken {γ ε : Type} [GuardLayer γ] [EffectModel ε]
    (c : CoroutineState γ ε) : Bool :=
  -- A coroutine is progress-aware if it holds tokens.
  !c.progressTokens.isEmpty

private def getCoro {ι γ π ε : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    (st : VMState ι γ π ε) (cid : CoroutineId) : Option (CoroutineState γ ε) :=
  -- Safe coroutine lookup.
  st.coroutines[cid]?

private def isRunnable {ι γ π ε : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    (st : VMState ι γ π ε) (cid : CoroutineId) : Bool :=
  -- Check runnable status using the coroutine array.
  match getCoro st cid with
  | some c => runnable c
  | none => false

private def hasProgress {ι γ π ε : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    (st : VMState ι γ π ε) (cid : CoroutineId) : Bool :=
  -- Check progress-token ownership for the coroutine.
  match getCoro st cid with
  | some c => hasProgressToken c
  | none => false

private def takeOut (queue : SchedQueue) (p : CoroutineId → Bool) :
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

private def removeFirst (cid : CoroutineId) (queue : SchedQueue) : SchedQueue :=
  -- Drop the first occurrence of a coroutine id.
  match queue with
  | [] => []
  | x :: xs => if x = cid then xs else x :: removeFirst cid xs

private def bestCandidate (queue : SchedQueue) (score : CoroutineId → Nat)
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

private def pickBest (queue : SchedQueue) (score : CoroutineId → Nat)
    (p : CoroutineId → Bool) : Option (CoroutineId × SchedQueue) :=
  -- Pick the max-scoring runnable element and return the rest.
  match bestCandidate queue score p with
  | none => none
  | some cid => some (cid, removeFirst cid queue)

private def pickRoundRobin {ι γ π ε : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    (st : VMState ι γ π ε) : Option (CoroutineId × SchedQueue) :=
  -- Pick the first runnable coroutine in the queue.
  takeOut st.sched.readyQueue (fun cid => isRunnable st cid)

private def pickProgress {ι γ π ε : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    (st : VMState ι γ π ε) : Option (CoroutineId × SchedQueue) :=
  -- Prefer runnable coroutines with progress tokens.
  match takeOut st.sched.readyQueue (fun cid => isRunnable st cid && hasProgress st cid) with
  | some res => some res
  | none => pickRoundRobin st

private def pickPriority {ι γ π ε : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    (st : VMState ι γ π ε) (f : CoroutineId → Nat) :
    Option (CoroutineId × SchedQueue) :=
  -- Pick the runnable coroutine with the highest priority.
  pickBest st.sched.readyQueue f (fun cid => isRunnable st cid)

private def pickRunnable {ι γ π ε : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    (st : VMState ι γ π ε) : Option (CoroutineId × SchedQueue) :=
  -- Dispatch selection based on scheduler policy.
  match st.sched.policy with
  | .progressAware => pickProgress st
  | .priority f => pickPriority st f
  | .roundRobin => pickRoundRobin st
  | .cooperative => pickRoundRobin st
  | .workStealing _ => pickRoundRobin st

private def dropBlocked {γ : Type} (blocked : BlockedSet γ) (cid : CoroutineId) :
    BlockedSet γ :=
  -- Remove any stale blocked entry for the coroutine.
  blocked.filter (fun p => decide (p.fst ≠ cid))

private def enqueueCoro (queue : SchedQueue) (cid : CoroutineId) : SchedQueue :=
  -- Enqueue a coroutine at the back.
  queue ++ [cid]

private def updateAfterStep {γ : Type} (sched : SchedState γ) (cid : CoroutineId)
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

def schedule {ι γ π ε : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] :
    VMState ι γ π ε → Option (CoroutineId × VMState ι γ π ε) :=
  fun st =>
    -- Pick a runnable coroutine and remove it from the queue.
    match pickRunnable st with
    | none => none
    | some (cid, rest) =>
        let sched' := { st.sched with readyQueue := rest, stepCount := st.sched.stepCount + 1 }
        some (cid, { st with sched := sched' })

/-- Instruction about to execute under the scheduler. -/
def currentInstr_coro {ι γ π ε : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    (st : VMState ι γ π ε) (coroId : CoroutineId) : Option (Instr γ ε) :=
  -- Use the coroutine PC to fetch the next instruction.
  match st.coroutines[coroId]? with
  | none => none
  | some c => st.code.code[c.pc]?

/-- Instruction about to execute given a scheduling step. -/
def currentInstr {ι γ π ε : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    (st : VMState ι γ π ε) (_ : Unit) : Option (Instr γ ε) :=
  -- Determine the instruction selected by the scheduler.
  match schedule st with
  | none => none
  | some (coroId, st') => currentInstr_coro st' coroId

/-- Scheduler step: run a selected coroutine and update queues. -/
def schedStep {ι γ π ε : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] :
    VMState ι γ π ε → Option (VMState ι γ π ε) :=
  fun st =>
    -- Execute a single scheduled coroutine step.
    match schedule st with
    | none => none
    | some (cid, st') =>
        let (st'', res) := execInstr st' cid
        let sched'' := updateAfterStep st''.sched cid res.status
        some { st'' with sched := sched'' }

/-- Placeholder: scheduler choices are confluent. -/
def schedule_confluence {ι γ π ε : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    (_st : VMState ι γ π ε) : Prop :=
  -- Placeholder for schedule confluence.
  True

/-- Placeholder: cooperative execution refines concurrent. -/
def cooperative_refines_concurrent {ι γ π ε : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    (_st : VMState ι γ π ε) : Prop :=
  -- Placeholder for refinement.
  True
