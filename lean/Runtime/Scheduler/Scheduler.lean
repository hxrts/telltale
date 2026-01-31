import Runtime.VM.Definition
import Runtime.VM.SchedulerTypes

/-
The Problem. The runtime needs a scheduler model that can be referenced by the
VM without pulling in proof-level dependencies.

Solution Structure. Define a queue-based scheduler that tracks runnable and
blocked coroutines, and update the VM state accordingly.
-/

set_option autoImplicit false

/-! ## Scheduler state -/

structure CoroutinePool where
  -- Partition coroutines by status.
  ready : List CoroutineId
  blocked : List CoroutineId
  halted : List CoroutineId
  deriving Repr

/-! ## Scheduler helpers -/

private def runnable {γ ε : Type} [GuardLayer γ] [EffectModel ε]
    (c : CoroutineState γ ε) : Bool :=
  -- Ready and speculating coroutines are runnable.
  match c.status with
  | .ready | .speculating => true
  | _ => false

private def popReady {ι γ π ε : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    (st : VMState ι γ π ε) : Option (CoroutineId × List CoroutineId) :=
  -- Find the first runnable coroutine in the queue.
  let rec go (todo seen : List CoroutineId) : Option (CoroutineId × List CoroutineId) :=
    match todo with
    | [] => none
    | cid :: rest =>
        match st.coroutines[cid]? with
        | some c =>
            if runnable c then
              some (cid, (List.reverse seen) ++ rest)
            else
              go rest (cid :: seen)
        | none => go rest seen
  go st.sched.readyQueue []

private def rotateQueue (queue : List CoroutineId) (cid : CoroutineId) : List CoroutineId :=
  -- Round-robin: move the chosen id to the back.
  queue ++ [cid]

private def updateAfterStep {γ : Type} (sched : SchedState γ) (cid : CoroutineId)
    (status : ExecStatus γ) : SchedState γ :=
  -- Move coroutines between queues based on step result.
  match status with
  | .blocked reason =>
      { sched with blockedSet := (cid, reason) :: sched.blockedSet }
  | .halted | .faulted _ => sched
  | _ => { sched with readyQueue := sched.readyQueue ++ [cid] }

/-! ## Scheduler step -/

def schedule {ι γ π ε : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] :
    VMState ι γ π ε → Option (CoroutineId × VMState ι γ π ε) :=
  fun st =>
    -- Pick a runnable coroutine from the ready queue.
    match popReady st with
    | none => none
    | some (cid, rest) =>
        let queue' := rotateQueue rest cid
        let sched' := { st.sched with readyQueue := queue', stepCount := st.sched.stepCount + 1 }
        some (cid, { st with sched := sched' })

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
