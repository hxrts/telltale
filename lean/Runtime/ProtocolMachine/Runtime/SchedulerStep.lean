import Runtime.ProtocolMachine.Runtime.SchedulerHelpers

/-! # Runtime.ProtocolMachine.Runtime.SchedulerStep

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
    ProtocolMachineState ι γ π ε ν → Option (CoroutineId × ProtocolMachineState ι γ π ε ν) :=
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
    (st : ProtocolMachineState ι γ π ε ν) (coroId : CoroutineId) : Option (Instr γ ε) :=
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
    (st : ProtocolMachineState ι γ π ε ν) (_ : Unit) : Option (Instr γ ε) :=
  -- Determine the instruction selected by the scheduler.
  match schedule st with
  | none => none
  | some (coroId, st') => currentInstr_coro st' coroId

/-- Scheduler step: run a selected coroutine and update queues. -/
def schedStep {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν] :
    ProtocolMachineState ι γ π ε ν → Option (ProtocolMachineState ι γ π ε ν) :=
  fun st =>
    -- Execute a single scheduled coroutine step.
    match schedule st with
    | none => none
      | some (cid, st') =>
          let (st'', res) := execInstr st' cid
          let sched'' := updateAfterStep st''.sched cid res.status
          some { st'' with sched := sched'' }

/-! Proof-facing scheduler contracts and lemmas live in
`Runtime.Proofs.ProtocolMachine.SchedulerContracts` and
`Runtime.Proofs.ProtocolMachine.Scheduler`. -/
