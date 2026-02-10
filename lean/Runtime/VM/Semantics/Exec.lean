import Runtime.VM.Semantics.ExecHelpers
import Runtime.VM.Semantics.ExecSteps

/-! # Main Instruction Stepper

`execInstr`, the top-level entry point for executing one instruction on a coroutine.
The execution pipeline is:

1. Look up the coroutine by id (fault if missing).
2. Check coroutine status (skip if done/faulted).
3. Fetch the instruction at the current PC (fault if out of range).
4. Run the session monitor type check (fault if rejected).
5. Charge the instruction's cost against the coroutine's budget (fault if insufficient).
6. Dispatch to the per-instruction step function via `stepInstr`.
7. Write back the updated coroutine and append any observable event to the trace.

The scheduler calls `execInstr` in a loop. Each call produces an updated `VMState`
and an `ExecResult` indicating whether the coroutine continued, yielded, blocked,
halted, faulted, or triggered a structural change (spawn, transfer, fork, join, abort). -/

/-
The Problem. The scheduler needs a single entry point for executing one instruction
that handles all the setup (lookup, status check, fetch, monitor, cost) and teardown
(commit, event emission) uniformly across all instruction types.

Solution Structure. The `execInstr` function implements the 7-stage pipeline: lookup,
status check, fetch, monitor, cost charge, dispatch via `stepInstr`, and commit.
`commitPack` writes back coroutine state and appends observable events. Returns
`ExecResult` encoding continuation, yield, block, halt, fault, or structural changes.
-/

set_option autoImplicit false

universe u

/-! ## Step assembly helpers -/

private def outputConditionClaimOfEvent {ε : Type u} [EffectRuntime ε]
    (ev : StepEvent ε) : Option OutputConditionClaim :=
  match ev with
  | .internal => none
  | .obs _ =>
      some
        { predicateRef := "vm.observable_output"
        , witnessRef := none
        , outputDigest := "vm.output_digest.unspecified" }

private def appendOutputConditionCheck {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (check : OutputConditionCheck) : VMState ι γ π ε ν :=
  { st with outputConditionChecks := st.outputConditionChecks ++ [check] }

def commitPack {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (stBase : VMState ι γ π ε ν) (coroId : CoroutineId) (pack' : StepPack ι γ π ε ν) :
    VMState ι γ π ε ν × ExecResult γ ε :=
  -- Gate protocol-visible outputs on output-condition verification.
  match pack'.res.event.bind outputConditionClaimOfEvent with
  | none =>
      let st' := updateCoro pack'.st coroId pack'.coro
      (appendEvent st' pack'.res.event, pack'.res)
  | some claim =>
      let passed := stBase.config.outputCondition.verify claim
      let check : OutputConditionCheck := { claim := claim, passed := passed }
      if passed then
        let st' := updateCoro pack'.st coroId pack'.coro
        let st'' := appendOutputConditionCheck st' check
        (appendEvent st'' pack'.res.event, pack'.res)
      else
        let err : Fault γ := .specFault s!"output condition rejected: {claim.predicateRef}"
        let coro' := { pack'.coro with status := .faulted err }
        let st' := updateCoro stBase coroId coro'
        let st'' := appendOutputConditionCheck st' check
        (st'', mkRes (.faulted err) (some StepEvent.internal))

def execWithInstr {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coroId : CoroutineId) (coro : CoroutineState γ ε)
    (instr : Instr γ ε) : VMState ι γ π ε ν × ExecResult γ ε :=
  -- Enforce monitor typing and cost budget before execution.
  let monitorPasses :=
    match st.config.monitorMode with
    | .off => true
    | .sessionTypePrecheck => monitorAllows st.monitor instr
  if monitorPasses then
    match chargeCost st.config coro instr with
    | none =>
        let pack' := faultPack st coro .outOfCredits "out of credits"
        commitPack st coroId pack'
    | some coro' =>
        let pack' := stepInstr st coro' instr
        commitPack st coroId pack'
  else
    let pack' := faultPack st coro (.specFault "monitor rejected") "monitor rejected"
    commitPack st coroId pack'

def execAtPC {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coroId : CoroutineId) (coro : CoroutineState γ ε) :
    VMState ι γ π ε ν × ExecResult γ ε :=
  -- Handle coroutine status and fetch the next instruction.
  match coro.status with
  | .done => (st, mkRes .halted none)
  | .faulted err => (st, mkRes (.faulted err) (some StepEvent.internal))
  | _ =>
      match st.programs[coro.programId]? with
      | none =>
          let coro' := { coro with status := .faulted (.closeFault "unknown program") }
          let st' := updateCoro st coroId coro'
          (st', mkRes (.faulted (.closeFault "unknown program")) (some StepEvent.internal))
      | some prog =>
          match prog.code[coro.pc]? with
          | none =>
              let coro' := { coro with status := .faulted (.closeFault "pc out of range") }
              let st' := updateCoro st coroId coro'
              (st', mkRes (.faulted (.closeFault "pc out of range")) (some StepEvent.internal))
          | some instr => execWithInstr st coroId coro instr

/-! ## Main stepper -/

/-- Execute a single instruction for the selected coroutine. -/
def execInstr {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coroId : CoroutineId) :
    VMState ι γ π ε ν × ExecResult γ ε :=
  -- Guard against missing coroutine and delegate to the core stepper.
  match st.coroutines[coroId]? with
  | none =>
      (st, mkRes (.faulted (.closeFault "unknown coroutine")) (some StepEvent.internal))
  | some coro => execAtPC st coroId coro
