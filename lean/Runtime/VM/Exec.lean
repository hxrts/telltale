import Runtime.VM.ExecHelpers
import Runtime.VM.ExecSteps

/-!
# Main Instruction Stepper

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
halted, faulted, or triggered a structural change (spawn, transfer, fork, join, abort).
-/

set_option autoImplicit false

universe u

/-! ## Step assembly helpers -/

def commitPack {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (coroId : CoroutineId) (pack' : StepPack ι γ π ε ν) :
    VMState ι γ π ε ν × ExecResult γ ε :=
  -- Update the coroutine and append any observable event.
  let st' := updateCoro pack'.st coroId pack'.coro
  (appendEvent st' pack'.res.event, pack'.res)

def execWithInstr {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coroId : CoroutineId) (coro : CoroutineState γ ε)
    (instr : Instr γ ε) : VMState ι γ π ε ν × ExecResult γ ε :=
  -- Enforce monitor typing and cost budget before execution.
  if monitorAllows st.monitor instr then
    match chargeCost st.config coro instr with
    | none =>
        let pack' := faultPack st coro .outOfCredits "out of credits"
        commitPack coroId pack'
    | some coro' =>
        let pack' := stepInstr st coro' instr
        commitPack coroId pack'
  else
    let pack' := faultPack st coro (.specFault "monitor rejected") "monitor rejected"
    commitPack coroId pack'

def execAtPC {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
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
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coroId : CoroutineId) :
    VMState ι γ π ε ν × ExecResult γ ε :=
  -- Guard against missing coroutine and delegate to the core stepper.
  match st.coroutines[coroId]? with
  | none =>
      (st, mkRes (.faulted (.closeFault "unknown coroutine")) (some StepEvent.internal))
  | some coro => execAtPC st coroId coro
