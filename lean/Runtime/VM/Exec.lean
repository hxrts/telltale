import Runtime.VM.Exec.Helpers
import Runtime.VM.Exec.Steps

/-
The Problem. Provide the VM's single-instruction stepper used by the
scheduler and language instance.

Solution Structure. Factor per-case helpers and assemble the main stepper
from monitor checks, cost charging, and instruction dispatch.
-/

set_option autoImplicit false

universe u

/-! ## Step assembly helpers -/

private def commitPack {ι γ π ε : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    (coroId : CoroutineId) (pack' : StepPack ι γ π ε) :
    VMState ι γ π ε × ExecResult γ :=
  -- Update the coroutine and append any observable event.
  let st' := updateCoro pack'.st coroId pack'.coro
  (appendEvent st' pack'.res.event, pack'.res)

private def execWithInstr {ι γ π ε : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    (st : VMState ι γ π ε) (coroId : CoroutineId) (coro : CoroutineState γ ε)
    (instr : Instr γ ε) : VMState ι γ π ε × ExecResult γ :=
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

private def execAtPC {ι γ π ε : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    (st : VMState ι γ π ε) (coroId : CoroutineId) (coro : CoroutineState γ ε) :
    VMState ι γ π ε × ExecResult γ :=
  -- Handle coroutine status and fetch the next instruction.
  match coro.status with
  | .done => (st, mkRes .halted none)
  | .faulted err => (st, mkRes (.faulted err) (some (.fault "faulted coroutine")))
  | _ =>
      match st.code.code[coro.pc]? with
      | none =>
          let coro' := { coro with status := .faulted (.closeFault "pc out of range") }
          let st' := updateCoro st coroId coro'
          (st', mkRes (.faulted (.closeFault "pc out of range")) (some (.fault "pc out of range")))
      | some instr => execWithInstr st coroId coro instr

/-! ## Main stepper -/

/-- Execute a single instruction for the selected coroutine. -/
def execInstr {ι γ π ε : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    (st : VMState ι γ π ε) (coroId : CoroutineId) :
    VMState ι γ π ε × ExecResult γ :=
  -- Guard against missing coroutine and delegate to the core stepper.
  match st.coroutines[coroId]? with
  | none =>
      (st, mkRes (.faulted (.closeFault "unknown coroutine")) (some (.fault "unknown coroutine")))
  | some coro => execAtPC st coroId coro
