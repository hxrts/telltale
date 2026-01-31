import Runtime.VM.Exec.Helpers
import Runtime.VM.Exec.Steps

/-
The Problem. Provide the VM's single-instruction stepper used by the
scheduler and language instance.

Solution Structure. Combine cost charging with instruction dispatch and
update the coroutine array plus observable trace.
-/

set_option autoImplicit false

universe u

/-- Execute a single instruction for the selected coroutine. -/
def execInstr {ι γ π ε : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    (st : VMState ι γ π ε) (coroId : CoroutineId) :
    VMState ι γ π ε × ExecResult γ :=
  -- Guard against missing coroutine or invalid PC.
  match st.coroutines[coroId]? with
  | none =>
      (st, mkRes (.faulted (.closeFault "unknown coroutine")) (some (.fault "unknown coroutine")))
  | some coro =>
      match coro.status with
      | .done => (st, mkRes .halted none)
      | .faulted err => (st, mkRes (.faulted err) (some (.fault "faulted coroutine")))
      | _ =>
          match st.code[coro.pc]? with
          | none =>
              let coro' := { coro with status := .faulted (.closeFault "pc out of range") }
              let st' := updateCoro st coroId coro'
              (st', mkRes (.faulted (.closeFault "pc out of range")) (some (.fault "pc out of range")))
          | some instr =>
              match chargeCost st.config coro instr with
              | none =>
                  let pack' := faultPack st coro .outOfCredits "out of credits"
                  let st' := updateCoro pack'.st coroId pack'.coro
                  (appendEvent st' pack'.res.event, pack'.res)
              | some coro' =>
                  let pack' := stepInstr st coro' instr
                  let st' := updateCoro pack'.st coroId pack'.coro
                  (appendEvent st' pack'.res.event, pack'.res)
