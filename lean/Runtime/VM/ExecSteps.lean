import Runtime.VM.ExecHelpers
import Runtime.VM.ExecComm
import Runtime.VM.ExecSession
import Runtime.VM.ExecGuardEffect
import Runtime.VM.ExecSpeculation
import Runtime.VM.ExecOwnership
import Runtime.VM.ExecControl

/-!
# Instruction Dispatcher

`stepInstr`, the single match statement that routes each `Instr` variant to its
corresponding step function defined in the `Exec*.lean` files. This is the only
place where the full instruction set is enumerated. Adding a new instruction means
adding one arm here and one step function in the appropriate `Exec*.lean` module.

Called by `Exec.lean`'s `execWithInstr` after monitor and cost checks have passed.
-/

set_option autoImplicit false

universe u

/-! ## Instruction dispatcher -/

def stepInstr {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (i : Instr γ ε) : StepPack ι γ π ε ν :=
  -- Call the appropriate per-instruction helper.
  match i with
  | .send chan val => stepSend st coro chan val
  | .recv chan dst => stepRecv st coro chan dst
  | .offer chan lbl => stepOffer st coro chan lbl
  | .choose chan table => stepChoose st coro chan table
  | .acquire layer dst => stepAcquire st coro layer dst
  | .release layer evidence => stepRelease st coro layer evidence
  | .invoke action => stepInvoke st coro action
  | .open _roles localTypes handlers dsts => stepOpen st coro localTypes handlers dsts
  | .close session => stepClose st coro session
  | .fork sid => stepFork st coro sid
  | .join => stepJoin st coro
  | .abort => stepAbort st coro
  | .transfer ep target bundle => stepTransfer st coro ep target bundle
  | .tag fact dst => stepTag st coro fact dst
  | .check knowledge target dst => stepCheck st coro knowledge target dst
  | .loadImm dst v => stepLoadImm st coro dst v
  | .mov dst src => stepMov st coro dst src
  | .jmp target => stepJmp st coro target
  | .spawn target args => stepSpawn st coro target args
  | .yield => stepYield st coro
  | .halt => haltPack st coro
