import Runtime.VM.ExecHelpers

/-!
# Speculation Instruction Semantics

Step functions for `fork`, `join`, and `abort`, the speculation lifecycle
described in `runtime.md` §17.

`stepFork` enters speculative mode by reading a ghost session id from a register
and setting `specState` on the coroutine. `stepJoin` exits speculation by clearing
the ghost state (a real implementation would verify `matchesRealState`). `stepAbort`
also clears ghost state but discards speculative work (always safe, no token required).

These are V1 stubs: depth accounting, checkpoint/restore, and reconciliation
verification are deferred to V2 when ghost sessions are fully implemented.
-/

set_option autoImplicit false

universe u

/-! ## Speculation semantics -/

def stepFork {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (sidReg : Reg) : StepPack ι γ π ε ν :=
  -- Enter speculation mode for a ghost session id.
  match readReg coro.regs sidReg with
  | some (.nat gsid) =>
      let coro' := advancePc { coro with specState := some { ghostSid := gsid, depth := 0 } }
      pack coro' st (mkRes (.forked gsid) (some (.obs (.forked gsid gsid))))
  | some v =>
      faultPack st coro (.typeViolation .nat (valTypeOf v)) "bad fork operand"
  | none =>
      faultPack st coro .outOfRegisters "missing fork operand"


def stepJoin {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) : StepPack ι γ π ε ν :=
  -- Join speculation: clear ghost state.
  let sid :=
    match coro.specState with
    | some s => s.ghostSid
    | none => 0
  let coro' := advancePc { coro with specState := none }
  pack coro' st (mkRes .joined (some (.obs (.joined sid))))


def stepAbort {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) : StepPack ι γ π ε ν :=
  -- Abort speculation: clear ghost state.
  let sid :=
    match coro.specState with
    | some s => s.ghostSid
    | none => 0
  let coro' := advancePc { coro with specState := none }
  pack coro' st (mkRes .aborted (some (.obs (.aborted sid))))
