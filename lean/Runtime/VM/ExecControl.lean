import Runtime.VM.ExecHelpers

/-!
# Control-Flow Instruction Semantics

Step functions for `spawn`, `loadImm`, `mov`, `jmp`, and `yield`. These are the
non-session-typed instructions that manipulate coroutine-local state (registers,
program counter) or create new coroutines.

`stepSpawn` allocates a new coroutine with copied arguments and the default cost
budget. `stepYield` cooperatively yields to the scheduler. The others are standard
register-machine operations.
-/

set_option autoImplicit false

universe u

/-! ## Control-flow semantics -/

private def copyArgs (src : RegFile) (size : Nat) (args : List Reg) : RegFile :=
  -- Copy argument registers into a fresh register file.
  let initRegs : RegFile := Array.mk (List.replicate size Value.unit)
  let rec go (idx : Nat) (regs : RegFile) (xs : List Reg) : RegFile :=
    match xs with
    | [] => regs
    | r :: rs =>
        match readReg src r with
        | none => go (idx + 1) regs rs
        | some v =>
            if h : idx < regs.size then
              go (idx + 1) (regs.set (i := idx) (v := v) (h := h)) rs
            else
              regs
  go 0 initRegs args


def stepSpawn {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (target : PC) (args : List Reg) : StepPack ι γ π ε ν :=
  -- Spawn a new coroutine with copied arguments.
  let newId := st.nextCoroId
  let newRegs := copyArgs coro.regs coro.regs.size args
  let budget := st.config.costModel.defaultBudget
  let newCoro : CoroutineState γ ε :=
    { id := newId, pc := target, regs := newRegs, status := .ready
      effectCtx := coro.effectCtx, ownedEndpoints := [], progressTokens := []
      knowledgeSet := [], costBudget := budget, specState := none }
  let coros' := st.coroutines.push newCoro
  let st' := { st with coroutines := coros', nextCoroId := newId + 1 }
  let coro' := advancePc { coro with status := .ready }
  pack coro' st' (mkRes (.spawned newId) none)


def stepLoadImm {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (dst : Reg) (v : Value) : StepPack ι γ π ε ν :=
  -- Load an immediate value into a register.
  match setReg coro.regs dst v with
  | some regs' => continuePack st { coro with regs := regs' } none
  | none => faultPack st coro .outOfRegisters "out of registers"


def stepMov {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (dst src : Reg) : StepPack ι γ π ε ν :=
  -- Move a value between registers.
  match readReg coro.regs src with
  | none => faultPack st coro .outOfRegisters "bad src reg"
  | some v =>
      match setReg coro.regs dst v with
      | none => faultPack st coro .outOfRegisters "bad dst reg"
      | some regs' => continuePack st { coro with regs := regs' } none


def stepJmp {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (target : PC) : StepPack ι γ π ε ν :=
  -- Jump to a new program counter.
  let coro' := { coro with pc := target, status := .ready }
  pack coro' st (mkRes .continue none)


def stepYield {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) : StepPack ι γ π ε ν :=
  -- Yield to scheduler by blocking the coroutine.
  let coro' := advancePc { coro with status := .blocked .spawnWait }
  pack coro' st (mkRes .yielded none)
