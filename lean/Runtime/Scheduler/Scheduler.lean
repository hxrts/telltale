import Runtime.VM.Definition
import Runtime.VM.SchedulerTypes

/-
The Problem. The runtime needs a scheduler model that can be referenced by the
VM without pulling in proof-level dependencies.

Solution Structure. Define a minimal pool view and step function that can be
refined later by scheduler correctness theorems.
-/

set_option autoImplicit false

/-! ## Scheduler state -/

structure CoroutinePool where
  -- Partition coroutines by status.
  ready : List CoroutineId
  blocked : List CoroutineId
  halted : List CoroutineId
  deriving Repr

/-! ## Scheduler step -/

def schedule {ι γ π ε : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] :
    VMState ι γ π ε → Option (CoroutineId × VMState ι γ π ε) :=
  fun st =>
    -- Pick the first runnable coroutine in array order.
    let rec go (i : Nat) : Option CoroutineId :=
      if h : i < st.coroutines.size then
        let c := st.coroutines[i]'h
        match c.status with
        | .ready | .speculating => some i
        | _ => go (i + 1)
      else
        none
    match go 0 with
    | none => none
    | some cid => some (cid, st)

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
        let (st'', _) := execInstr st' cid
        some st''

def schedule_confluence {ι γ π ε : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    (_st : VMState ι γ π ε) : Prop :=
  -- Placeholder: scheduler choices are confluent.
  True

def cooperative_refines_concurrent {ι γ π ε : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    (_st : VMState ι γ π ε) : Prop :=
  -- Placeholder: cooperative execution refines concurrent.
  True
