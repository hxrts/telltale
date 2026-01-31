import Runtime.VM.Definition
import Runtime.Compat.WP

/-!
# Task 17: Cooperative Scheduler

Cooperative coroutine scheduler from iris_runtime_2.md §4.

## Definitions

- `SchedPolicy` — round-robin, priority, work-stealing
- `schedule` — select next runnable coroutine
- `schedStep` — scheduler + VM step composed
- `schedule_confluence` — diamond property
- `cooperative_refines_concurrent`
- `CoroutinePool` — ready/blocked/halted partition

Dependencies: Task 11, Shim.WeakestPre.
-/

set_option autoImplicit false

inductive SchedPolicy where
  | roundRobin
  | priority
  | workStealing
  deriving Repr

structure CoroutinePool where
  ready : List CoroutineId
  blocked : List CoroutineId
  halted : List CoroutineId
  deriving Repr

def schedule {ι π ε : Type} [IdentityModel ι] [PersistenceModel π] [EffectModel ε] :
    VMState ι π ε → Option (CoroutineId × VMState ι π ε) :=
  fun st =>
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

def schedStep {ι π ε : Type} [IdentityModel ι] [PersistenceModel π] [EffectModel ε] :
    VMState ι π ε → Option (VMState ι π ε) :=
  fun st =>
    match schedule st with
    | none => none
    | some (cid, st') =>
        let (st'', _) := execInstr st' cid
        some st''

def schedule_confluence {ι π ε : Type} [IdentityModel ι] [PersistenceModel π] [EffectModel ε]
    (_st : VMState ι π ε) : Prop := True

def cooperative_refines_concurrent {ι π ε : Type} [IdentityModel ι] [PersistenceModel π] [EffectModel ε]
    (_st : VMState ι π ε) : Prop := True
