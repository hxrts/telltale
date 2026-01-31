import Runtime.ProgramLogic.SessionWP
import Runtime.Compat.Inv

/-!
# Task 23: Unified Monitor and Failure Model

Monitor consistency across session kinds and crash safety
from iris_runtime_2.md §§9, 14.

## Definitions

### Unified Monitor
- `SessionKind` — protocol, guard, handler, ghost
- `WellTypedInstr` — unified typing judgment
- `SessionMonitor` — monitor state tracking all session kinds
- `monitor_sound`, `unified_monitor_preserves`
- `cross_kind_interop`

### Failure Model
- `Failure`, `FStep` — failure-aware step relation
- `Recoverable` — recovery predicate
- `crash_nonparticipant_preserves`
- `participant_failover`
- `crash_close_safe`

Dependencies: Task 19, Shim.Invariants.
-/

set_option autoImplicit false

universe u

inductive SessionKind where
  -- The source kind of a monitored session action.
  | protocol (sid : SessionId)
  | guard (chainId : Nat) (layer : Namespace)
  | handler (hsid : Nat)
  | ghost (gsid : Nat)

inductive WellTypedInstr {γ ε : Type u} [GuardLayer γ] [EffectModel ε] :
    Instr γ ε → SessionKind → LocalType → LocalType → Prop where
  | wt_step (i : Instr γ ε) (sk : SessionKind) (L L' : LocalType) :
      -- Placeholder typing judgment for unified monitor.
      WellTypedInstr i sk L L'

structure SessionMonitor where
  -- Monitor transition per session kind.
  step : SessionKind → Option SessionKind

def monitor_sound (_m : SessionMonitor) : Prop :=
  -- Placeholder: monitor soundness invariant.
  True
def unified_monitor_preserves : Prop :=
  -- Placeholder: monitor preserves typing across steps.
  True
def cross_kind_interop : Prop :=
  -- Placeholder: cross-kind interop property.
  True

inductive Failure where
  -- Failure cases for sessions.
  | crash (sid : SessionId)
  | timeout (sid : SessionId)
  deriving Repr

inductive FStep where
  -- Failure-aware step relation (placeholder).
  | step (f : Failure)
  deriving Repr

def Recoverable {ι γ π ε : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    (_st : VMState ι γ π ε) (_sid : SessionId) : Prop :=
  -- Placeholder: recovery predicate.
  True

def crash_nonparticipant_preserves : Prop :=
  -- Placeholder: non-participant crash preserves correctness.
  True
def participant_failover : Prop :=
  -- Placeholder: participant failover property.
  True
def crash_close_safe : Prop :=
  -- Placeholder: crash-close safety.
  True
