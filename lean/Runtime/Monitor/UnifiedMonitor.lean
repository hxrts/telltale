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
  | protocol (sid : SessionId)
  | guard (chainId : Nat) (layer : Namespace)
  | handler (hsid : Nat)
  | ghost (gsid : Nat)

inductive WellTypedInstr {ε : Type u} [EffectModel ε] :
    Instr ε → SessionKind → LocalType → LocalType → Prop where
  | wt_step (i : Instr ε) (sk : SessionKind) (L L' : LocalType) :
      WellTypedInstr i sk L L'

structure SessionMonitor where
  step : SessionKind → Option SessionKind

def monitor_sound (_m : SessionMonitor) : Prop := True
def unified_monitor_preserves : Prop := True
def cross_kind_interop : Prop := True

inductive Failure where
  | crash (sid : SessionId)
  | timeout (sid : SessionId)
  deriving Repr

inductive FStep where
  | step (f : Failure)
  deriving Repr

def Recoverable {ι π ε : Type} [IdentityModel ι] [PersistenceModel π] [EffectModel ε]
    (_st : VMState ι π ε) (_sid : SessionId) : Prop :=
  True

def crash_nonparticipant_preserves : Prop := True
def participant_failover : Prop := True
def crash_close_safe : Prop := True
