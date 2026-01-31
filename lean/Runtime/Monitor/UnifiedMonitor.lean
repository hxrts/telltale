import Runtime.VM.Core
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

inductive SessionKind (γ : Type u) where
  -- The source kind of a monitored session action.
  | protocol (sid : SessionId)
  | guard (chainId : GuardChainId) (layer : γ)
  | handler (hsid : HandlerId)
  | ghost (gsid : GhostSessionId)

inductive WellTypedInstr {γ ε : Type u} [GuardLayer γ] [EffectModel ε] :
    Instr γ ε → SessionKind γ → LocalType → LocalType → Prop where
  | wt_step (i : Instr γ ε) (sk : SessionKind γ) (L L' : LocalType) :
      -- Placeholder typing judgment for unified monitor.
      WellTypedInstr i sk L L'

structure SessionMonitor (γ : Type u) where
  -- Monitor transition per session kind.
  step : SessionKind γ → Option (SessionKind γ)

def monitorAllows {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    (_m : SessionMonitor γ) (_i : Instr γ ε) : Bool :=
  -- Placeholder: monitor accepts all instructions.
  true

def monitor_sound {γ : Type u} (_m : SessionMonitor γ) : Prop :=
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

def Recoverable {σ : Type} (_st : σ) (_sid : SessionId) : Prop :=
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
