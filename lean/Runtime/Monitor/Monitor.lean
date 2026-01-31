import Runtime.VM.Core
import Runtime.Compat.Inv

/-
The Problem. The runtime needs a unified monitor that tracks session
kinds uniformly, allowing typing and invariants to be checked at a
single interface.

Solution Structure. Define a lightweight monitor interface parametric
over session kinds. Failure semantics live in a separate module to avoid
cyclic dependencies on VM state.
-/

/-!
# Task 23: Unified Monitor

Monitor consistency across session kinds
from iris_runtime_2.md §14.

## Definitions

### Unified Monitor
- `SessionKind` — protocol, guard, handler, ghost
- `WellTypedInstr` — unified typing judgment
- `SessionMonitor` — monitor state tracking all session kinds
- `monitor_sound`, `unified_monitor_preserves`
- `cross_kind_interop`

Failure model definitions live in `Runtime.Failure.Failure`.

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

def SessionKind.sid? {γ : Type u} : SessionKind γ → Option SessionId :=
  -- Extract a protocol session id when present.
  fun
  | .protocol sid => some sid
  | _ => none

inductive WellTypedInstr {γ ε : Type u} [GuardLayer γ] [EffectModel ε] :
    Instr γ ε → SessionKind γ → LocalType → LocalType → Prop where
  | wt_step (i : Instr γ ε) (sk : SessionKind γ) (L L' : LocalType) :
      -- Placeholder typing judgment for unified monitor.
      WellTypedInstr i sk L L'
  | wt_invoke (action : EffectModel.EffectAction ε) (hsid : HandlerId) :
      -- Handler session typing for invoke steps.
      WellTypedInstr (.invoke action) (.handler hsid) (EffectModel.handlerType action) .end_

structure SessionMonitor (γ : Type u) where
  -- Monitor transition per session kind.
  step : SessionKind γ → Option (SessionKind γ)

def monitorAllows {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    (_m : SessionMonitor γ) (_i : Instr γ ε) : Bool :=
  -- Placeholder: monitor accepts all instructions.
  true

def monitor_sound {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    (m : SessionMonitor γ) : Prop :=
  -- Well-typed instructions are accepted by the monitor.
  ∀ (i : Instr γ ε) (sk : SessionKind γ) (L L' : LocalType),
    WellTypedInstr i sk L L' → monitorAllows m i = true

def unified_monitor_preserves {γ : Type u} (m : SessionMonitor γ) : Prop :=
  -- Monitor steps preserve protocol session ids when present.
  ∀ sk sk', m.step sk = some sk' → SessionKind.sid? sk' = SessionKind.sid? sk

def cross_kind_interop {γ : Type u} (m : SessionMonitor γ) : Prop :=
  -- Distinct session kinds step independently of protocol ids.
  ∀ sk1 sk2, sk1 ≠ sk2 →
    SessionKind.sid? sk1 = none ∨ SessionKind.sid? sk2 = none ∨ SessionKind.sid? sk1 ≠ SessionKind.sid? sk2 →
    (m.step sk1).isSome → (m.step sk2).isSome
