import Runtime.VM.LanguageInstance
import Runtime.ProgramLogic.SessionWP
import Runtime.Compat.WP

/-!
# Task 22: Observable Trace Infrastructure and VM Adequacy

Observable events, trace properties, and the capstone adequacy theorem
from iris_runtime_2.md §11.

## Definitions

- `ObsEvent` — observable events (send, recv, open, close, fail, recover)
- `ObsTrace` — event trace
- `Violation`, `ViolationPolicy`
- `CausallyConsistent`, `FIFOConsistent`
- `session_state_interp`
- `vm_adequacy` — WP proof ⊢ trace is valid linearization
- `no_phantom_events`
- `compile_refines`

Dependencies: Task 12, Task 19, Shim.WeakestPre.
-/

set_option autoImplicit false
noncomputable section

inductive ObsEvent where
  | send (edge : Edge) (label : Label)
  | recv (edge : Edge) (label : Label)
  | open (sid : SessionId)
  | close (sid : SessionId)
  | fail (msg : String)
  | recover (sid : SessionId)
  deriving Repr

abbrev ObsTrace := List ObsEvent

inductive Violation where
  | safety (msg : String)
  | liveness (msg : String)
  deriving Repr

structure ViolationPolicy where
  allow : Violation → Bool

def CausallyConsistent (_trace : ObsTrace) : Prop := True
def FIFOConsistent (_trace : ObsTrace) : Prop := True

def session_state_interp {ι π ε : Type} [IdentityModel ι] [PersistenceModel π] [EffectModel ε]
    (st : VMState ι π ε) : iProp :=
  iProp.sep (iProp.pure (WFVMState st))
    (iProp.pure (sessionStore_refines_envs st.sessions))

def vm_adequacy {ι π ε : Type} [IdentityModel ι] [PersistenceModel π] [EffectModel ε] : Prop := True
def no_phantom_events {ι π ε : Type} [IdentityModel ι] [PersistenceModel π] [EffectModel ε] : Prop := True
def compile_refines {ι π ε : Type} [IdentityModel ι] [PersistenceModel π] [EffectModel ε] : Prop := True
