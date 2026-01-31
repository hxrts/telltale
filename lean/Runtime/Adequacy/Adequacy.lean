import Runtime.VM.LanguageInstance
import Runtime.VM.Program
import Runtime.VM.Violation
import Runtime.ProgramLogic.SessionWP
import Runtime.Compat.WP

/- 
The Problem. Define observable traces and adequacy statements that connect
the VM execution to protocol-level correctness claims.

Solution Structure. Provide trace/event types and placeholder adequacy
statements that will be refined by later proofs.
-/

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
  -- Observable events emitted by VM execution.
  | send (edge : Edge) (label : Label)
  | recv (edge : Edge) (label : Label)
  | open (sid : SessionId)
  | close (sid : SessionId)
  | fail (msg : String)
  | recover (sid : SessionId)
  deriving Repr

-- Trace of observable events.
abbrev ObsTrace := List ObsEvent -- Linearized execution trace.


def CausallyConsistent (_trace : ObsTrace) : Prop :=
  -- Placeholder for causal consistency of traces.
  True
def FIFOConsistent (_trace : ObsTrace) : Prop :=
  -- Placeholder for FIFO consistency of traces.
  True

def session_state_interp {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : iProp :=
  -- Interpret the concrete VM state as logical resources.
  iProp.sep (iProp.pure (WFVMState st))
    (iProp.pure (sessionStore_refines_envs st.sessions))

def vm_adequacy {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν] : Prop :=
  -- Placeholder adequacy statement.
  True
def no_phantom_events {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν] : Prop :=
  -- Placeholder for trace soundness.
  True
def compile_refines {γ ε ν : Type} [GuardLayer γ] [EffectModel ε]
    [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    (_p : Process) (_roles : RoleSet) (_types : Role → LocalType)
    (_chain : GuardChain γ) : Prop :=
  -- Placeholder: compiled bytecode refines the source process.
  True
