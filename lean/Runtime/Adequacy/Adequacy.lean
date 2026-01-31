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

inductive ObsEvent (ε : Type) [EffectModel ε] where
  -- Observable events emitted by VM execution.
  | sent (edge : Edge) (val : Value) (seqNo : Nat)
  | received (edge : Edge) (val : Value) (seqNo : Nat)
  | offered (edge : Edge) (label : Label)
  | chose (edge : Edge) (label : Label)
  | acquired (layer : Namespace) (endpoint : Endpoint)
  | released (layer : Namespace) (endpoint : Endpoint)
  | invoked (endpoint : Endpoint) (action : EffectModel.EffectAction ε)
  | opened (sid : SessionId) (roles : RoleSet)
  | closed (sid : SessionId)
  | epochAdvanced (sid : SessionId) (epoch : Nat)
  | transferred (endpoint : Endpoint) (fromCoro toCoro : Nat)
  | forked (sid : SessionId) (ghostSid : GhostSessionId)
  | joined (sid : SessionId)
  | aborted (sid : SessionId)
  | tagged (endpoint : Endpoint) (fact : KnowledgeFact)
  | checked (endpoint : Endpoint) (target : Role) (permitted : Bool)

-- Trace of observable events.
abbrev ObsTrace (ε : Type) [EffectModel ε] := List (Nat × ObsEvent ε)


def observe {ε : Type} [EffectModel ε] (ev : StepEvent) : Option (ObsEvent ε) :=
  -- Project internal step events to observable events.
  match ev with
  | .send edge _ v => some (.sent edge v 0)
  | .recv edge _ v => some (.received edge v 0)
  | .open sid => some (.opened sid [])
  | .close sid => some (.closed sid)
  | .fault _ => none

def CausallyConsistent {ε : Type} [EffectModel ε] (_trace : ObsTrace ε) : Prop :=
  -- Placeholder for causal consistency of traces.
  True
def FIFOConsistent {ε : Type} [EffectModel ε] (_trace : ObsTrace ε) : Prop :=
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
