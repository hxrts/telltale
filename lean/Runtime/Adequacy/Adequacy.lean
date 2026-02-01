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
  | acquired (layer : Namespace)
  | released (layer : Namespace)
  | invoked (handler : HandlerId)
  | opened (sid : SessionId) (roles : RoleSet)
  | closed (sid : SessionId)
  | epochAdvanced (sid : SessionId) (epoch : Nat)
  | transferred (endpoint : Endpoint) (fromCoro toCoro : Nat)
  | forked (sid : SessionId) (ghostSid : GhostSessionId)
  | joined (sid : SessionId)
  | aborted (sid : SessionId)
  | tagged (fact : KnowledgeFact)
  | checked (target : Role) (permitted : Bool)

-- Trace of observable events.
abbrev ObsTrace (ε : Type) [EffectModel ε] := List (Nat × ObsEvent ε)

private def listGet? {α : Type} : List α → Nat → Option α
  -- Total list lookup by index.
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n


def observeAt {ε : Type} [EffectModel ε]
    (idx : Nat) (ev : StepEvent) : Option (ObsEvent ε) :=
  -- Project internal events to observable events with seqNo = index.
  match ev with
  | .send edge _ v => some (.sent edge v idx)
  | .recv edge _ v => some (.received edge v idx)
  | .offer edge lbl => some (.offered edge lbl)
  | .choose edge lbl => some (.chose edge lbl)
  | .acquire layer => some (.acquired layer)
  | .release layer => some (.released layer)
  | .invoke handler => some (.invoked handler)
  | .transfer ep fromCoro toCoro => some (.transferred ep fromCoro toCoro)
  | .tag fact => some (.tagged fact)
  | .check target ok => some (.checked target ok)
  | .open sid => some (.opened sid [])
  | .close sid => some (.closed sid)
  | .fault _ => none

def observe {ε : Type} [EffectModel ε] (ev : StepEvent) : Option (ObsEvent ε) :=
  -- Index-free projection defaults seqNo to 0 for V1 convenience.
  observeAt (ε:=ε) 0 ev

def obsTraceOf {ε : Type} [EffectModel ε]
    (trace : List StepEvent) : ObsTrace ε :=
  -- Enumerate events and keep the observable subset with indices.
  let rec go (idx : Nat) (evs : List StepEvent) : ObsTrace ε :=
    match evs with
    | [] => []
    | ev :: rest =>
        let tail := go (idx + 1) rest
        match observeAt (ε:=ε) idx ev with
        | none => tail
        | some obs => (idx, obs) :: tail
  go 0 trace

def SentAt {ε : Type} [EffectModel ε]
    (trace : ObsTrace ε) (idx : Nat) (e : Edge) (v : Value) : Prop :=
  -- Event at idx is a send of v on e (seqNo ignored).
  ∃ n seq, listGet? trace idx = some (n, ObsEvent.sent e v seq)

def RecvAt {ε : Type} [EffectModel ε]
    (trace : ObsTrace ε) (idx : Nat) (e : Edge) (v : Value) : Prop :=
  -- Event at idx is a receive of v on e (seqNo ignored).
  ∃ n seq, listGet? trace idx = some (n, ObsEvent.received e v seq)

def SendBeforeObs {ε : Type} [EffectModel ε]
    (trace : ObsTrace ε) (e : Edge) (v1 v2 : Value) : Prop :=
  -- Send ordering derived from trace indices.
  ∃ i j, i < j ∧ SentAt trace i e v1 ∧ SentAt trace j e v2

def RecvBeforeObs {ε : Type} [EffectModel ε]
    (trace : ObsTrace ε) (e : Edge) (v1 v2 : Value) : Prop :=
  -- Receive ordering derived from trace indices.
  ∃ i j, i < j ∧ RecvAt trace i e v1 ∧ RecvAt trace j e v2

def CausallyConsistent {ε : Type} [EffectModel ε] (trace : ObsTrace ε) : Prop :=
  -- Every receive is preceded by a matching send.
  ∀ j e v, RecvAt trace j e v → ∃ i, i < j ∧ SentAt trace i e v

def FIFOConsistent {ε : Type} [EffectModel ε] (trace : ObsTrace ε) : Prop :=
  -- Receive order respects send order for each edge.
  ∀ e v1 v2, SendBeforeObs trace e v1 v2 → RecvBeforeObs trace e v1 v2

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
  -- V1 adequacy: observable traces are causally and FIFO consistent.
  ∀ (st : VMState ι γ π ε ν), WFVMState st →
    let obs := obsTraceOf (ε:=ε) st.obsTrace
    CausallyConsistent obs ∧ FIFOConsistent obs
def no_phantom_events {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν] : Prop :=
  -- Every observed event comes from some step event at that index.
  ∀ (st : VMState ι γ π ε ν) idx ev,
    (idx, ev) ∈ obsTraceOf (ε:=ε) st.obsTrace →
      ∃ stepEv ∈ st.obsTrace, observeAt (ε:=ε) idx stepEv = some ev
def compile_refines {γ ε ν : Type} [GuardLayer γ] [EffectModel ε]
    [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    (_p : Process) (_roles : RoleSet) (_types : Role → LocalType)
    (_chain : GuardChain γ) : Prop :=
  -- Compiler preserves role-local types and entry points.
  let prog := compile (γ:=γ) (ε:=ε) _p _roles _types _chain
  prog.entryPoints = _roles.map (fun r => (r, 0)) ∧
  prog.localTypes = programLocalTypes _roles _types
