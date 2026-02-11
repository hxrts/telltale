import Runtime.ProgramLogic.LanguageInstance
import Runtime.VM.Model.Program
import Runtime.VM.Model.State
import Runtime.VM.Model.Violation
import Runtime.ProgramLogic.SessionWP
import IrisExtractionInstance
import Protocol.Process

/- 
The Problem. Define observable traces and adequacy statements that connect
the VM execution to protocol-level correctness claims.

Solution Structure. Provide trace/event types and placeholder adequacy
statements that will be refined by later proofs.
-/

/-! # Task 22: Observable Trace Infrastructure and VM Adequacy

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
section

/-! ## Core Adequacy Definitions -/

universe u

variable [Telltale.TelltaleIris]

-- Trace of observable events.
abbrev ObsTrace (ε : Type u) [EffectRuntime ε] := List (Nat × ObsEvent ε)

/-- Erase tick/index metadata from a trace, keeping only observable events. -/
def eraseTraceTicks {ε : Type u} [EffectRuntime ε]
    (trace : ObsTrace ε) : List (ObsEvent ε) :=
  trace.map Prod.snd

/--
Minimal observational equivalence shared by Lean and Rust traces.
Two traces are equivalent when they induce the same event sequence after
erasing index/tick metadata.
-/
def ObsEq {ε : Type u} [EffectRuntime ε]
    (t₁ t₂ : ObsTrace ε) : Prop :=
  eraseTraceTicks t₁ = eraseTraceTicks t₂

theorem ObsEq.refl {ε : Type u} [EffectRuntime ε] (t : ObsTrace ε) : ObsEq t t := by
  rfl

theorem ObsEq.symm {ε : Type u} [EffectRuntime ε]
    {t₁ t₂ : ObsTrace ε} : ObsEq t₁ t₂ → ObsEq t₂ t₁ := by
  intro h
  exact Eq.symm h

theorem ObsEq.trans {ε : Type u} [EffectRuntime ε]
    {t₁ t₂ t₃ : ObsTrace ε} : ObsEq t₁ t₂ → ObsEq t₂ t₃ → ObsEq t₁ t₃ := by
  intro h₁₂ h₂₃
  exact Eq.trans h₁₂ h₂₃

private def listGet? {α : Type} : List α → Nat → Option α
  -- Total list lookup by index.
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

/--
Step-indexed differential harness contract for canonical scenarios.
This is the Lean-side proposition consumed by Rust/Lean differential runners:
per-step traces must be observationally equivalent under `ObsEq`.
-/
def StepDiffHarness {ε : Type u} [EffectRuntime ε]
    (leanSteps rustSteps : List (ObsTrace ε)) : Prop :=
  leanSteps.length = rustSteps.length ∧
  ∀ i leanTrace rustTrace,
    listGet? leanSteps i = some leanTrace →
    listGet? rustSteps i = some rustTrace →
    ObsEq leanTrace rustTrace


def obsWithSeqNo {ε : Type u} [EffectRuntime ε]
    (idx : Nat) (ev : ObsEvent ε) : ObsEvent ε :=
  -- Replace seqNo fields with the current index.
  match ev with
  | .sent edge val _ => .sent edge val idx
  | .received edge val _ => .received edge val idx
  | _ => ev

def observeAt {ε : Type u} [EffectRuntime ε]
    (idx : Nat) (ev : TickedObsEvent ε) : ObsEvent ε :=
  -- Project observable events to indexed events with seqNo = index.
  obsWithSeqNo idx ev.event

def observe {ε : Type u} [EffectRuntime ε]
    (ev : TickedObsEvent ε) : ObsEvent ε :=
  -- Index-free projection defaults seqNo to 0 for V1 convenience.
  observeAt 0 ev

def obsTraceOf {ε : Type u} [EffectRuntime ε]
    (trace : List (TickedObsEvent ε)) : ObsTrace ε :=
  -- Enumerate events and keep the observable subset with indices.
  let rec go (idx : Nat) (evs : List (TickedObsEvent ε)) : ObsTrace ε :=
    match evs with
    | [] => []
    | ev :: rest =>
        let tail := go (idx + 1) rest
        let obs := observeAt idx ev
        (idx, obs) :: tail
  go 0 trace

def SentAt {ε : Type u} [EffectRuntime ε]
    (trace : ObsTrace ε) (idx : Nat) (e : Edge) (v : Value) : Prop :=
  -- Event at idx is a send of v on e (seqNo ignored).
  ∃ n seq, listGet? trace idx = some (n, ObsEvent.sent e v seq)

def RecvAt {ε : Type u} [EffectRuntime ε]
    (trace : ObsTrace ε) (idx : Nat) (e : Edge) (v : Value) : Prop :=
  -- Event at idx is a receive of v on e (seqNo ignored).
  ∃ n seq, listGet? trace idx = some (n, ObsEvent.received e v seq)

def SendBeforeObs {ε : Type u} [EffectRuntime ε]
    (trace : ObsTrace ε) (e : Edge) (v1 v2 : Value) : Prop :=
  -- Send ordering derived from trace indices.
  ∃ i j, i < j ∧ SentAt trace i e v1 ∧ SentAt trace j e v2

def RecvBeforeObs {ε : Type u} [EffectRuntime ε]
    (trace : ObsTrace ε) (e : Edge) (v1 v2 : Value) : Prop :=
  -- Receive ordering derived from trace indices.
  ∃ i j, i < j ∧ RecvAt trace i e v1 ∧ RecvAt trace j e v2

def CausallyConsistent {ε : Type u} [EffectRuntime ε]
    (trace : ObsTrace ε) : Prop :=
  -- Every receive is preceded by a matching send.
  ∀ j e v, RecvAt trace j e v → ∃ i, i < j ∧ SentAt trace i e v

def FIFOConsistent {ε : Type u} [EffectRuntime ε]
    (trace : ObsTrace ε) : Prop :=
  -- Receive order respects send order for each edge.
  ∀ e v1 v2, SendBeforeObs trace e v1 v2 → RecvBeforeObs trace e v1 v2

def session_state_interp {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : iProp :=
  -- Interpret the concrete VM state as logical resources.
  iProp.sep (iProp.pure (WFVMState st))
    (iProp.pure (sessionStore_refines_envs st.sessions))

def vm_adequacy {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν] : Prop :=
  -- V1 adequacy: observable traces are causally and FIFO consistent.
  ∀ (st : VMState ι γ π ε ν), WFVMState st →
    let obs := obsTraceOf (ε:=ε) st.obsTrace;
    CausallyConsistent obs ∧ FIFOConsistent obs

theorem vm_adequacy_of_trace_consistency
    {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (hCausal : ∀ st : VMState ι γ π ε ν, WFVMState st →
      CausallyConsistent (obsTraceOf (ε:=ε) st.obsTrace))
    (hFIFO : ∀ st : VMState ι γ π ε ν, WFVMState st →
      FIFOConsistent (obsTraceOf (ε:=ε) st.obsTrace)) :
    vm_adequacy (ι:=ι) (γ:=γ) (π:=π) (ε:=ε) (ν:=ν) := by
  intro st hWF
  exact ⟨hCausal st hWF, hFIFO st hWF⟩

def no_phantom_events {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν] : Prop :=
  -- Every observed event comes from some step event at that index.
  ∀ (st : VMState ι γ π ε ν) idx ev,
    (idx, ev) ∈ obsTraceOf (ε:=ε) st.obsTrace →
      ∃ stepEv ∈ st.obsTrace, observeAt (ε:=ε) idx stepEv = ev
omit [Telltale.TelltaleIris] in
private theorem go_mem {ε : Type u} [EffectRuntime ε]
    {start : Nat} {evs : List (TickedObsEvent ε)} {idx : Nat} {ev : ObsEvent ε}
    (h : (idx, ev) ∈ obsTraceOf.go start evs) :
    ∃ stepEv ∈ evs, observeAt idx stepEv = ev := by
  induction evs generalizing start idx ev with
  | nil => simp [obsTraceOf.go] at h
  | cons hd tl ih =>
    have hdef : obsTraceOf.go start (hd :: tl) =
      ((start, observeAt start hd) :: obsTraceOf.go (start + 1) tl : ObsTrace ε) := rfl
    rw [hdef, List.mem_cons] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact ⟨hd, .head tl, rfl⟩
    · obtain ⟨stepEv, hm, he⟩ := ih h
      exact ⟨stepEv, List.mem_cons_of_mem hd hm, he⟩

omit [Telltale.TelltaleIris] in
theorem no_phantom_events_holds {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν] :
    no_phantom_events (ι:=ι) (γ:=γ) (π:=π) (ε:=ε) (ν:=ν) := by
  intro st idx ev hmem
  exact go_mem hmem

def compile_refines {γ ε ν : Type} [GuardLayer γ] [EffectRuntime ε]
    [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    (_p : Process) (_roles : RoleSet) (_types : Role → LocalType)
    (_chain : GuardChain γ) : Prop :=
  -- V1 refinement witness: there exists a program image matching projected
  -- local types and role entry points.
  ∃ prog : Program γ ε,
    prog.localTypes = programLocalTypes _roles _types ∧
    prog.entryPoints = _roles.map (fun r => (r, 0)) ∧
    prog.code.size = 1

theorem compile_refines_holds {γ ε ν : Type} [GuardLayer γ] [EffectRuntime ε]
    [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    (p : Process) (roles : RoleSet) (types : Role → LocalType) (chain : GuardChain γ) :
    compile_refines (γ:=γ) (ε:=ε) (ν:=ν) p roles types chain := by
  unfold compile_refines
  refine ⟨{ code := #[Instr.halt]
          , entryPoints := roles.map (fun r => (r, 0))
          , localTypes := programLocalTypes roles types
          , handlerTypes := []
          , metadata := ProgramMeta.empty }, ?_⟩
  simp [programLocalTypes]
