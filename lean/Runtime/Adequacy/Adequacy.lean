import Runtime.ProgramLogic.LanguageInstance
import Runtime.ProtocolMachine.Model.Program
import Runtime.ProtocolMachine.Model.State
import Runtime.ProtocolMachine.Model.Violation
import Runtime.ProgramLogic.SessionWP
import IrisExtractionInstance
import Protocol.Process

/- 
The Problem. Define observable traces and adequacy statements that connect
the protocol machine execution to protocol-level correctness claims.

Solution Structure. Provide trace/event types and adequacy
statements that can be refined by later proofs.
-/

/-! # Task 22: Observable Trace Infrastructure and protocol machine Adequacy

Observable events, trace properties, and the capstone adequacy theorem
for protocol machine execution.

## Definitions

- `ObsEvent` — observable events (send, recv, open, close, fail, recover)
- `ObsTrace` — event trace
- `Violation`, `ViolationPolicy`
- `CausallyConsistent`, `FIFOConsistent`
- `session_state_interp`
- `causallyConsistent_of_fifo` — per-edge FIFO implies causality
- `no_phantom_events`

The reachability-based adequacy theorem lives in
`Runtime.Adequacy.CommTraceAdequacy`; compiler refinement lives in
`Runtime.Adequacy.CompileRefines`.

Dependencies: Task 12, Task 19, IrisExtractionInstance.
-/

set_option autoImplicit false
section

/-! ## Core Adequacy Definitions -/

universe u

variable [Telltale.TelltaleIris]

/-! ## Observational Equivalence Core -/

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

/-! ## Differential Harness Contract -/

/--
Step-indexed differential harness contract for canonical scenarios.
This is the Lean-side proposition consumed by Rust/Lean differential runners:
per-step traces must be observationally equivalent under `ObsEq`.
-/
def StepDiffHarness {ε : Type u} [EffectRuntime ε]
    (leanSteps rustSteps : List (ObsTrace ε)) : Prop :=
  leanSteps.length = rustSteps.length ∧
  ∀ (i : Nat) (leanTrace rustTrace : ObsTrace ε),
    leanSteps[i]? = some leanTrace →
    rustSteps[i]? = some rustTrace →
    ObsEq leanTrace rustTrace

/-! ## Trace Observation Utilities -/


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
  ∃ n seq, (trace)[idx]? = some (n, ObsEvent.sent e v seq)

def RecvAt {ε : Type u} [EffectRuntime ε]
    (trace : ObsTrace ε) (idx : Nat) (e : Edge) (v : Value) : Prop :=
  -- Event at idx is a receive of v on e (seqNo ignored).
  ∃ n seq, (trace)[idx]? = some (n, ObsEvent.received e v seq)

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

/-- Payloads sent on edge `e`, in trace order. -/
def sentOn {ε : Type u} [EffectRuntime ε] (e : Edge) (trace : ObsTrace ε) : List Value :=
  trace.filterMap fun p => match p.2 with
    | .sent e' v _ => if e' = e then some v else none
    | _ => none

/-- Payloads received on edge `e`, in trace order. -/
def recvOn {ε : Type u} [EffectRuntime ε] (e : Edge) (trace : ObsTrace ε) : List Value :=
  trace.filterMap fun p => match p.2 with
    | .received e' v _ => if e' = e then some v else none
    | _ => none

/-- Per-edge FIFO: at every point of the trace, the payloads received on each
edge form a prefix of the payloads sent on it. (The earlier value-pair
formulation demanded that every send be received, which fails for any trace
with in-flight messages, and was unsound for repeated payload values.) -/
def FIFOConsistent {ε : Type u} [EffectRuntime ε]
    (trace : ObsTrace ε) : Prop :=
  ∀ k e, recvOn e (trace.take k) <+: sentOn e (trace.take k)

/-! ### FIFO implies causality -/

omit [Telltale.TelltaleIris] in
/-- Taking one more element past a known index appends that element. -/
private theorem take_succ_of_getElem? {α : Type} {l : List α} {j : Nat} {x : α}
    (h : l[j]? = some x) : l.take (j + 1) = l.take j ++ [x] := by
  rw [List.take_succ, h]; rfl

omit [Telltale.TelltaleIris] in
/-- A payload sent within the first `j` entries has a send index below `j`. -/
private theorem sentAt_of_mem_sentOn {ε : Type u} [EffectRuntime ε]
    {trace : ObsTrace ε} {j : Nat} {e : Edge} {v : Value}
    (h : v ∈ sentOn e (trace.take j)) : ∃ i, i < j ∧ SentAt trace i e v := by
  obtain ⟨p, hp, hpv⟩ := List.mem_filterMap.mp h
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hp
  have hij : i < j := by simp at hi; omega
  have hlt : i < trace.length := by simp at hi; omega
  have hg : (trace)[i]? = some p := by
    rw [← hget, List.getElem_take, List.getElem?_eq_getElem hlt]
  obtain ⟨n, ev⟩ := p
  cases ev with
  | sent e' v' s =>
      by_cases he : e' = e
      · subst he
        simp at hpv
        subst hpv
        exact ⟨i, hij, n, s, hg⟩
      · simp [he] at hpv
  | _ => simp at hpv

omit [Telltale.TelltaleIris] in
/-- Per-edge FIFO consistency implies causal consistency. -/
theorem causallyConsistent_of_fifo {ε : Type u} [EffectRuntime ε]
    {trace : ObsTrace ε} (hF : FIFOConsistent trace) : CausallyConsistent trace := by
  intro j e v ⟨n, seq, hj⟩
  have hpre := hF (j + 1) e
  rw [take_succ_of_getElem? hj] at hpre
  simp only [sentOn, recvOn, List.filterMap_append, List.filterMap_cons,
    List.filterMap_nil, eq_self_iff_true, ↓reduceIte, List.append_nil] at hpre
  exact sentAt_of_mem_sentOn
    (List.IsPrefix.subset hpre (List.mem_append_right _ (List.mem_singleton_self v)))

/-! ## protocol machine Adequacy Statement -/

def session_endpoint_resources {ν : Type u} [VerificationModel ν]
    [GhostMapSlot LocalType]
    (γs : GhostName) (store : SessionStore ν) : iProp :=
  -- Concrete endpoint fragments extracted from the session store.
  sepList ((store.foldr (fun p acc => p.snd.localTypes ++ acc) []).map
    (fun epL => endpoint_frag γs epL.1 epL.2))

def coroutine_progress_resources {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    [GhostMapSlot Nat]
    (γp : GhostName) (coros : Array (CoroutineState γ ε)) : iProp :=
  -- Concrete progress-token fragments carried by coroutine runtime state.
  sepList ((coros.toList.foldr (fun c acc => c.progressTokens ++ acc) []).map
    (fun tok => progress_token_own γp tok.sid tok.endpoint 1))

def coroutine_knowledge_resources {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    [GhostMapSlot Unit]
    (γk : GhostName) (coros : Array (CoroutineState γ ε)) : iProp :=
  -- Concrete knowledge ownership per coroutine.
  sepList (coros.toList.map (fun c => knowledge_set_owns γk c.knowledgeSet))

def ghost_speculation_resources {ι γ π ε ν : Type u}
    [IdentityModel ι] [GuardLayer γ] [PersistenceModel π] [EffectRuntime ε]
    [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    [GhostMapSlot Nat]
    (γsp : SessionId → GhostName) (st : ProtocolMachineState ι γ π ε ν) : iProp :=
  -- Session-scoped speculation resources: each active ghost session owns its
  -- own authoritative speculation map under its own ghost name.
  sepList (st.ghostSessions.sessions.toList.map
    (fun p => speculation_session_inv (γsp p.snd.realSid) p.snd.realSid))

/-! ### Session-State Interpretation -/

def session_state_interp {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    [GhostMapSlot Unit] [GhostMapSlot Nat] [GhostMapSlot LocalType]
    (st : ProtocolMachineState ι γ π ε ν) : iProp :=
  -- Interpret concrete protocol machine state as WF/refinement facts plus concrete ghost resources.
  iProp.exist fun γs =>
    iProp.exist fun γp =>
      iProp.exist fun γk =>
        iProp.exist fun (γsp : SessionId → GhostName) =>
          iProp.sep (iProp.pure (WFVMState st))
            (iProp.sep (iProp.pure (sessionStore_refines_envs st.sessions))
              (iProp.sep (session_endpoint_resources γs st.sessions)
                (iProp.sep (coroutine_progress_resources γp st.coroutines)
                  (iProp.sep (coroutine_knowledge_resources γk st.coroutines)
                    (ghost_speculation_resources γsp st)))))

/-! ## No-Phantom-Events Bridge -/

def no_phantom_events {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν] : Prop :=
  -- Every observed event comes from some step event at that index.
  ∀ (st : ProtocolMachineState ι γ π ε ν) idx ev,
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
