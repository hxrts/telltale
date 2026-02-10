import Runtime.VM.Model.State
import Runtime.VM.Runtime.Scheduler
import IrisExtractionInstance

/-
The Problem. The VM needs a failure model that is parametric over the
identity model and integrates crashes, partitions, and recovery without
committing to a concrete recovery algorithm.

Solution Structure. Define failure modes, a failure-aware step relation,
and recovery predicates as lightweight stubs aligned with runtime.md §9.
-/

/-! # Task 24: Failure Model and Recovery

Failure-aware step relation and recovery predicates
from runtime.md §9.

## Definitions

- `Failure` — site crash, partition, heal, corrupt, timeout
- `ParticipantLost`, `ParticipantSurvives`
- `FStep` — failure-aware step relation
- `Recoverable`, `crash_nonparticipant_preserves`
- `participant_failover`, `crash_close_safe`

Dependencies: Task 23, Scheduler. -/

set_option autoImplicit false

universe u

/-! ## Failure modes -/

inductive Failure (ι : Type u) [IdentityModel ι] where
  -- Failure events that perturb transport or sites.
  | siteCrash (site : IdentityModel.SiteId ι)
  | partition (edges : List Edge)
  | heal (edges : List Edge)
  | corrupt (edge : Edge) (seqNo : Nat)
  | timeout (edge : Edge) (deadline : Nat)

def ParticipantLost {ι : Type u} [IdentityModel ι]
    (crashed : List (IdentityModel.SiteId ι))
    (p : IdentityModel.ParticipantId ι) : Prop :=
  -- A participant is lost if all of its sites crashed.
  ∀ s ∈ IdentityModel.sites p, s ∈ crashed

def ParticipantSurvives {ι : Type u} [IdentityModel ι]
    (crashed : List (IdentityModel.SiteId ι))
    (p : IdentityModel.ParticipantId ι) : Prop :=
  -- A participant survives if at least one site remains.
  ∃ s ∈ IdentityModel.sites p, s ∉ crashed

/-! ## Failure-aware step relation -/

def crashSite {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (_site : IdentityModel.SiteId ι) : VMState ι γ π ε ν :=
  -- Mark site as crashed (idempotent list update).
  by
    classical
    let _ : DecidableEq (IdentityModel.SiteId ι) := IdentityModel.decEqS (ι:=ι)
    exact if _site ∈ st.crashedSites then st
    else { st with crashedSites := _site :: st.crashedSites }

def disconnectEdges {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (_edges : List Edge) : VMState ι γ π ε ν :=
  -- Mark edges as partitioned.
  let added := _edges.filter (fun e => decide (e ∉ st.partitionedEdges))
  { st with partitionedEdges := added ++ st.partitionedEdges }

def reconnectEdges {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (_edges : List Edge) : VMState ι γ π ε ν :=
  -- Remove edges from the partitioned set.
  let remaining := st.partitionedEdges.filter (fun e => decide (e ∉ _edges))
  { st with partitionedEdges := remaining }

/-- Topology-only changes used by runtime scheduling/failure models. -/
inductive TopologyChange {ι : Type u} [IdentityModel ι] where
  | crash (site : IdentityModel.SiteId ι)
  | partition (edges : List Edge)
  | heal (edges : List Edge)

/-- Environment-sourced runtime event stream.
Topology perturbations are modeled as external environment ingress. -/
inductive EnvironmentEvent {ι : Type u} [IdentityModel ι] where
  | topology (tc : TopologyChange (ι := ι))

/-- Apply a topology change without executing protocol instructions. -/
def applyTopologyChange {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (tc : TopologyChange (ι := ι)) :
    VMState ι γ π ε ν :=
  match tc with
  | .crash site => crashSite st site
  | .partition edges => disconnectEdges st edges
  | .heal edges => reconnectEdges st edges

/-- Apply one environment event to VM state.
Topology perturbations only enter through this ingress function. -/
def applyEnvironmentEvent {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (ev : EnvironmentEvent (ι := ι)) :
    VMState ι γ π ε ν :=
  match ev with
  | .topology tc => applyTopologyChange st tc

/-- Apply an environment-event batch in arrival order. -/
def applyEnvironmentEvents {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (events : List (EnvironmentEvent (ι := ι))) :
    VMState ι γ π ε ν :=
  events.foldl applyEnvironmentEvent st

def closeSession {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (_sid : SessionId) : VMState ι γ π ε ν :=
  -- Close the matching session and clear its buffers/traces.
  let rec closeStore (ss : SessionStore ν) : SessionStore ν :=
    match ss with
    | [] => []
    | (sid, s) :: rest =>
        if sid = _sid then
          (sid, { s with phase := .closed, buffers := [], traces := (∅ : DEnv) }) :: rest
        else
          (sid, s) :: closeStore rest
  { st with sessions := closeStore st.sessions }

inductive FStep {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν] :
    VMState ι γ π ε ν → VMState ι γ π ε ν → Prop where
  -- Failure-aware step relation for the VM.
  | normal (st st' : VMState ι γ π ε ν)
      (h : schedStep st = some st') : FStep st st'
  | siteCrash (st : VMState ι γ π ε ν) (site : IdentityModel.SiteId ι) :
      FStep st (crashSite st site)
  | partition (st : VMState ι γ π ε ν) (edges : List Edge) :
      FStep st (disconnectEdges st edges)
  | heal (st : VMState ι γ π ε ν) (edges : List Edge) :
      FStep st (reconnectEdges st edges)
  | closeOnCrash (st : VMState ι γ π ε ν) (sid : SessionId) :
      -- Surviving participants can close sessions after a crash.
      FStep st (closeSession st sid)

/-! ## Recovery predicates -/

def FailureSessionCoherent {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st : VMState ι γ π ε ν) (_sid : SessionId) : Prop :=
  -- Session is coherent if it exists and is not closed.
  ∃ stSess, (_sid, stSess) ∈ _st.sessions ∧ stSess.phase ≠ .closed

def FStarDrain {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st _st' : VMState ι γ π ε ν) : Prop :=
  -- Configuration and programs are preserved across drain.
  _st'.config = _st.config ∧
  _st'.programs = _st.programs ∧
  -- No normal scheduling step is possible (quiescent).
  schedStep _st' = none ∧
  -- All closed sessions have empty buffers and traces.
  (∀ sid (stSess : SessionState ν), (sid, stSess) ∈ _st'.sessions →
    stSess.phase = .closed → stSess.buffers = [] ∧ stSess.traces = (∅ : DEnv))

def Recoverable {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (sid : SessionId)
    (_crashed : List (IdentityModel.SiteId ι)) : Prop :=
  -- Recovery requires a drained state with coherent session.
  ∃ st', FStarDrain st st' ∧ FailureSessionCoherent st' sid

def SiteParticipates {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st : VMState ι γ π ε ν) (_site : IdentityModel.SiteId ι)
    (_sid : SessionId) : Prop :=
  -- Site participates if the session is live and the site isn't crashed.
  FailureSessionCoherent _st _sid ∧ _site ∉ _st.crashedSites

def Participates {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st : VMState ι γ π ε ν) (_p : IdentityModel.ParticipantId ι)
    (_sid : SessionId) : Prop :=
  -- Participant participates if any of its sites participates.
  ∃ s ∈ IdentityModel.sites _p, SiteParticipates _st s _sid

def CanResume {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st : VMState ι γ π ε ν) (_p : IdentityModel.ParticipantId ι)
    (_sid : SessionId) : Prop :=
  -- A surviving participant can resume if it still participates.
  ParticipantSurvives _st.crashedSites _p ∧ Participates _st _p _sid

def crash_nonparticipant_preserves {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st : VMState ι γ π ε ν) (_site : IdentityModel.SiteId ι)
    (_sid : SessionId) : Prop :=
  -- If the site is not involved, coherence is preserved after crash.
  ¬ SiteParticipates _st _site _sid →
    FailureSessionCoherent _st _sid →
    FailureSessionCoherent (crashSite _st _site) _sid

def participant_failover {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st : VMState ι γ π ε ν) (_p : IdentityModel.ParticipantId ι)
    (_site : IdentityModel.SiteId ι) : Prop :=
  -- Participant can fail over if it survives and has an alternate site.
  ParticipantSurvives _st.crashedSites _p ∧ _site ∈ IdentityModel.sites _p

def crash_close_safe {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st : VMState ι γ π ε ν) (_sid : SessionId)
    (_survivor : IdentityModel.ParticipantId ι)
    (_crashed : List (IdentityModel.SiteId ι)) : Prop :=
  -- Closing after crash preserves coherence for surviving participant.
  ParticipantSurvives _crashed _survivor →
    FailureSessionCoherent _st _sid →
    FailureSessionCoherent (closeSession _st _sid) _sid
