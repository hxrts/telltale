import Runtime.VM.Model.State
import Runtime.VM.Runtime.Scheduler
import IrisExtractionInstance

/-
The Problem. The VM needs a failure model that is parametric over the
identity model and integrates crashes, partitions, and recovery without
committing to a concrete recovery algorithm.

Solution Structure. Define failure modes, a failure-aware step relation,
and deterministic recovery actions aligned with runtime.md §9.
-/

/-! # Task 24: Failure Model and Recovery

Failure-aware step relation and recovery predicates
from runtime.md §9.

## Definitions

- `Failure` — site crash, partition, heal, corrupt, timeout
- `ParticipantLost`, `ParticipantSurvives`
- `FStep` — failure-aware step relation
- Recovery transition primitives used by loader/scheduler integration

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

/-- Canonical runtime status of a failure event for ingress/recovery handling. -/
inductive FailureStatus where
  | topologyMutation
  | transportCorruption
  | transportTimeout
  deriving Repr, DecidableEq

/-- Canonical status classifier used by the executable Lean failure semantics. -/
def failureStatus {ι : Type u} [IdentityModel ι] : Failure ι → FailureStatus
  | .siteCrash _ => .topologyMutation
  | .partition _ => .topologyMutation
  | .heal _ => .topologyMutation
  | .corrupt _ _ => .transportCorruption
  | .timeout _ _ => .transportTimeout

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

/-! ### Topology mutation primitives -/

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

/-! ### Environment ingress events -/

/-- Topology-only changes used by runtime scheduling/failure models. -/
inductive TopologyChange {ι : Type u} [IdentityModel ι] where
  | crash (site : IdentityModel.SiteId ι)
  | partition (edges : List Edge)
  | heal (edges : List Edge)

/-- Environment-sourced runtime event stream.
Topology perturbations are modeled as external environment ingress. -/
inductive EnvironmentEvent {ι : Type u} [IdentityModel ι] where
  | topology (tc : TopologyChange (ι := ι))

/-! #### Topology-change application -/

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
  let st' :=
    match ev with
    | .topology tc => applyTopologyChange st tc
  match ev with
  | .topology tc =>
      let detail :=
        match tc with
        | .crash _ => "topology:crash"
        | .partition edges => s!"topology:partition edges={edges.length}"
        | .heal edges => s!"topology:heal edges={edges.length}"
    let traceEv : FailureTraceEvent :=
      { tick := st'.clock
      , seqNo := st'.nextFailureSeqNo
      , tag := .topology
      , detail := detail
      }
    { st' with
        failureTrace := st'.failureTrace ++ [traceEv]
      , nextFailureSeqNo := st'.nextFailureSeqNo + 1
    }

/-! #### Batched environment ingress -/

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

/-! ### Session closure/coherence helpers -/

/-- Lookup a session state by id. -/
def sessionState? {ν : Type u} [VerificationModel ν]
    (sessions : SessionStore ν) (sid : SessionId) : Option (SessionState ν) :=
  sessions.find? (fun p => decide (p.fst = sid)) |>.map Prod.snd

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

/-- Session coherence as an executable predicate. -/
def failureSessionCoherentB {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (sid : SessionId) : Bool :=
  match sessionState? st.sessions sid with
  | none => false
  | some sess =>
      match sess.phase with
      | .closed => false
      | _ => true

/-! ### Recovery policy vocabulary -/

/-- Recovery actions used by the executable failure semantics. -/
inductive RecoveryAction where
  | continue
  | retryAfter (ticks : Nat)
  | closeSession (sid : SessionId)
  | quarantineEdge (edge : Edge)
  | reconcileThenRetry (ticks : Nat)
  deriving Repr, DecidableEq

/-- Determinism profile for runtime recovery control. -/
inductive RecoveryDeterminismMode where
  | strict
  | boundedDiff (maxDiff : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Proof-visible policy parameters for deterministic recovery selection. -/
structure RecoveryPolicy where
  mode : RecoveryDeterminismMode := .strict
  maxRetries : Nat := 0
  baseBackoffTicks : Nat := 1
  backoffStepTicks : Nat := 1
  deriving Repr, DecidableEq, Inhabited

/-- Canonical runtime recovery policy (strict deterministic behavior). -/
def defaultRecoveryPolicy : RecoveryPolicy := {}

/-- Deterministic retry delay induced by bounded backoff policy parameters. -/
def retryBackoffDelay (policy : RecoveryPolicy) (attempt : Nat) : Nat :=
  policy.baseBackoffTicks + attempt * policy.backoffStepTicks

/-- Retry budget predicate (proof-visible bounded retry semantics). -/
def retryAllowed (policy : RecoveryPolicy) (attempt : Nat) : Prop :=
  attempt ≤ policy.maxRetries

/-! ### Structured failure evidence and event mapping -/

/-- Alias used by failure recovery to express commit certainty on ingress evidence. -/
abbrev CommitCertainty := ErrorCertainty

/-- Evidence supplied to deterministic recovery policy decisions. -/
structure RecoveryEvidence where
  retryAttempt : Nat := 0
  certainty : CommitCertainty := .unknown
  evidenceId : Nat := 0
  observedClock : Nat := 0
  detail : String := ""
  deriving Repr, DecidableEq, Inhabited

/-- Structured error action tag corresponding to runtime recovery actions. -/
def errorActionTagOfRecoveryAction : RecoveryAction → ErrorActionTag
  | .continue => .continue
  | .retryAfter _ => .retryAfter
  | .closeSession _ => .closeSession
  | .quarantineEdge _ => .quarantineEdge
  | .reconcileThenRetry _ => .reconcileThenRetry

/-- Coarse fault-class label for deterministic structured error reporting. -/
def faultClassOfFailure {ι : Type u} [IdentityModel ι] : Failure ι → String
  | .siteCrash _ => "topology_mutation"
  | .partition _ => "topology_mutation"
  | .heal _ => "topology_mutation"
  | .corrupt _ _ => "transport_corruption"
  | .timeout _ _ => "transport_timeout"

/-! #### Deterministic trace/error event emission -/

/-- Append one deterministic trace event in ingress order. -/
def appendFailureTraceEvent {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν)
    (tag : FailureTraceTag) (detail : String) : VMState ι γ π ε ν :=
  let ev : FailureTraceEvent :=
    { tick := st.clock
    , seqNo := st.nextFailureSeqNo
    , tag := tag
    , detail := detail
    }
  { st with
      failureTrace := st.failureTrace ++ [ev]
    , nextFailureSeqNo := st.nextFailureSeqNo + 1
  }

/-- Emit one structured error event in deterministic ingress order. -/
def emitStructuredErrorEvent {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν)
    (faultClass : String)
    (certainty : CommitCertainty)
    (action : RecoveryAction)
    (evidenceId : Nat)
    (detail : String) : VMState ι γ π ε ν :=
  let ev : StructuredErrorEvent :=
    { tick := st.clock
    , seqNo := st.nextFailureSeqNo
    , faultClass := faultClass
    , certainty := certainty
    , action := errorActionTagOfRecoveryAction action
    , evidenceId := evidenceId
    , detail := detail
    }
  { st with
      structuredErrorEvents := st.structuredErrorEvents ++ [ev]
    , nextFailureSeqNo := st.nextFailureSeqNo + 1
  }

/-! ### Reconciliation pre-stage -/

/-- Reconciliation stage used before replay when certainty is unknown. -/
def reconcileBeforeReplay {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (sid : SessionId) : VMState ι γ π ε ν :=
  if st.needsReconciliation then
    let st' := { st with needsReconciliation := false }
    appendFailureTraceEvent st' .reconciliation s!"reconcile_before_replay sid={sid}"
  else
    st

/-! ### Deterministic recovery decision procedures -/

/-- Deterministic policy dispatcher for timeout handling under strict/bounded modes. -/
def decideTimeoutRecovery
    (policy : RecoveryPolicy)
    (stClock : Nat)
    (sid : SessionId)
    (deadline : Nat)
    (evidence : RecoveryEvidence := {}) : RecoveryAction :=
  match policy.mode with
  | .strict =>
      if stClock >= deadline then .closeSession sid else .retryAfter (deadline - stClock)
  | .boundedDiff _ =>
      if evidence.certainty = .unknown then
        .reconcileThenRetry (retryBackoffDelay policy evidence.retryAttempt)
      else if evidence.retryAttempt ≤ policy.maxRetries then
        .retryAfter (retryBackoffDelay policy evidence.retryAttempt)
      else
        .closeSession sid

/-! #### Session-scoped recovery decision -/

/-- Deterministic recovery choice for a failure affecting a session. -/
def decideRecovery {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (sid : SessionId) (f : Failure ι)
    (evidence : RecoveryEvidence := {})
    (policy : RecoveryPolicy := defaultRecoveryPolicy) : RecoveryAction :=
  if h : failureSessionCoherentB st sid then
    match policy.mode with
    | .strict =>
        match f with
        | .siteCrash _ => .retryAfter 1
        | .partition _ => .retryAfter 1
        | .heal _ => .continue
        | .corrupt edge _ => .quarantineEdge edge
        | .timeout edge deadline =>
            decideTimeoutRecovery policy st.clock edge.sid deadline evidence
    | .boundedDiff _ =>
        match f with
        | .siteCrash _ =>
            if evidence.certainty = .unknown then
              .reconcileThenRetry (retryBackoffDelay policy evidence.retryAttempt)
            else if evidence.retryAttempt ≤ policy.maxRetries then
              .retryAfter (retryBackoffDelay policy evidence.retryAttempt)
            else
              .closeSession sid
        | .partition _ =>
            if evidence.certainty = .unknown then
              .reconcileThenRetry (retryBackoffDelay policy evidence.retryAttempt)
            else if evidence.retryAttempt ≤ policy.maxRetries then
              .retryAfter (retryBackoffDelay policy evidence.retryAttempt)
            else
              .closeSession sid
        | .heal _ => .continue
        | .corrupt edge _ => .quarantineEdge edge
        | .timeout edge deadline =>
            decideTimeoutRecovery policy st.clock edge.sid deadline evidence
  else
    .closeSession sid

/-! Proof-only recovery lemmas are in `Runtime.Proofs.VM.Failure`. -/
