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

/-- Retry delay is bounded by the configured max-retry envelope. -/
theorem retryBackoffDelay_bounded
    (policy : RecoveryPolicy)
    {attempt : Nat}
    (hAttempt : retryAllowed policy attempt) :
    retryBackoffDelay policy attempt ≤
      policy.baseBackoffTicks + policy.maxRetries * policy.backoffStepTicks := by
  unfold retryBackoffDelay retryAllowed at *
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hAttempt) _

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

/-- `decideRecovery` is total: every input yields a concrete recovery action. -/
theorem decideRecovery_total
    {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (sid : SessionId) (f : Failure ι)
    (evidence : RecoveryEvidence := {})
    (policy : RecoveryPolicy := defaultRecoveryPolicy) :
    ∃ act, decideRecovery st sid f evidence policy = act := by
  exact ⟨decideRecovery st sid f evidence policy, rfl⟩

/-- `decideRecovery` is deterministic: equal inputs imply equal chosen actions. -/
theorem decideRecovery_deterministic
    {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (sid : SessionId) (f : Failure ι)
    (evidence : RecoveryEvidence := {})
    (policy : RecoveryPolicy := defaultRecoveryPolicy) :
    ∀ a₁ a₂,
      decideRecovery st sid f evidence policy = a₁ →
      decideRecovery st sid f evidence policy = a₂ →
      a₁ = a₂ := by
  intro a₁ a₂ h₁ h₂
  simpa [h₁] using h₂

/-- Apply a concrete recovery action to state. -/
def applyRecoveryAction {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (act : RecoveryAction) : VMState ι γ π ε ν :=
  let st' :=
    match act with
    | .continue => st
    | .retryAfter _ => st
    | .closeSession sid => closeSession st sid
    | .quarantineEdge edge => disconnectEdges st [edge]
    | .reconcileThenRetry _ => { st with needsReconciliation := true }
  let detail :=
    match act with
    | .continue => "recovery:continue"
    | .retryAfter ticks => s!"recovery:retry ticks={ticks}"
    | .closeSession sid => s!"recovery:close sid={sid}"
    | .quarantineEdge edge => s!"recovery:quarantine sid={edge.sid}"
    | .reconcileThenRetry ticks => s!"recovery:reconcile_then_retry ticks={ticks}"
  appendFailureTraceEvent st' .recovery detail

/-- Apply one failure event, including deterministic recovery action selection. -/
def applyFailure {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (f : Failure ι) : VMState ι γ π ε ν :=
  let st0 := appendFailureTraceEvent st .failure s!"failure:{faultClassOfFailure f}"
  match f with
  | .siteCrash site =>
      let st' := crashSite st0 site
      let evidence : RecoveryEvidence :=
        { retryAttempt := 0
        , certainty := .certain
        , evidenceId := st'.nextFailureSeqNo
        , observedClock := st'.clock
        , detail := "site_crash"
        }
      let act : RecoveryAction := .retryAfter 1
      let st'' := applyRecoveryAction st' act
      emitStructuredErrorEvent st'' (faultClassOfFailure f) evidence.certainty act evidence.evidenceId evidence.detail
  | .partition edges =>
      let st' := disconnectEdges st0 edges
      let evidence : RecoveryEvidence :=
        { retryAttempt := 0
        , certainty := .certain
        , evidenceId := st'.nextFailureSeqNo
        , observedClock := st'.clock
        , detail := s!"partition edges={edges.length}"
        }
      let act : RecoveryAction := .retryAfter 1
      let st'' := applyRecoveryAction st' act
      emitStructuredErrorEvent st'' (faultClassOfFailure f) evidence.certainty act evidence.evidenceId evidence.detail
  | .heal edges =>
      let st' := reconnectEdges st0 edges
      let evidence : RecoveryEvidence :=
        { retryAttempt := 0
        , certainty := .certain
        , evidenceId := st'.nextFailureSeqNo
        , observedClock := st'.clock
        , detail := s!"heal edges={edges.length}"
        }
      let act : RecoveryAction := .continue
      let st'' := applyRecoveryAction st' act
      emitStructuredErrorEvent st'' (faultClassOfFailure f) evidence.certainty act evidence.evidenceId evidence.detail
  | .corrupt edge _seqNo =>
      let st' := reconcileBeforeReplay st0 edge.sid
      let evidence : RecoveryEvidence :=
        { retryAttempt := 0
        , certainty := .unknown
        , evidenceId := st'.nextFailureSeqNo
        , observedClock := st'.clock
        , detail := s!"corrupt sid={edge.sid} seq={_seqNo}"
        }
      let act := decideRecovery st' edge.sid f evidence
      let st'' := applyRecoveryAction st' act
      emitStructuredErrorEvent st'' (faultClassOfFailure f) evidence.certainty act evidence.evidenceId evidence.detail
  | .timeout edge _deadline =>
      let st' := reconcileBeforeReplay st0 edge.sid
      let retryAttempt :=
        if st'.clock >= _deadline then st'.clock - _deadline else 0
      let certainty : CommitCertainty :=
        if st'.clock >= _deadline then .unknown else .boundedDiff
      let evidence : RecoveryEvidence :=
        { retryAttempt := retryAttempt
        , certainty := certainty
        , evidenceId := st'.nextFailureSeqNo
        , observedClock := st'.clock
        , detail := s!"timeout sid={edge.sid} deadline={_deadline}"
        }
      let act := decideRecovery st' edge.sid f evidence
      let st'' := applyRecoveryAction st' act
      emitStructuredErrorEvent st'' (faultClassOfFailure f) evidence.certainty act evidence.evidenceId evidence.detail

/-- Apply a failure-event batch in deterministic arrival order. -/
def applyFailureEvents {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (events : List (Failure ι)) :
    VMState ι γ π ε ν :=
  events.foldl applyFailure st

/-- Deterministic ingress for one runtime tick.
    Topology/environment events are applied first, then failure events, then scheduling. -/
def ingressTick {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν)
    (envEvents : List (EnvironmentEvent (ι := ι)))
    (failureEvents : List (Failure ι)) : VMState ι γ π ε ν :=
  let st' := applyEnvironmentEvents st envEvents
  let st'' := applyFailureEvents st' failureEvents
  match schedStep st'' with
  | some st''' => st'''
  | none => st''

/-- Execute one failure-aware tick: consume at most one failure event, otherwise schedule. -/
def failureTick {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (event? : Option (Failure ι)) : VMState ι γ π ε ν :=
  match event? with
  | some f => applyFailure st f
  | none =>
      match schedStep st with
      | some st' => st'
      | none => st

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
