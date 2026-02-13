import Runtime.VM.Runtime.Failure.Core

/-! # Failure Recovery Transitions

Determinism and application of recovery actions, showing the failure
handling state machine is well-defined and deterministic. -/

/-
The Problem. When failures occur, the VM must decide and apply recovery
actions. For deterministic execution, `decideRecovery` must be a function
(equal inputs give equal outputs) and action application must be defined.

Solution Structure. Prove `decideRecovery_deterministic` showing the
decision is functional. Define `applyRecoveryAction` mapping actions
to state transitions.
-/

set_option autoImplicit false

universe u

-- Recovery Decision Determinism

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

-- # Recovery action application

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

-- # Single-failure transition with deterministic evidence

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

  -- ## Corruption and timeout branches

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

-- # Batched failure ingress

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

-- # Tick-level ingress orchestration

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

-- # Failure-aware scheduler fallback tick

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

-- # Relational failure-step semantics

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
