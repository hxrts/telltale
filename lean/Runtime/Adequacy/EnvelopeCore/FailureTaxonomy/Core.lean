import Runtime.Adequacy.EnvelopeCore.AdmissionLogic
import Runtime.ProtocolMachine.Model.SemanticObjects.ProgressContracts
import Runtime.Adequacy.EnvelopeCore.FailureTaxonomy.CoreCodes

/-! # Failure Taxonomy and Recovery

Classification of protocol machine failures, commit certainty levels, and structured
recovery actions for deterministic fault handling. -/

set_option autoImplicit false
namespace Runtime
namespace Adequacy
universe u v

/-! ## Progress-Failure Taxonomy -/

/-- Explicit mapping from progress-contract terminal/degradation states into the
shared failure taxonomy. Non-failure progress states do not admit a failure
classification. -/
def failureClassOfProgressState : Runtime.ProtocolMachine.Model.ProgressState → Option FailureClass
  | .pending => none
  | .blocked => none
  | .noProgress => some .noProgressToken
  | .degraded => some .transportTimeout
  | .succeeded => none
  | .failed => some .invokeFault
  | .cancelled => some .closeFault
  | .timedOut => some .transportTimeout
  | .handedOff => none

/-- Machine-stable error code projection for progress-failure states. -/
def errorCodeOfProgressState : Runtime.ProtocolMachine.Model.ProgressState → Option ErrorCode :=
  Option.map errorCodeOfFailureClass ∘ failureClassOfProgressState

/-- Structured failure-taxonomy evidence carried by one progress contract once
it reaches a classified failure state. -/
structure ProgressFailureEvidence where
  operationId : String
  session : Option Nat
  failureClass : FailureClass
  errorCode : ErrorCode
  reason : Option String
  deriving Repr, DecidableEq, Inhabited

namespace _root_.Runtime.ProtocolMachine.Model

/-- Build explicit failure-taxonomy evidence for one progress contract when its
state is classified as a failure-visible progress outcome. -/
def _root_.Runtime.ProtocolMachine.Model.ProgressContract.failureEvidence? :
    _root_.Runtime.ProtocolMachine.Model.ProgressContract →
      Option Runtime.Adequacy.ProgressFailureEvidence
  | contract =>
      match Runtime.Adequacy.failureClassOfProgressState contract.state,
          Runtime.Adequacy.errorCodeOfProgressState contract.state with
      | some failureClass, some errorCode =>
          some
            { operationId := contract.operationId
            , session := contract.session
            , failureClass := failureClass
            , errorCode := errorCode
            , reason := contract.reason
            }
      | _, _ => none

end _root_.Runtime.ProtocolMachine.Model

/-! ## Failure-Visible Snapshots -/

/-- Failure-visible snapshot used for cross-target conformance theorems. -/
structure FailureVisibleSnapshot where
  errorCodes : List ErrorCode
  faultClasses : List String
  certainties : List ErrorCertainty
  actions : List ErrorActionTag
  terminalOutcome : Bool
  safetyVerdict : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Build failure-visible snapshots from executable protocol machine states. -/
def vmFailureVisibleSnapshot
    {ι γ π ε ν : Type u}
    [ProtocolMachineDomain ι γ π ε ν]
    (st : ProtocolMachineState ι γ π ε ν) : FailureVisibleSnapshot :=
  let terminalOutcome :=
    st.coroutines.toList.all (fun c =>
      match c.status with
      | .done => true
      | .faulted _ => true
      | _ => false)
  let safetyVerdict :=
    !(st.structuredErrorEvents.any (fun ev => ev.action = .abort))
  { errorCodes := st.structuredErrorEvents.map (fun ev => errorCodeOfFaultClassTag ev.faultClass)
  , faultClasses := st.structuredErrorEvents.map (fun ev => ev.faultClass)
  , certainties := st.structuredErrorEvents.map (fun ev => ev.certainty)
  , actions := st.structuredErrorEvents.map (fun ev => ev.action)
  , terminalOutcome := terminalOutcome
  , safetyVerdict := safetyVerdict
  }

/-! ## Failure-Visible Equivalence Forms -/

/-- Failure-visible projection used by cross-target conformance theorems. -/
abbrev FailureVisibleProjection (State : Type u) := State → FailureVisibleSnapshot

/-- Failure-visible state equivalence. -/
def EqFailVisible {State : Type u}
    (project : FailureVisibleProjection State)
    (s₁ s₂ : State) : Prop :=
  project s₁ = project s₂

/-- Failure-visible run equivalence. -/
def EqFailVisibleRun {State : Type u}
    (project : FailureVisibleProjection State)
    (r₁ r₂ : Run State) : Prop :=
  ∀ t, EqFailVisible project (r₁ t) (r₂ t)

/-- Cross-target failure-envelope conformance theorem form (single/multi/sharded). -/
def CrossTargetFailureConformance {State : Type u}
    (project : FailureVisibleProjection State)
    (SingleRun MultiRun ShardedRun : Run State → Prop) : Prop :=
  ∀ single multi sharded,
    SingleRun single → MultiRun multi → ShardedRun sharded →
      EqFailVisibleRun project single multi ∧
      EqFailVisibleRun project single sharded ∧
      EqFailVisibleRun project multi sharded

/-! ## Recovery Safety Forms -/

/-- Abstract state transformer used by recovery/action theorems. -/
abbrev RecoveryStep (State : Type u) := State → RecoveryAction → State

/-- Abstract safety theorem form for deterministic recovery actions. -/
def RecoveryActionSafety {State : Type u}
    (Safe : State → Prop)
    (step : RecoveryStep State) : Prop :=
  ∀ st act, Safe st → Safe (step st act)

/-- Preconditions used by no-harmful-replay theorem forms. -/
structure ReplayPreconditions (State : Type u) where
  nonceFresh : State → Nat → Prop
  reconciled : State → Prop

/-- Abstract no-harmful-replay theorem form under nonce/reconciliation preconditions. -/
def NoUnsafeReplay {State : Type u}
    (Safe : State → Prop)
    (pre : ReplayPreconditions State)
    (replay : State → Nat → State) : Prop :=
  ∀ st nonce,
    pre.nonceFresh st nonce →
    pre.reconciled st →
    Safe (replay st nonce)

/-! ## Restart and Structured-Error Forms -/

/-- Checkpoint-restart refinement theorem form. -/
def CheckpointRestartRefinement {State : Type u}
    (Refines : State → State → Prop)
    (checkpoint restart : State → State) : Prop :=
  ∀ st, Refines (restart (checkpoint st)) st

/-- Structured error projection used by restart/error-adequacy theorems. -/
abbrev StructuredErrorProjection (State : Type u) := State → List StructuredErrorEvent

/-- Structured error adequacy after restart/checkpoint replay. -/
def StructuredErrorAdequacyAfterRestart {State : Type u}
    (structuredErrors : StructuredErrorProjection State)
    (checkpoint restart : State → State) : Prop :=
  ∀ st, structuredErrors (restart (checkpoint st)) = structuredErrors st

/-- Combined theorem form: restart refinement plus structured error adequacy. -/
def RestartRefinementStructuredErrorAdequacy {State : Type u}
    (Refines : State → State → Prop)
    (checkpoint restart : State → State)
    (structuredErrors : StructuredErrorProjection State) : Prop :=
  CheckpointRestartRefinement Refines checkpoint restart ∧
  StructuredErrorAdequacyAfterRestart structuredErrors checkpoint restart

/-- Identity restart/checkpoint trivially satisfies restart+structured-error adequacy. -/
theorem restart_structured_error_adequacy_identity
    {State : Type u}
    (structuredErrors : StructuredErrorProjection State) :
    RestartRefinementStructuredErrorAdequacy
      (fun s₁ s₂ => s₁ = s₂)
      (fun s => s)
      (fun s => s)
      structuredErrors := by
  refine ⟨?_, ?_⟩
  · intro st
    rfl
  · intro st
    rfl

/-! ## Failure Envelope Extensions -/

/-- Failure-envelope soundness extension over local envelopes. -/
def FailureEnvelopeSoundnessExtension {State : Type u} {Obs : Type v}
    (E : LocalEnvelope State Obs)
    (RefRun ImplRun : Run State → Prop)
    (injectFailure : Run State → Run State) : Prop :=
  ∀ ref impl,
    RefRun ref → ImplRun impl →
    EqEnvLocal E (injectFailure ref) (injectFailure impl)

/-- Failure-envelope maximality extension over local envelopes. -/
def FailureEnvelopeMaximalityExtension {State : Type u} {Obs : Type v}
    (E : LocalEnvelope State Obs)
    (RefRun ImplRun : Run State → Prop)
    (injectFailure : Run State → Run State) : Prop :=
  ∀ R : Run State → Run State → Prop,
    (∀ ref impl,
      RefRun ref → ImplRun impl →
      R ref impl →
      EqEnvLocal E (injectFailure ref) (injectFailure impl)) →
    ∀ ref impl,
      RefRun ref → ImplRun impl →
      R ref impl →
      EqEnvLocal E (injectFailure ref) (injectFailure impl)

/-! ## Failure-Envelope Premise Bundles -/

/-- Premise bundle for abstract Phase-E8 failure/recovery theorem extraction. -/
structure FailureEnvelopePremises (State : Type u) (Obs : Type v) where
  localEnvelope : LocalEnvelope State Obs
  Safe : State → Prop
  recoveryStep : RecoveryStep State
  failureVisible : FailureVisibleProjection State
  singleThreadRun : Run State → Prop
  multiThreadRun : Run State → Prop
  shardedRun : Run State → Prop
  replayPre : ReplayPreconditions State
  replay : State → Nat → State
  Refines : State → State → Prop
  checkpoint : State → State
  restart : State → State
  structuredErrors : StructuredErrorProjection State
  RefRun : Run State → Prop
  ImplRun : Run State → Prop
  injectFailure : Run State → Run State
  crossTargetConformanceWitness :
    CrossTargetFailureConformance
      failureVisible singleThreadRun multiThreadRun shardedRun
  /-- Assumed input: `Safe` and `recoveryStep` are arbitrary, so recovery-action
  safety is not derivable here and must be discharged by the instantiation. -/
  assumedRecoveryActionSafety :
    RecoveryActionSafety Safe recoveryStep
  noUnsafeReplayWitness :
    NoUnsafeReplay Safe replayPre replay
  checkpointRestartRefinementWitness :
    CheckpointRestartRefinement Refines checkpoint restart
  restartStructuredErrorAdequacyWitness :
    RestartRefinementStructuredErrorAdequacy
      Refines checkpoint restart structuredErrors
  failureEnvelopeSoundnessWitness :
    FailureEnvelopeSoundnessExtension localEnvelope RefRun ImplRun injectFailure
  failureEnvelopeMaximalityWitness :
    FailureEnvelopeMaximalityExtension localEnvelope RefRun ImplRun injectFailure


end Adequacy
end Runtime
