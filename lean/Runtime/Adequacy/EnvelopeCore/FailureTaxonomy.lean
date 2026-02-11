import Runtime.Adequacy.EnvelopeCore.AdmissionLogic

/-! # Failure Taxonomy and Recovery

Classification of VM failures, commit certainty levels, and structured
recovery actions for deterministic fault handling. -/

/-
The Problem. The VM can fail in many ways (type violations, channel
closure, transport errors, etc.). For deterministic recovery, we need
to classify failures by their certainty level (how much state may be
uncommitted) and map them to recovery actions.

Solution Structure. Define `FailureClass` enumeration covering all
failure modes. Define `CommitCertainty` levels and `RecoveryAction`
vocabulary. Provide failure-to-recovery mappings for structured
error handling.
-/

set_option autoImplicit false

namespace Runtime
namespace Adequacy

universe u v

/-! ## Failure Classification -/

inductive FailureClass where
  | typeViolation
  | unknownLabel
  | channelClosed
  | signatureInvalid
  | verificationFailed
  | guardFault
  | invokeFault
  | transferFault
  | closeFault
  | specFault
  | flowViolation
  | noProgressToken
  | outputConditionFault
  | outOfRegisters
  | pcOutOfBounds
  | bufferFull
  | outOfCredits
  | topologyMutation
  | transportCorruption
  | transportTimeout
  | unknown
  deriving Repr, DecidableEq, Inhabited

/-- Commit certainty abstraction used by failure/recovery reasoning. -/
inductive CommitCertainty where
  | certain
  | boundedDiff
  | unknown
  deriving Repr, DecidableEq, Inhabited

/-- Abstract recovery action vocabulary (policy-level). -/
inductive RecoveryAction where
  | continue
  | retryAfter (ticks : Nat)
  | closeSession (sid : Nat)
  | quarantineEdge
  | abort
  deriving Repr, DecidableEq, Inhabited

/-- Machine-stable error code schema shared by Lean model and Rust runtime. -/
inductive ErrorCode where
  | typeViolation
  | unknownLabel
  | channelClosed
  | invalidSignature
  | verificationFailed
  | acquireFault
  | invokeFault
  | transferFault
  | closeFault
  | specFault
  | flowViolation
  | noProgressToken
  | outputConditionFault
  | outOfRegisters
  | pcOutOfBounds
  | bufferFull
  | outOfCredits
  | topologyMutation
  | transportCorruption
  | transportTimeout
  | unknown
  deriving Repr, DecidableEq, Inhabited

/-- Stable wire/string representation for cross-target artifacts. -/
def errorCodeString : ErrorCode → String
  | .typeViolation => "type_violation"
  | .unknownLabel => "unknown_label"
  | .channelClosed => "channel_closed"
  | .invalidSignature => "invalid_signature"
  | .verificationFailed => "verification_failed"
  | .acquireFault => "acquire_fault"
  | .invokeFault => "invoke_fault"
  | .transferFault => "transfer_fault"
  | .closeFault => "close_fault"
  | .specFault => "spec_fault"
  | .flowViolation => "flow_violation"
  | .noProgressToken => "no_progress_token"
  | .outputConditionFault => "output_condition_fault"
  | .outOfRegisters => "out_of_registers"
  | .pcOutOfBounds => "pc_out_of_bounds"
  | .bufferFull => "buffer_full"
  | .outOfCredits => "out_of_credits"
  | .topologyMutation => "topology_mutation"
  | .transportCorruption => "transport_corruption"
  | .transportTimeout => "transport_timeout"
  | .unknown => "unknown_fault"

/-- Structured evidence record for deterministic recovery decisions. -/
structure RecoveryEvidence where
  code : ErrorCode
  failureClass : FailureClass
  certainty : CommitCertainty
  detail : String
  tick : Nat
  source : String
  deriving Repr, DecidableEq, Inhabited

/-- Map abstract failure classes to machine-stable error codes. -/
def errorCodeOfFailureClass : FailureClass → ErrorCode
  | .typeViolation => .typeViolation
  | .unknownLabel => .unknownLabel
  | .channelClosed => .channelClosed
  | .signatureInvalid => .invalidSignature
  | .verificationFailed => .verificationFailed
  | .guardFault => .acquireFault
  | .invokeFault => .invokeFault
  | .transferFault => .transferFault
  | .closeFault => .closeFault
  | .specFault => .specFault
  | .flowViolation => .flowViolation
  | .noProgressToken => .noProgressToken
  | .outputConditionFault => .outputConditionFault
  | .outOfRegisters => .outOfRegisters
  | .pcOutOfBounds => .pcOutOfBounds
  | .bufferFull => .bufferFull
  | .outOfCredits => .outOfCredits
  | .topologyMutation => .topologyMutation
  | .transportCorruption => .transportCorruption
  | .transportTimeout => .transportTimeout
  | .unknown => .unknown

/-- Total mapping from Lean VM instruction faults to abstract failure classes. -/
def failureClassOfLeanFault {γ : Type u} : _root_.Fault γ → FailureClass
  | .typeViolation _ _ => .typeViolation
  | .unknownLabel _ => .unknownLabel
  | .channelClosed _ => .channelClosed
  | .invalidSignature _ => .signatureInvalid
  | .acquireFault _ _ => .guardFault
  | .invokeFault _ => .invokeFault
  | .transferFault _ => .transferFault
  | .closeFault _ => .closeFault
  | .specFault _ => .specFault
  | .flowViolation _ => .flowViolation
  | .noProgressToken _ => .noProgressToken
  | .outOfCredits => .outOfCredits
  | .outOfRegisters => .outOfRegisters

/-- Total mapping from Lean ingress failure events to abstract failure classes. -/
def failureClassOfLeanIngressFailure {ι : Type u} [IdentityModel ι] :
    _root_.Failure ι → FailureClass
  | .siteCrash _ => .topologyMutation
  | .partition _ => .topologyMutation
  | .heal _ => .topologyMutation
  | .corrupt _ _ => .transportCorruption
  | .timeout _ _ => .transportTimeout

/-- Rust fault tags mirrored for total cross-target classification mapping. -/
inductive RustFaultTag where
  | typeViolation
  | unknownLabel
  | channelClosed
  | invalidSignature
  | verificationFailed
  | invokeFault
  | acquireFault
  | transferFault
  | specFault
  | closeFault
  | flowViolation
  | noProgressToken
  | outputConditionFault
  | outOfRegisters
  | pcOutOfBounds
  | bufferFull
  | outOfCredits
  deriving Repr, DecidableEq, Inhabited

/-- Total mapping from Rust fault tags to abstract failure classes. -/
def failureClassOfRustFaultTag : RustFaultTag → FailureClass
  | .typeViolation => .typeViolation
  | .unknownLabel => .unknownLabel
  | .channelClosed => .channelClosed
  | .invalidSignature => .signatureInvalid
  | .verificationFailed => .verificationFailed
  | .invokeFault => .invokeFault
  | .acquireFault => .guardFault
  | .transferFault => .transferFault
  | .specFault => .specFault
  | .closeFault => .closeFault
  | .flowViolation => .flowViolation
  | .noProgressToken => .noProgressToken
  | .outputConditionFault => .outputConditionFault
  | .outOfRegisters => .outOfRegisters
  | .pcOutOfBounds => .pcOutOfBounds
  | .bufferFull => .bufferFull
  | .outOfCredits => .outOfCredits

/-- Lean fault mapped to a machine-stable shared error code. -/
def errorCodeOfLeanFault {γ : Type u} (f : _root_.Fault γ) : ErrorCode :=
  errorCodeOfFailureClass (failureClassOfLeanFault f)

/-- Rust fault tag mapped to a machine-stable shared error code. -/
def errorCodeOfRustFaultTag (f : RustFaultTag) : ErrorCode :=
  errorCodeOfFailureClass (failureClassOfRustFaultTag f)

/-- Decode fault-class tags used in structured error artifacts to stable error codes. -/
def errorCodeOfFaultClassTag (faultClass : String) : ErrorCode :=
  if faultClass = "type_violation" then .typeViolation else
  if faultClass = "unknown_label" then .unknownLabel else
  if faultClass = "channel_closed" then .channelClosed else
  if faultClass = "invalid_signature" then .invalidSignature else
  if faultClass = "verification_failed" then .verificationFailed else
  if faultClass = "acquire_fault" then .acquireFault else
  if faultClass = "invoke_fault" then .invokeFault else
  if faultClass = "transfer_fault" then .transferFault else
  if faultClass = "close_fault" then .closeFault else
  if faultClass = "spec_fault" then .specFault else
  if faultClass = "flow_violation" then .flowViolation else
  if faultClass = "no_progress_token" then .noProgressToken else
  if faultClass = "output_condition_fault" then .outputConditionFault else
  if faultClass = "out_of_registers" then .outOfRegisters else
  if faultClass = "pc_out_of_bounds" then .pcOutOfBounds else
  if faultClass = "buffer_full" then .bufferFull else
  if faultClass = "out_of_credits" then .outOfCredits else
  if faultClass = "topology_mutation" then .topologyMutation else
  if faultClass = "transport_corruption" then .transportCorruption else
  if faultClass = "transport_timeout" then .transportTimeout else
  .unknown

/-- Failure-visible snapshot used for cross-target conformance theorems. -/
structure FailureVisibleSnapshot where
  errorCodes : List ErrorCode
  faultClasses : List String
  certainties : List ErrorCertainty
  actions : List ErrorActionTag
  terminalOutcome : Bool
  safetyVerdict : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Build failure-visible snapshots from executable VM states. -/
def vmFailureVisibleSnapshot
    {ι γ π ε ν : Type u}
    [VMDomain ι γ π ε ν]
    (st : VMState ι γ π ε ν) : FailureVisibleSnapshot :=
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

/-- Abstract state transformer used by recovery/action theorems. -/
abbrev RecoveryStep (State : Type u) := State → RecoveryAction → State

/-- Abstract safety theorem form for deterministic recovery actions. -/
def RecoveryActionSafety {State : Type u}
    (Safe : State → Prop)
    (step : RecoveryStep State) : Prop :=
  ∀ st act, Safe st → Safe (step st act)

/-- Preconditions used by no-unsafe-replay theorem forms. -/
structure ReplayPreconditions (State : Type u) where
  nonceFresh : State → Nat → Prop
  reconciled : State → Prop

/-- Abstract no-unsafe-replay theorem form under nonce/reconciliation preconditions. -/
def NoUnsafeReplay {State : Type u}
    (Safe : State → Prop)
    (pre : ReplayPreconditions State)
    (replay : State → Nat → State) : Prop :=
  ∀ st nonce,
    pre.nonceFresh st nonce →
    pre.reconciled st →
    Safe (replay st nonce)

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
theorem restartStructuredErrorAdequacy_identity
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
  recoveryActionSafetyWitness :
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

/-- Extract cross-target failure-envelope conformance theorem from failure premises. -/
theorem crossTargetFailureConformance_of_failurePremises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    CrossTargetFailureConformance
      p.failureVisible p.singleThreadRun p.multiThreadRun p.shardedRun :=
  p.crossTargetConformanceWitness

/-- Extract abstract recovery-action safety theorem from failure premises. -/
theorem recoveryActionSafety_of_failurePremises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    RecoveryActionSafety p.Safe p.recoveryStep :=
  p.recoveryActionSafetyWitness

/-- Extract abstract no-unsafe-replay theorem from failure premises. -/
theorem noUnsafeReplay_of_failurePremises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    NoUnsafeReplay p.Safe p.replayPre p.replay :=
  p.noUnsafeReplayWitness

/-- Extract checkpoint-restart refinement theorem from failure premises. -/
theorem checkpointRestartRefinement_of_failurePremises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    CheckpointRestartRefinement p.Refines p.checkpoint p.restart :=
  p.checkpointRestartRefinementWitness

/-- Extract restart-refinement + structured-error adequacy from failure premises. -/
theorem restartStructuredErrorAdequacy_of_failurePremises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    RestartRefinementStructuredErrorAdequacy
      p.Refines p.checkpoint p.restart p.structuredErrors :=
  p.restartStructuredErrorAdequacyWitness

/-- Extract failure-envelope soundness extension theorem from failure premises. -/
theorem failureEnvelopeSoundness_of_failurePremises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    FailureEnvelopeSoundnessExtension
      p.localEnvelope p.RefRun p.ImplRun p.injectFailure :=
  p.failureEnvelopeSoundnessWitness

/-- Extract failure-envelope maximality extension theorem from failure premises. -/
theorem failureEnvelopeMaximality_of_failurePremises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    FailureEnvelopeMaximalityExtension
      p.localEnvelope p.RefRun p.ImplRun p.injectFailure :=
  p.failureEnvelopeMaximalityWitness

/-- Packaged abstract failure/recovery theorem family. -/
structure FailureEnvelopeProtocol where
  State : Type u
  Obs : Type v
  premises : FailureEnvelopePremises State Obs
  crossTargetConformance :
    CrossTargetFailureConformance
      premises.failureVisible
      premises.singleThreadRun
      premises.multiThreadRun
      premises.shardedRun :=
      crossTargetFailureConformance_of_failurePremises premises
  recoveryActionSafety :
    RecoveryActionSafety premises.Safe premises.recoveryStep :=
      recoveryActionSafety_of_failurePremises premises
  noUnsafeReplay :
    NoUnsafeReplay premises.Safe premises.replayPre premises.replay :=
      noUnsafeReplay_of_failurePremises premises
  checkpointRestartRefinement :
    CheckpointRestartRefinement
      premises.Refines premises.checkpoint premises.restart :=
      checkpointRestartRefinement_of_failurePremises premises
  restartStructuredErrorAdequacy :
    RestartRefinementStructuredErrorAdequacy
      premises.Refines premises.checkpoint premises.restart premises.structuredErrors :=
      restartStructuredErrorAdequacy_of_failurePremises premises
  failureEnvelopeSoundness :
    FailureEnvelopeSoundnessExtension
      premises.localEnvelope premises.RefRun premises.ImplRun premises.injectFailure :=
      failureEnvelopeSoundness_of_failurePremises premises
  failureEnvelopeMaximality :
    FailureEnvelopeMaximalityExtension
      premises.localEnvelope premises.RefRun premises.ImplRun premises.injectFailure :=
      failureEnvelopeMaximality_of_failurePremises premises


end Adequacy
end Runtime
