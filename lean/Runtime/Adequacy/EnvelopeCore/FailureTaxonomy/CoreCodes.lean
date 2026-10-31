import Runtime.Adequacy.EnvelopeCore.AdmissionLogic
import Runtime.ProtocolMachine.Model.SemanticObjects.ProgressContracts

/-! # FailureTaxonomy.CoreCodesnnFailure classification, shared error-code schema, wire encodings, failure-class and Rust fault-tag mappings. Re-exported by `Runtime.Adequacy.EnvelopeCore.FailureTaxonomy.Core`. -/


/-
The Problem. The protocol machine can fail in many ways (type violations, channel
closure, transport errors, etc.). For deterministic recovery, we need
to classify failures by their certainty level (how much state may be
uncommitted) and map them to recovery actions.

Solution Structure. Define `FailureClass` enumeration covering all
failure modes. Define `CommitCertainty` levels and `RecoveryAction`
vocabulary. Provide failure-to-recovery mappings for structured
error handling.

LONG_FILE_JUSTIFICATION: This file is a mechanically regular taxonomy layer.
Keeping the failure classes, error codes, and recovery-envelope glue in one
document keeps the runtime fault vocabulary auditable as a single surface.
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

/-! ## Shared Error-Code Schema -/

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

/-! ## Error-Code Wire Encodings -/

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

/-! ## Failure-Class Mappings -/

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

/-- Total mapping from Lean protocol machine instruction faults to abstract failure classes. -/
def failureClassOfLeanFault {γ : Type u} : _root_.Fault γ → FailureClass
  | .typeViolation _ _ => .typeViolation
  | .unknownLabel _ => .unknownLabel
  | .channelClosed _ => .channelClosed
  | .invalidSignature _ => .signatureInvalid
  | .acquireFault _ _ => .guardFault
  | .invokeFault _ => .invokeFault
  | .effectFault _ _ => .invokeFault
  | .outputCondition _ => .outputConditionFault
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

/-! ## Rust Fault-Tag Mappings -/

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

/-! ## Fault-Class Tag Decoding -/

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

end Adequacy
end Runtime
