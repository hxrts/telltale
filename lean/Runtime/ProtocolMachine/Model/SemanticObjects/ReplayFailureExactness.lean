import Runtime.ProtocolMachine.Model.SemanticObjects.AuthoritativeReadsPublication
import Runtime.ProtocolMachine.Model.SemanticObjects.ProgressContracts

set_option autoImplicit false

/-!
# Runtime.ProtocolMachine.Model.SemanticObjects.ReplayFailureExactness

The Problem.
Replay-visible operation identity, terminal truth, and failure exactness cannot
remain implicit in trace reconstruction. The protocol-machine needs explicit
Lean-level predicates stating when replay preserves operation identity, when
terminal publication is stable, which failure/progress surfaces are exact versus
abstraction-level, and how those surfaces attach to canonical audit and
conformance views.

Solution Structure.
This module defines replay-stability predicates over `OperationInstance`,
failure-surface exactness and observational classes over `ProgressState`, and
audit/conformance predicates tying `ProgressContract`, `ProgressTransition`, and
canonical `PublicationEvent` surfaces together.
-/

namespace Runtime.ProtocolMachine.Model

/-! ## Replay-Stable Operation Identity -/

def OperationInstance.sameReplayIdentity
    (left right : OperationInstance) : Prop :=
  left.operationId = right.operationId ∧
  left.session = right.session

def OperationInstance.hasTerminalTruth
    (operation : OperationInstance) : Prop :=
  operation.terminalPublication.isSome

def ProtocolMachineSemanticObjects.replayStableOperationIdentity
    (objects : ProtocolMachineSemanticObjects) : Prop :=
  ∀ operation₁ ∈ objects.operationInstances,
    ∀ operation₂ ∈ objects.operationInstances,
      operation₁.sameReplayIdentity operation₂ →
      operation₁.kind = operation₂.kind ∧
      operation₁.requiresProof = operation₂.requiresProof

def ProtocolMachineSemanticObjects.terminalTruthStableUnderReplay
    (objects : ProtocolMachineSemanticObjects) : Prop :=
  ∀ operation₁ ∈ objects.operationInstances,
    ∀ operation₂ ∈ objects.operationInstances,
      operation₁.sameReplayIdentity operation₂ →
      operation₁.hasTerminalTruth →
      operation₂.hasTerminalTruth →
      operation₁.phase = operation₂.phase ∧
      operation₁.terminalPublication = operation₂.terminalPublication

def ProtocolMachineSemanticObjects.staleLateResultRejected
    (objects : ProtocolMachineSemanticObjects) : Prop :=
  ∀ effect ∈ objects.outstandingEffects,
    ∀ ownerId tick,
      effect.resultIsLate ownerId tick →
      effect.rejectsCommit ownerId tick

/-! ## Failure Exactness / Observation Classes -/

inductive FailureSurfaceExactness where
  | nonFailure
  | abstraction
  | exact
  deriving Repr, DecidableEq

inductive FailureObservationClass where
  | nonFailure
  | waiting
  | degraded
  | failed
  | cancelled
  | timedOut
  deriving Repr, DecidableEq

def ProgressState.failureExactness : ProgressState → FailureSurfaceExactness
  | .pending | .succeeded | .handedOff => .nonFailure
  | .blocked | .noProgress | .degraded => .abstraction
  | .failed | .cancelled | .timedOut => .exact

def ProgressState.failureObservationClass : ProgressState → FailureObservationClass
  | .pending | .succeeded | .handedOff => .nonFailure
  | .blocked | .noProgress => .waiting
  | .degraded => .degraded
  | .failed => .failed
  | .cancelled => .cancelled
  | .timedOut => .timedOut

def ProgressState.failureObservationallyEquivalent
    (left right : ProgressState) : Prop :=
  left.failureObservationClass = right.failureObservationClass

/-! ## Failure Audit / Conformance Surfaces -/

structure ReplayFailureContext where
  operationId : String
  session : Option Nat
  expectedState : ProgressState
  deriving Repr, DecidableEq

def ProgressContract.matchesReplayFailureContext
    (contract : ProgressContract)
    (ctx : ReplayFailureContext) : Prop :=
  contract.operationId = ctx.operationId ∧
  contract.session = ctx.session ∧
  contract.state = ctx.expectedState

def ProgressTransition.matchesReplayFailureContext
    (transition : ProgressTransition)
    (ctx : ReplayFailureContext) : Prop :=
  transition.operationId = ctx.operationId ∧
  transition.session = ctx.session ∧
  transition.toState = ctx.expectedState

def PublicationEvent.matchesCanonicalReplayAudit
    (event : PublicationEvent)
    (ctx : ReplayFailureContext) : Prop :=
  event.operationId = ctx.operationId ∧
  event.session = ctx.session ∧
  event.observerClass = .canonical ∧
  event.status = .published

def ProtocolMachineSemanticObjects.failureAuditAligned
    (objects : ProtocolMachineSemanticObjects)
    (ctx : ReplayFailureContext) : Prop :=
  ∀ contract ∈ objects.progressContracts,
    contract.matchesReplayFailureContext ctx →
      (ctx.expectedState.failureExactness = .exact →
        ∃ event ∈ objects.publicationEvents,
          event.matchesCanonicalReplayAudit ctx) ∧
      (ctx.expectedState.failureExactness = .abstraction →
        ∃ transition ∈ objects.progressTransitions,
          transition.matchesReplayFailureContext ctx)

def ProtocolMachineSemanticObjects.replayFailureConformanceAligned
    (objects : ProtocolMachineSemanticObjects)
    (ctx : ReplayFailureContext) : Prop :=
  objects.replayStableOperationIdentity ∧
  objects.terminalTruthStableUnderReplay ∧
  objects.staleLateResultRejected ∧
  objects.failureAuditAligned ctx

end Runtime.ProtocolMachine.Model
