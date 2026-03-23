import Runtime.VM.Model.SemanticObjects.ReplayFailureExactness

set_option autoImplicit false

/-!
# Runtime.VM.Model.SemanticObjects.CrossTargetProgressDependentWork

The Problem.
Progress/degradation semantics need an explicit cross-target story, and
declared dependent work must compose parent obligations in a theorem-facing way
rather than remaining runtime discipline. Native and single-threaded wasm
realizations may differ operationally, but they must agree on the semantic
meaning of the targeted progress/failure surfaces and on whether declared
dependent work has discharged.

Solution Structure.
This module defines cross-target progress views over `ProgressContract`, marks
which progress distinctions are exact versus abstraction-level versus
implementation-local, and states parent/child dependent-work composition rules
over `OperationInstance`, `ProgressContract`, and canonical terminal
publication.
-/

namespace Runtime.VM.Model

/-! ## Cross-Target Progress Semantics -/

inductive OperationalRealization where
  | nativeCooperative
  | nativeThreaded
  | wasmSingleThreaded
  deriving Repr, DecidableEq

inductive CrossTargetProgressMeaning where
  | exact
  | abstraction
  | implementationLocal
  deriving Repr, DecidableEq

def ProgressState.crossTargetMeaning : ProgressState → CrossTargetProgressMeaning
  | .pending => .implementationLocal
  | .blocked | .noProgress => .abstraction
  | .degraded | .succeeded | .failed | .cancelled | .timedOut | .handedOff => .exact

def ProgressState.crossTargetEquivalent
    (left right : ProgressState) : Prop :=
  match left.crossTargetMeaning, right.crossTargetMeaning with
  | .exact, .exact => left = right
  | .abstraction, .abstraction => left.failureObservationallyEquivalent right
  | .implementationLocal, .implementationLocal => True
  | _, _ => False

structure RealizedProgressView where
  realization : OperationalRealization
  contract : ProgressContract
  deriving Repr, DecidableEq

def RealizedProgressView.sameSubject
    (left right : RealizedProgressView) : Prop :=
  left.contract.operationId = right.contract.operationId ∧
  left.contract.session = right.contract.session

def RealizedProgressView.crossTargetCompatible
    (left right : RealizedProgressView) : Prop :=
  left.sameSubject right ∧
  left.contract.state.crossTargetEquivalent right.contract.state

def ProtocolMachineSemanticObjects.hasCanonicalTerminalPublicationFor
    (objects : ProtocolMachineSemanticObjects)
    (operationId : String)
    (session : Option Nat) : Prop :=
  ∃ event ∈ objects.publicationEvents,
    event.operationId = operationId ∧
    event.session = session ∧
    event.observerClass = .canonical ∧
    event.status = .published

def ProtocolMachineSemanticObjects.crossTargetProgressPreserved
    (objects : ProtocolMachineSemanticObjects)
    (left right : RealizedProgressView) : Prop :=
  left.crossTargetCompatible right ∧
  (left.contract.isTerminal →
    objects.hasCanonicalTerminalPublicationFor
      left.contract.operationId left.contract.session) ∧
  (right.contract.isTerminal →
    objects.hasCanonicalTerminalPublicationFor
      right.contract.operationId right.contract.session)

/-! ## Declared Dependent Work -/

def OperationInstance.declaresDependentWorkOn
    (parent child : OperationInstance) : Prop :=
  child.operationId ∈ parent.dependentOperationIds ∧
  child.session = parent.session

def OperationInstance.dependentWorkResolvedBy
    (parent child : OperationInstance) : Prop :=
  parent.declaresDependentWorkOn child ∧
  child.ownerId.isSome ∧
  child.hasTerminalTruth

def ProtocolMachineSemanticObjects.dependentWorkFullyResolved
    (objects : ProtocolMachineSemanticObjects)
    (parent : OperationInstance) : Prop :=
  ∀ childId ∈ parent.dependentOperationIds,
    ∃ child ∈ objects.operationInstances,
      child.operationId = childId ∧
      child.session = parent.session ∧
      child.ownerId.isSome ∧
      child.hasTerminalTruth

def ProtocolMachineSemanticObjects.parentTerminalityComposedFromDependents
    (objects : ProtocolMachineSemanticObjects)
    (parent : OperationInstance)
    (contract : ProgressContract) : Prop :=
  contract.tracksOperation parent ∧
  objects.dependentWorkFullyResolved parent ∧
  (contract.isTerminal →
    parent.hasTerminalTruth ∧
    objects.hasCanonicalTerminalPublicationFor
      parent.operationId parent.session)

end Runtime.VM.Model
