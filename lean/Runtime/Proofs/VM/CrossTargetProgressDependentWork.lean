import Runtime.VM.Model.SemanticObjects.CrossTargetProgressDependentWorkLemmas

set_option autoImplicit false

/-! # Runtime.Proofs.VM.CrossTargetProgressDependentWork

Proof-facing surface for cross-target progress semantics and declared
dependent-work composition.
-/

namespace Runtime
namespace Proofs
namespace VM

abbrev OperationalRealization := Runtime.VM.Model.OperationalRealization
abbrev CrossTargetProgressMeaning := Runtime.VM.Model.CrossTargetProgressMeaning
abbrev RealizedProgressView := Runtime.VM.Model.RealizedProgressView

abbrev crossTargetProgressPreserved :=
  Runtime.VM.Model.ProtocolMachineSemanticObjects.crossTargetProgressPreserved

abbrev dependentWorkFullyResolved :=
  Runtime.VM.Model.ProtocolMachineSemanticObjects.dependentWorkFullyResolved

abbrev parentTerminalityComposedFromDependents :=
  Runtime.VM.Model.ProtocolMachineSemanticObjects.parentTerminalityComposedFromDependents

abbrev blocked_noProgress_crossTargetEquivalent :=
  Runtime.VM.Model.blocked_noProgress_crossTargetEquivalent

theorem exact_crossTargetEquivalent_iff_equal
    {left right : Runtime.VM.Model.ProgressState}
    (hLeft : left.crossTargetMeaning = .exact)
    (hRight : right.crossTargetMeaning = .exact) :
    left.crossTargetEquivalent right ↔ left = right :=
  Runtime.VM.Model.exact_crossTargetEquivalent_iff_equal hLeft hRight

theorem exact_crossTargetCompatible_requires_same_state
    {left right : Runtime.VM.Model.RealizedProgressView}
    (hCompat : left.crossTargetCompatible right)
    (hLeft : left.contract.state.crossTargetMeaning = .exact)
    (hRight : right.contract.state.crossTargetMeaning = .exact) :
    left.contract.state = right.contract.state :=
  Runtime.VM.Model.exact_crossTargetCompatible_requires_same_state
    hCompat hLeft hRight

theorem crossTargetProgressPreserved_left_terminal_has_canonical_publication
    {objects : Runtime.VM.Model.ProtocolMachineSemanticObjects}
    {left right : Runtime.VM.Model.RealizedProgressView}
    (hPreserved : objects.crossTargetProgressPreserved left right)
    (hTerminal : left.contract.isTerminal) :
    objects.hasCanonicalTerminalPublicationFor
      left.contract.operationId left.contract.session :=
  Runtime.VM.Model.crossTargetProgressPreserved_left_terminal_has_canonical_publication
    hPreserved hTerminal

theorem crossTargetProgressPreserved_right_terminal_has_canonical_publication
    {objects : Runtime.VM.Model.ProtocolMachineSemanticObjects}
    {left right : Runtime.VM.Model.RealizedProgressView}
    (hPreserved : objects.crossTargetProgressPreserved left right)
    (hTerminal : right.contract.isTerminal) :
    objects.hasCanonicalTerminalPublicationFor
      right.contract.operationId right.contract.session :=
  Runtime.VM.Model.crossTargetProgressPreserved_right_terminal_has_canonical_publication
    hPreserved hTerminal

theorem dependentWorkResolvedBy_has_declared_edge
    {parent child : Runtime.VM.Model.OperationInstance}
    (hResolved : parent.dependentWorkResolvedBy child) :
    child.operationId ∈ parent.dependentOperationIds ∧
    child.session = parent.session :=
  Runtime.VM.Model.dependentWorkResolvedBy_has_declared_edge hResolved

theorem dependentWorkFullyResolved_mem_terminal_child
    {objects : Runtime.VM.Model.ProtocolMachineSemanticObjects}
    {parent : Runtime.VM.Model.OperationInstance}
    (hResolved : objects.dependentWorkFullyResolved parent)
    {childId : String}
    (hMem : childId ∈ parent.dependentOperationIds) :
    ∃ child ∈ objects.operationInstances,
      child.operationId = childId ∧
      child.session = parent.session ∧
      child.ownerId.isSome ∧
      child.hasTerminalTruth :=
  Runtime.VM.Model.dependentWorkFullyResolved_mem_terminal_child hResolved hMem

theorem parentTerminalityComposedFromDependents_terminal_truth
    {objects : Runtime.VM.Model.ProtocolMachineSemanticObjects}
    {parent : Runtime.VM.Model.OperationInstance}
    {contract : Runtime.VM.Model.ProgressContract}
    (hCompose : objects.parentTerminalityComposedFromDependents parent contract)
    (hTerminal : contract.isTerminal) :
    parent.hasTerminalTruth :=
  Runtime.VM.Model.parentTerminalityComposedFromDependents_terminal_truth
    hCompose hTerminal

theorem parentTerminalityComposedFromDependents_canonical_publication
    {objects : Runtime.VM.Model.ProtocolMachineSemanticObjects}
    {parent : Runtime.VM.Model.OperationInstance}
    {contract : Runtime.VM.Model.ProgressContract}
    (hCompose : objects.parentTerminalityComposedFromDependents parent contract)
    (hTerminal : contract.isTerminal) :
    objects.hasCanonicalTerminalPublicationFor
      parent.operationId parent.session :=
  Runtime.VM.Model.parentTerminalityComposedFromDependents_canonical_publication
    hCompose hTerminal

theorem undeclared_child_cannot_discharge_parent
    {parent child : Runtime.VM.Model.OperationInstance}
    (hNotDeclared : child.operationId ∉ parent.dependentOperationIds) :
    ¬ parent.dependentWorkResolvedBy child :=
  Runtime.VM.Model.undeclared_child_cannot_discharge_parent hNotDeclared

end VM
end Proofs
end Runtime
