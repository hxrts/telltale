import Runtime.Proofs.ProtocolMachine.SemanticObjects.OutstandingEffects
import Runtime.Proofs.ProtocolMachine.SemanticObjects.ProgressContracts
import Runtime.Proofs.ProtocolMachine.SemanticObjects.CrossTargetProgressDependentWork

set_option autoImplicit false

/-!
# Runtime.Proofs.Conservation.Commitment

Direct theorem surface for commitment conservation.
-/

namespace Runtime
namespace Proofs
namespace Conservation

open Runtime.ProtocolMachine.Model

theorem invalidated_commitments_cannot_commit
    (effect : OutstandingEffect)
    (ownerId : Option String)
    (tick : Nat) :
    ¬ (effect.applyEvent (.invalidated tick)).admissibleForCommit ownerId tick :=
  Runtime.ProtocolMachine.Model.invalidated_not_admissible effect ownerId tick

theorem invalidated_commitments_reject_late_results
    (effect : OutstandingEffect)
    (ownerId : Option String)
    (tick : Nat) :
    (effect.applyEvent (.invalidated tick)).resultIsLate ownerId tick :=
  Runtime.ProtocolMachine.Model.late_result_rejected_after_invalidate effect ownerId tick

theorem progress_measure_zero_exactly_when_resolved
    (contract : ProgressContract) :
    contract.progressMeasure = 0 ↔ contract.isTerminal :=
  Runtime.ProtocolMachine.Model.progressMeasure_zero_iff_terminal contract

theorem owner_internal_liveness_explicitly_tracks_operation
    {objects : ProtocolMachineSemanticObjects}
    {contract : ProgressContract}
    (hLiveness : objects.ownerInternalLivenessContract contract) :
    contract.hasBudgetDiscipline ∧
    ∃ operation ∈ objects.operationInstances,
      contract.tracksOperation operation :=
  Runtime.ProtocolMachine.Model.ownerInternalLivenessContract_explicit hLiveness

theorem dependent_work_resolution_requires_terminal_children
    {objects : ProtocolMachineSemanticObjects}
    {parent : OperationInstance}
    (hResolved : objects.dependentWorkFullyResolved parent)
    {childId : String}
    (hMem : childId ∈ parent.dependentOperationIds) :
    ∃ child ∈ objects.operationInstances,
      child.operationId = childId ∧
      child.session = parent.session ∧
      child.ownerId.isSome ∧
      child.hasTerminalTruth :=
  Runtime.ProtocolMachine.Model.dependentWorkFullyResolved_mem_terminal_child
    hResolved hMem

theorem terminal_parent_truth_requires_resolved_dependent_work
    {objects : ProtocolMachineSemanticObjects}
    {parent : OperationInstance}
    {contract : ProgressContract}
    (hCompose : objects.parentTerminalityComposedFromDependents parent contract)
    (hTerminal : contract.isTerminal) :
    parent.hasTerminalTruth :=
  Runtime.ProtocolMachine.Model.parentTerminalityComposedFromDependents_terminal_truth
    hCompose hTerminal

end Conservation
end Proofs
end Runtime
