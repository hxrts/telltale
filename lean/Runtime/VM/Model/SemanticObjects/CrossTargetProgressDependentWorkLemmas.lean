import Runtime.VM.Model.SemanticObjects.CrossTargetProgressDependentWork

set_option autoImplicit false

/-!
# Runtime.VM.Model.SemanticObjects.CrossTargetProgressDependentWorkLemmas

The Problem.
Cross-target progress semantics and dependent-work composition need theorem-
facing consequences: abstraction-level waiting states should compose modulo
observation, exact states should agree literally, and declared dependent work
should be sufficient to discharge parent terminality obligations only when it is
explicit and terminal.

Solution Structure.
This module proves the core compatibility and composition lemmas over the
cross-target progress and dependent-work predicates defined in
`CrossTargetProgressDependentWork.lean`.
-/

namespace Runtime.VM.Model

theorem blocked_noProgress_crossTargetEquivalent :
    ProgressState.crossTargetEquivalent .blocked .noProgress := by
  rfl

theorem exact_crossTargetEquivalent_iff_equal
    {left right : ProgressState}
    (hLeft : left.crossTargetMeaning = .exact)
    (hRight : right.crossTargetMeaning = .exact) :
    left.crossTargetEquivalent right ↔ left = right := by
  cases left <;> cases right <;>
    simp [ProgressState.crossTargetMeaning, ProgressState.crossTargetEquivalent] at hLeft hRight ⊢

theorem exact_crossTargetCompatible_requires_same_state
    {left right : RealizedProgressView}
    (hCompat : left.crossTargetCompatible right)
    (hLeft : left.contract.state.crossTargetMeaning = .exact)
    (hRight : right.contract.state.crossTargetMeaning = .exact) :
    left.contract.state = right.contract.state := by
  exact (exact_crossTargetEquivalent_iff_equal hLeft hRight).1 hCompat.2

theorem crossTargetProgressPreserved_left_terminal_has_canonical_publication
    {objects : ProtocolMachineSemanticObjects}
    {left right : RealizedProgressView}
    (hPreserved : objects.crossTargetProgressPreserved left right)
    (hTerminal : left.contract.isTerminal) :
    objects.hasCanonicalTerminalPublicationFor
      left.contract.operationId left.contract.session :=
  hPreserved.2.1 hTerminal

theorem crossTargetProgressPreserved_right_terminal_has_canonical_publication
    {objects : ProtocolMachineSemanticObjects}
    {left right : RealizedProgressView}
    (hPreserved : objects.crossTargetProgressPreserved left right)
    (hTerminal : right.contract.isTerminal) :
    objects.hasCanonicalTerminalPublicationFor
      right.contract.operationId right.contract.session :=
  hPreserved.2.2 hTerminal

theorem dependentWorkResolvedBy_has_declared_edge
    {parent child : OperationInstance}
    (hResolved : parent.dependentWorkResolvedBy child) :
    child.operationId ∈ parent.dependentOperationIds ∧
    child.session = parent.session :=
  hResolved.1

theorem dependentWorkFullyResolved_mem_terminal_child
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
  hResolved childId hMem

theorem parentTerminalityComposedFromDependents_terminal_truth
    {objects : ProtocolMachineSemanticObjects}
    {parent : OperationInstance}
    {contract : ProgressContract}
    (hCompose : objects.parentTerminalityComposedFromDependents parent contract)
    (hTerminal : contract.isTerminal) :
    parent.hasTerminalTruth :=
  (hCompose.2.2 hTerminal).1

theorem parentTerminalityComposedFromDependents_canonical_publication
    {objects : ProtocolMachineSemanticObjects}
    {parent : OperationInstance}
    {contract : ProgressContract}
    (hCompose : objects.parentTerminalityComposedFromDependents parent contract)
    (hTerminal : contract.isTerminal) :
    objects.hasCanonicalTerminalPublicationFor
      parent.operationId parent.session :=
  (hCompose.2.2 hTerminal).2

theorem undeclared_child_cannot_discharge_parent
    {parent child : OperationInstance}
    (hNotDeclared : child.operationId ∉ parent.dependentOperationIds) :
    ¬ parent.dependentWorkResolvedBy child := by
  intro hResolved
  exact hNotDeclared hResolved.1.1

end Runtime.VM.Model
