import Runtime.Proofs.ProtocolMachine.SemanticObjects.OutstandingEffects
import Runtime.ProtocolMachine.Model.SemanticObjects.ReplayFailureExactness

set_option autoImplicit false

/-!
# Runtime.Proofs.ProtocolMachine.SemanticObjects.ReplayFailureExactness

The Problem.
Replay/failure exactness needs theorem-facing consequences: replay-stable
operation identity should expose stable theorem data, exact failure surfaces
should be distinguished from abstractions, and late-result rejection plus audit
alignment should be usable as proof surfaces.

Solution Structure.
This module proves the basic replay-stability, failure-exactness, and
audit-alignment lemmas over the explicit predicates defined in
`ReplayFailureExactness.lean`.
-/

namespace Runtime.ProtocolMachine.Model

open Runtime.Proofs.EffectBisim

theorem replayStableOperationIdentity_preserves_kind_and_proof
    {objects : ProtocolMachineSemanticObjects}
    (hStable : objects.replayStableOperationIdentity)
    {operation₁ operation₂ : OperationInstance}
    (hMem₁ : operation₁ ∈ objects.operationInstances)
    (hMem₂ : operation₂ ∈ objects.operationInstances)
    (hReplay : operation₁.sameReplayIdentity operation₂) :
    operation₁.kind = operation₂.kind ∧
    operation₁.requiresProof = operation₂.requiresProof :=
  hStable operation₁ hMem₁ operation₂ hMem₂ hReplay

theorem terminalTruthStableUnderReplay_preserves_publication
    {objects : ProtocolMachineSemanticObjects}
    (hStable : objects.terminalTruthStableUnderReplay)
    {operation₁ operation₂ : OperationInstance}
    (hMem₁ : operation₁ ∈ objects.operationInstances)
    (hMem₂ : operation₂ ∈ objects.operationInstances)
    (hReplay : operation₁.sameReplayIdentity operation₂)
    (hTruth₁ : operation₁.hasTerminalTruth)
    (hTruth₂ : operation₂.hasTerminalTruth) :
    operation₁.phase = operation₂.phase ∧
    operation₁.terminalPublication = operation₂.terminalPublication :=
  hStable operation₁ hMem₁ operation₂ hMem₂ hReplay hTruth₁ hTruth₂

theorem staleLateResultRejected_rejects_commit
    {objects : ProtocolMachineSemanticObjects}
    (hRejected : objects.staleLateResultRejected)
    {effect : OutstandingEffect}
    (hMem : effect ∈ objects.outstandingEffects)
    {ownerId : Option String}
    {tick : Nat}
    (hLate : effect.resultIsLate ownerId tick) :
    effect.rejectsCommit ownerId tick :=
  hRejected effect hMem ownerId tick hLate

theorem staleLateResultRejected_is_observationally_silent
    {objects : ProtocolMachineSemanticObjects}
    (hRejected : objects.staleLateResultRejected)
    {effect : OutstandingEffect}
    (hMem : effect ∈ objects.outstandingEffects)
    {ownerId : Option String}
    {tick : Nat}
    (hLate : effect.resultIsLate ownerId tick) :
    ObservationalEq outstandingEffectObs effect effect := by
  have _ : effect.rejectsCommit ownerId tick :=
    staleLateResultRejected_rejects_commit hRejected hMem hLate
  exact rejectLateResult_observationalEq effect ownerId tick hLate

theorem blocked_and_noProgress_are_wait_equivalent :
    ProgressState.failureObservationallyEquivalent .blocked .noProgress := by
  rfl

theorem degraded_is_not_wait_equivalent :
    ¬ ProgressState.failureObservationallyEquivalent .degraded .blocked := by
  simp [ProgressState.failureObservationallyEquivalent,
    ProgressState.failureObservationClass]

theorem exact_failure_equivalence_is_identity
    {left right : ProgressState}
    (hLeftExact : left.failureExactness = .exact)
    (hRightExact : right.failureExactness = .exact)
    (hEqv : left.failureObservationallyEquivalent right) :
    left = right := by
  cases left <;> cases right <;>
    simp [ProgressState.failureExactness,
      ProgressState.failureObservationallyEquivalent,
      ProgressState.failureObservationClass] at hLeftExact hRightExact hEqv ⊢

theorem failureAuditAligned_exact_requires_canonical_publication
    {objects : ProtocolMachineSemanticObjects}
    {ctx : ReplayFailureContext}
    (hAligned : objects.failureAuditAligned ctx)
    {contract : ProgressContract}
    (hMem : contract ∈ objects.progressContracts)
    (hCtx : contract.matchesReplayFailureContext ctx)
    (hExact : ctx.expectedState.failureExactness = .exact) :
    ∃ event ∈ objects.publicationEvents,
      event.matchesCanonicalReplayAudit ctx :=
  (hAligned contract hMem hCtx).1 hExact

theorem failureAuditAligned_abstraction_requires_transition
    {objects : ProtocolMachineSemanticObjects}
    {ctx : ReplayFailureContext}
    (hAligned : objects.failureAuditAligned ctx)
    {contract : ProgressContract}
    (hMem : contract ∈ objects.progressContracts)
    (hCtx : contract.matchesReplayFailureContext ctx)
    (hAbstraction : ctx.expectedState.failureExactness = .abstraction) :
    ∃ transition ∈ objects.progressTransitions,
      transition.matchesReplayFailureContext ctx :=
  (hAligned contract hMem hCtx).2 hAbstraction

theorem replayFailureConformanceAligned_includes_terminal_truth
    {objects : ProtocolMachineSemanticObjects}
    {ctx : ReplayFailureContext}
    (hAligned : objects.replayFailureConformanceAligned ctx) :
    objects.terminalTruthStableUnderReplay :=
  hAligned.2.1

theorem replayFailureConformanceAligned_includes_audit_alignment
    {objects : ProtocolMachineSemanticObjects}
    {ctx : ReplayFailureContext}
    (hAligned : objects.replayFailureConformanceAligned ctx) :
    objects.failureAuditAligned ctx :=
  hAligned.2.2.2

end Runtime.ProtocolMachine.Model
