import Runtime.VM.Model.SemanticObjects.ReplayFailureExactnessLemmas

set_option autoImplicit false

/-! # Runtime.Proofs.VM.ReplayFailureExactness

Proof-facing surface for replay-stable operation identity, terminal-truth
stability, stale late-result rejection, and typed failure exactness.
-/

namespace Runtime
namespace Proofs
namespace VM

abbrev FailureSurfaceExactness := Runtime.VM.Model.FailureSurfaceExactness
abbrev FailureObservationClass := Runtime.VM.Model.FailureObservationClass
abbrev ReplayFailureContext := Runtime.VM.Model.ReplayFailureContext

abbrev replayStableOperationIdentity :=
  Runtime.VM.Model.ProtocolMachineSemanticObjects.replayStableOperationIdentity

abbrev terminalTruthStableUnderReplay :=
  Runtime.VM.Model.ProtocolMachineSemanticObjects.terminalTruthStableUnderReplay

abbrev staleLateResultRejected :=
  Runtime.VM.Model.ProtocolMachineSemanticObjects.staleLateResultRejected

abbrev failureAuditAligned :=
  Runtime.VM.Model.ProtocolMachineSemanticObjects.failureAuditAligned

abbrev replayFailureConformanceAligned :=
  Runtime.VM.Model.ProtocolMachineSemanticObjects.replayFailureConformanceAligned

theorem replayStableOperationIdentity_preserves_kind_and_proof
    {objects : Runtime.VM.Model.ProtocolMachineSemanticObjects}
    (hStable : objects.replayStableOperationIdentity)
    {operation₁ operation₂ : Runtime.VM.Model.OperationInstance}
    (hMem₁ : operation₁ ∈ objects.operationInstances)
    (hMem₂ : operation₂ ∈ objects.operationInstances)
    (hReplay : operation₁.sameReplayIdentity operation₂) :
    operation₁.kind = operation₂.kind ∧
    operation₁.requiresProof = operation₂.requiresProof :=
  Runtime.VM.Model.replayStableOperationIdentity_preserves_kind_and_proof
    hStable hMem₁ hMem₂ hReplay

theorem terminalTruthStableUnderReplay_preserves_publication
    {objects : Runtime.VM.Model.ProtocolMachineSemanticObjects}
    (hStable : objects.terminalTruthStableUnderReplay)
    {operation₁ operation₂ : Runtime.VM.Model.OperationInstance}
    (hMem₁ : operation₁ ∈ objects.operationInstances)
    (hMem₂ : operation₂ ∈ objects.operationInstances)
    (hReplay : operation₁.sameReplayIdentity operation₂)
    (hTruth₁ : operation₁.hasTerminalTruth)
    (hTruth₂ : operation₂.hasTerminalTruth) :
    operation₁.phase = operation₂.phase ∧
    operation₁.terminalPublication = operation₂.terminalPublication :=
  Runtime.VM.Model.terminalTruthStableUnderReplay_preserves_publication
    hStable hMem₁ hMem₂ hReplay hTruth₁ hTruth₂

theorem staleLateResultRejected_rejects_commit
    {objects : Runtime.VM.Model.ProtocolMachineSemanticObjects}
    (hRejected : objects.staleLateResultRejected)
    {effect : Runtime.VM.Model.OutstandingEffect}
    (hMem : effect ∈ objects.outstandingEffects)
    {ownerId : Option String}
    {tick : Nat}
    (hLate : effect.resultIsLate ownerId tick) :
    effect.rejectsCommit ownerId tick :=
  Runtime.VM.Model.staleLateResultRejected_rejects_commit
    hRejected hMem hLate

theorem staleLateResultRejected_is_observationally_silent
    {objects : Runtime.VM.Model.ProtocolMachineSemanticObjects}
    (hRejected : objects.staleLateResultRejected)
    {effect : Runtime.VM.Model.OutstandingEffect}
    (hMem : effect ∈ objects.outstandingEffects)
    {ownerId : Option String}
    {tick : Nat}
    (hLate : effect.resultIsLate ownerId tick) :
    Runtime.Proofs.EffectBisim.ObservationalEq
      Runtime.VM.Model.outstandingEffectObs effect effect :=
  Runtime.VM.Model.staleLateResultRejected_is_observationally_silent
    hRejected hMem hLate

abbrev blocked_and_noProgress_are_wait_equivalent :=
  Runtime.VM.Model.blocked_and_noProgress_are_wait_equivalent

abbrev degraded_is_not_wait_equivalent :=
  Runtime.VM.Model.degraded_is_not_wait_equivalent

theorem exact_failure_equivalence_is_identity
    {left right : Runtime.VM.Model.ProgressState}
    (hLeftExact : left.failureExactness = .exact)
    (hRightExact : right.failureExactness = .exact)
    (hEqv : left.failureObservationallyEquivalent right) :
    left = right :=
  Runtime.VM.Model.exact_failure_equivalence_is_identity
    hLeftExact hRightExact hEqv

theorem failureAuditAligned_exact_requires_canonical_publication
    {objects : Runtime.VM.Model.ProtocolMachineSemanticObjects}
    {ctx : Runtime.VM.Model.ReplayFailureContext}
    (hAligned : objects.failureAuditAligned ctx)
    {contract : Runtime.VM.Model.ProgressContract}
    (hMem : contract ∈ objects.progressContracts)
    (hCtx : contract.matchesReplayFailureContext ctx)
    (hExact : ctx.expectedState.failureExactness = .exact) :
    ∃ event ∈ objects.publicationEvents,
      event.matchesCanonicalReplayAudit ctx :=
  Runtime.VM.Model.failureAuditAligned_exact_requires_canonical_publication
    hAligned hMem hCtx hExact

theorem failureAuditAligned_abstraction_requires_transition
    {objects : Runtime.VM.Model.ProtocolMachineSemanticObjects}
    {ctx : Runtime.VM.Model.ReplayFailureContext}
    (hAligned : objects.failureAuditAligned ctx)
    {contract : Runtime.VM.Model.ProgressContract}
    (hMem : contract ∈ objects.progressContracts)
    (hCtx : contract.matchesReplayFailureContext ctx)
    (hAbstraction : ctx.expectedState.failureExactness = .abstraction) :
    ∃ transition ∈ objects.progressTransitions,
      transition.matchesReplayFailureContext ctx :=
  Runtime.VM.Model.failureAuditAligned_abstraction_requires_transition
    hAligned hMem hCtx hAbstraction

end VM
end Proofs
end Runtime
