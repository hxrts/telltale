import Runtime.Proofs.ProtocolMachine.Monitor
import Runtime.Proofs.ProtocolMachine.SemanticObjects.ReplayFailureExactness

set_option autoImplicit false

/-!
# Runtime.Proofs.Conservation.Identity

Direct theorem surface for identity conservation.
-/

namespace Runtime
namespace Proofs
namespace Conservation

open Runtime.ProtocolMachine.Model

theorem replay_identity_preserves_operation_kind_and_proof
    {objects : ProtocolMachineSemanticObjects}
    (hStable : objects.replayStableOperationIdentity)
    {operation₁ operation₂ : OperationInstance}
    (hMem₁ : operation₁ ∈ objects.operationInstances)
    (hMem₂ : operation₂ ∈ objects.operationInstances)
    (hReplay : operation₁.sameReplayIdentity operation₂) :
    operation₁.kind = operation₂.kind ∧
    operation₁.requiresProof = operation₂.requiresProof :=
  Runtime.ProtocolMachine.Model.replayStableOperationIdentity_preserves_kind_and_proof
    hStable hMem₁ hMem₂ hReplay

theorem terminal_truth_is_stable_across_replay
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
  Runtime.ProtocolMachine.Model.terminalTruthStableUnderReplay_preserves_publication
    hStable hMem₁ hMem₂ hReplay hTruth₁ hTruth₂

theorem stale_late_results_are_rejected
    {objects : ProtocolMachineSemanticObjects}
    (hRejected : objects.staleLateResultRejected)
    {effect : OutstandingEffect}
    (hMem : effect ∈ objects.outstandingEffects)
    {ownerId : Option String}
    {tick : Nat}
    (hLate : effect.resultIsLate ownerId tick) :
    effect.rejectsCommit ownerId tick :=
  Runtime.ProtocolMachine.Model.staleLateResultRejected_rejects_commit
    hRejected hMem hLate

theorem identity_monitor_preserves_session_ids {γ : Type} :
    unified_monitor_preserves ({ step := fun sk : SessionKind γ => some sk } : SessionMonitor γ) :=
  unified_monitor_preserves_identity

end Conservation
end Proofs
end Runtime
