import Runtime.ProtocolMachine.Model.Durability
import Runtime.Proofs.ProtocolMachine.Effects
import Runtime.Proofs.ProtocolMachine.SemanticObjects.AgreementCore

set_option autoImplicit false

namespace Runtime.ProtocolMachine.Model

theorem walSyncMetadata_legal :
    walSyncMetadata.architecturallyLegal := by
  constructor
  · intro hObs
    cases hObs
  constructor
  · intro hBestEffort
    cases hBestEffort
  constructor
  · intro _
    simp [walSyncMetadata, EffectInterfaceMetadata.timeoutRequired,
      EffectTimeoutPolicy.requiresExplicitTimeout]
  constructor
  · intro _
    simp [walSyncMetadata, EffectInterfaceMetadata.timeoutRequired,
      EffectTimeoutPolicy.requiresExplicitTimeout]
  · intro _
    simp [walSyncMetadata]

theorem walSyncMetadata_requires_internal_handler :
    walSyncMetadata.handlerDomain = .internal := by
  exact internalOnly_requires_internal_handler walSyncMetadata
    walSyncMetadata_legal rfl

theorem recovery_rank_monotone_of_escalation
    {currentLevel nextLevel : AgreementLevel}
    {currentFinalization nextFinalization : Option FinalizationOutcome}
    (hEscalation :
      AgreementEscalation currentLevel currentFinalization nextLevel nextFinalization) :
    currentLevel.rank ≤ nextLevel.rank := by
  cases hEscalation <;> decide

theorem durableRecoveryDecision_gate_crossing_requires_recovered_agreement
    {decision : DurableRecoveryDecision}
    (hSound : decision.sound)
    (hGate : decision.gateCrossed = true) :
    decision.recoveredLevel.atLeast decision.gateLevel := by
  exact hSound.2.1 hGate

theorem durableRecoveryDecision_reuseFinalized_preserves_terminal_truth
    {decision : DurableRecoveryDecision}
    (hSound : decision.sound)
    (hReuse : decision.action = .reuseFinalized) :
    decision.recoveredLevel = .finalized ∧
    decision.finalization = some .finalized := by
  exact hSound.2.2.1 hReuse

theorem durableRecoveryDecision_preserveTerminal_requires_terminal_outcome
    {decision : DurableRecoveryDecision}
    (hSound : decision.sound)
    (hPreserve : decision.action = .preserveTerminal) :
    decision.finalization = some .aborted ∨
    decision.finalization = some .rejected ∨
    decision.finalization = some .timedOut := by
  exact hSound.2.2.2 hPreserve

end Runtime.ProtocolMachine.Model
