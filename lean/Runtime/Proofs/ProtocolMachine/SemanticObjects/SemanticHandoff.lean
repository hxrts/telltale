import Protocol.Coherence.ErasureCharacterization
import Runtime.Adequacy.EnvelopeCore.ReconfigurationBridge
import Runtime.Proofs.ProtocolMachine.SemanticObjects.OutstandingEffects
import Runtime.ProtocolMachine.Model.SemanticObjects.SemanticHandoffTransition

set_option autoImplicit false

/-!
# Runtime.Proofs.ProtocolMachine.SemanticObjects.SemanticHandoff

The Problem.
The semantic handoff model needs theorem-facing consequences: one owner before /
one owner after, explicit revocation of the old owner's publication authority,
and an explicit relation to delegation / reconfiguration theorem families.

Solution Structure.
This module proves direct handoff lemmas over the implementation-level transition
functions and packages bridge structures that connect `SemanticHandoff` to
delegation safety and envelope-preservation theorems without identifying them.
-/

namespace Runtime.ProtocolMachine.Model

open Runtime.Adequacy

universe u v

/-! ## Direct Handoff Lemmas -/

theorem operation_owner_activated_after_committed_handoff
    (operation : OperationInstance)
    (handoff : SemanticHandoff)
    (obligation : TransformationObligation)
    (hCommit : handoff.isCommitted)
    (hObligation : obligation.isCommitted)
    (hAffected : obligation.affectsOperation operation) :
    (operation.applyHandoff handoff obligation).ownerId = some handoff.activatedOwnerId := by
  have hCond :
      handoff.status = .committed ∧ obligation.status = .committed ∧
        operation.operationId ∈ obligation.affectedOperationIds := by
    simpa [SemanticHandoff.isCommitted, TransformationObligation.isCommitted,
      TransformationObligation.affectsOperation] using And.intro hCommit (And.intro hObligation hAffected)
  simp [OperationInstance.applyHandoff, hCond]

theorem operation_old_owner_revoked_after_committed_handoff
    (operation : OperationInstance)
    (handoff : SemanticHandoff)
    (obligation : TransformationObligation)
    (hCommit : handoff.isCommitted)
    (hObligation : obligation.isCommitted)
    (hAffected : obligation.affectsOperation operation) :
    handoff.revokedOwnerId ≠ handoff.activatedOwnerId →
    (operation.applyHandoff handoff obligation).ownerId ≠ some handoff.revokedOwnerId := by
  intro hDistinct
  have hActivated :
      (operation.applyHandoff handoff obligation).ownerId = some handoff.activatedOwnerId :=
    operation_owner_activated_after_committed_handoff operation handoff obligation
      hCommit hObligation hAffected
  intro hRevoked
  have hEq : handoff.activatedOwnerId = handoff.revokedOwnerId := by
    have : some handoff.activatedOwnerId = some handoff.revokedOwnerId := hActivated.symm.trans hRevoked
    exact Option.some.inj this
  exact hDistinct hEq.symm

theorem operation_phase_handedOff_when_eligible
    (operation : OperationInstance)
    (handoff : SemanticHandoff)
    (obligation : TransformationObligation)
    (hCommit : handoff.isCommitted)
    (hObligation : obligation.isCommitted)
    (hAffected : obligation.affectsOperation operation)
    (hEligible : operation.handoffEligible) :
    (operation.applyHandoff handoff obligation).phase = .handedOff := by
  have hCond :
      handoff.status = .committed ∧ obligation.status = .committed ∧
        operation.operationId ∈ obligation.affectedOperationIds := by
    simpa [SemanticHandoff.isCommitted, TransformationObligation.isCommitted,
      TransformationObligation.affectsOperation] using And.intro hCommit (And.intro hObligation hAffected)
  have hEligible' : operation.phase = .pending ∨ operation.phase = .blocked := by
    simpa [OperationInstance.handoffEligible] using hEligible
  simp [OperationInstance.applyHandoff, hCond, hEligible']

theorem transported_effect_owner_activated_after_handoff
    (effect : OutstandingEffect)
    (handoff : SemanticHandoff)
    (obligation : TransformationObligation)
    (hCommit : handoff.isCommitted)
    (hObligation : obligation.isCommitted)
    (hTransport : obligation.transportsEffect effect)
    (hNotInvalidated : ¬ obligation.invalidatesEffect effect) :
    (effect.applyHandoff handoff obligation).ownerId = some handoff.activatedOwnerId := by
  have hCond : handoff.status = .committed ∧ obligation.status = .committed := by
    simpa [SemanticHandoff.isCommitted, TransformationObligation.isCommitted] using And.intro hCommit hObligation
  have hTransport' : effect.effectId ∈ obligation.transportedEffectIds := by
    simpa [TransformationObligation.transportsEffect] using hTransport
  have hNotInvalidated' : ¬ effect.effectId ∈ obligation.invalidatedEffectIds := by
    simpa [TransformationObligation.invalidatesEffect] using hNotInvalidated
  simp [OutstandingEffect.applyHandoff, hCond, hTransport', hNotInvalidated']

theorem invalidated_effect_rejects_commit_after_handoff
    (effect : OutstandingEffect)
    (handoff : SemanticHandoff)
    (obligation : TransformationObligation)
    (hCommit : handoff.isCommitted)
    (hObligation : obligation.isCommitted)
    (hInvalidate : obligation.invalidatesEffect effect) :
    (effect.applyHandoff handoff obligation).rejectsCommit (some handoff.activatedOwnerId) handoff.tick := by
  have hCond : handoff.status = .committed ∧ obligation.status = .committed := by
    simpa [SemanticHandoff.isCommitted, TransformationObligation.isCommitted] using And.intro hCommit hObligation
  have hInvalidate' : effect.effectId ∈ obligation.invalidatedEffectIds := by
    simpa [TransformationObligation.invalidatesEffect] using hInvalidate
  intro hAdmissible
  have hApplied :
      effect.applyHandoff handoff obligation =
        { (effect.applyEvent (.invalidated handoff.tick handoff.reason)) with
          ownerId := some handoff.activatedOwnerId } := by
    simp [OutstandingEffect.applyHandoff, hCond, hInvalidate']
  rw [hApplied] at hAdmissible
  have hLive := hAdmissible.1
  simp [OutstandingEffect.isLive, OutstandingEffect.applyEvent] at hLive

theorem revoked_owner_publication_rejected_after_handoff
    (event : PublicationEvent)
    (handoff : SemanticHandoff)
    (obligation : TransformationObligation)
    (hCommit : handoff.isCommitted)
    (hObligation : obligation.isCommitted)
    (hAffected : obligation.affectsPublication event)
    (hOwner : event.ownerId = some handoff.revokedOwnerId) :
    (event.applyHandoff handoff obligation).status = .rejected := by
  have hCond :
      handoff.status = .committed ∧ obligation.status = .committed ∧
        event.operationId ∈ obligation.affectedOperationIds := by
    simpa [SemanticHandoff.isCommitted, TransformationObligation.isCommitted,
      TransformationObligation.affectsPublication] using And.intro hCommit (And.intro hObligation hAffected)
  simp [PublicationEvent.applyHandoff, hCond, hOwner]

/-! ## Delegation / Envelope Bridge -/

structure SemanticHandoffDelegationBridge
    {G G' : GEnv} {D D' : DEnv}
    (handoff : SemanticHandoff) where
  statusCommitted : handoff.isCommitted
  delegation : DelegationStep G G' D D' handoff.session handoff.revokedOwnerId handoff.activatedOwnerId

theorem handoff_bridge_safeDelegation
    {G G' : GEnv} {D D' : DEnv}
    (handoff : SemanticHandoff)
    (bridge : SemanticHandoffDelegationBridge (G := G) (G' := G') (D := D) (D' := D') handoff)
    (hCoh : Coherent G D) :
    SafeDelegation G G' D D' handoff.session handoff.revokedOwnerId handoff.activatedOwnerId := by
  exact delegation_sufficiency hCoh bridge.delegation

structure SemanticHandoffEnvelopeBridge
    {Protocol : Type u} {State : Type v} {Obs : Type (max u v)}
    (handoff : SemanticHandoff)
    (localEnvelope : LocalEnvelope State Obs)
    (delegation : ProtocolDelegationSemantics Protocol State) where
  statusCommitted : handoff.isCommitted
  preservesEnvelope : ProtocolDelegationPreservesEnvelope localEnvelope delegation

theorem handoff_bridge_preservesEnvelope
    {Protocol : Type u} {State : Type v} {Obs : Type (max u v)}
    (handoff : SemanticHandoff)
    (localEnvelope : LocalEnvelope State Obs)
    (delegation : ProtocolDelegationSemantics Protocol State)
    (bridge : SemanticHandoffEnvelopeBridge handoff localEnvelope delegation) :
    ProtocolDelegationPreservesEnvelope localEnvelope delegation :=
  bridge.preservesEnvelope

end Runtime.ProtocolMachine.Model
