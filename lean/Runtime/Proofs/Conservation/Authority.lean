import Runtime.Proofs.ProtocolMachine.Effects
import Runtime.Proofs.ProtocolMachine.SemanticObjects.AuthoritativeReadsPublication
import Runtime.Proofs.ProtocolMachine.SemanticObjects.SemanticHandoff

set_option autoImplicit false

/-!
# Runtime.Proofs.Conservation.Authority

Direct theorem surface for authority conservation.
-/

namespace Runtime
namespace Proofs
namespace Conservation

open Runtime.ProtocolMachine.Model

theorem observational_effects_do_not_authorize_truth
    (metadata : EffectInterfaceMetadata)
    (hLegal : metadata.architecturallyLegal)
    (hObs : metadata.semanticClass = .observational) :
    metadata.authorityClass ≠ .authoritative :=
  Runtime.ProtocolMachine.Model.observational_surfaces_do_not_author_truth metadata hLegal hObs

theorem best_effort_effects_do_not_authorize_truth
    (metadata : EffectInterfaceMetadata)
    (hLegal : metadata.architecturallyLegal)
    (hBestEffort : metadata.semanticClass = .bestEffort) :
    metadata.authorityClass ≠ .authoritative :=
  Runtime.ProtocolMachine.Model.bestEffort_surfaces_do_not_author_truth metadata hLegal hBestEffort

theorem committed_handoff_activates_new_owner
    (operation : OperationInstance)
    (handoff : SemanticHandoff)
    (obligation : TransformationObligation)
    (hCommit : handoff.isCommitted)
    (hObligation : obligation.isCommitted)
    (hAffected : obligation.affectsOperation operation) :
    (operation.applyHandoff handoff obligation).ownerId = some handoff.activatedOwnerId :=
  Runtime.ProtocolMachine.Model.operation_owner_activated_after_committed_handoff
    operation handoff obligation hCommit hObligation hAffected

theorem committed_handoff_revokes_old_owner
    (operation : OperationInstance)
    (handoff : SemanticHandoff)
    (obligation : TransformationObligation)
    (hCommit : handoff.isCommitted)
    (hObligation : obligation.isCommitted)
    (hAffected : obligation.affectsOperation operation)
    (hDistinct : handoff.revokedOwnerId ≠ handoff.activatedOwnerId) :
    (operation.applyHandoff handoff obligation).ownerId ≠ some handoff.revokedOwnerId :=
  Runtime.ProtocolMachine.Model.operation_old_owner_revoked_after_committed_handoff
    operation handoff obligation hCommit hObligation hAffected hDistinct

theorem revoked_owner_cannot_publish_after_handoff
    (event : PublicationEvent)
    (handoff : SemanticHandoff)
    (obligation : TransformationObligation)
    (hCommit : handoff.isCommitted)
    (hObligation : obligation.isCommitted)
    (hAffected : obligation.affectsPublication event)
    (hOwner : event.ownerId = some handoff.revokedOwnerId) :
    (event.applyHandoff handoff obligation).status = .rejected :=
  Runtime.ProtocolMachine.Model.revoked_owner_publication_rejected_after_handoff
    event handoff obligation hCommit hObligation hAffected hOwner

theorem canonical_publication_requires_owner_and_evidence
    {objects : ProtocolMachineSemanticObjects}
    (hDisciplined : objects.publicationObserverClassDisciplined)
    {event : PublicationEvent}
    (hMem : event ∈ objects.publicationEvents)
    (hCanon : event.observerClass = .canonical)
    (hPublished : event.status = .published) :
    event.ownerId.isSome ∧ event.proofRef.isSome ∧ event.handleRef.isSome :=
  Runtime.ProtocolMachine.Model.canonical_published_event_requires_owner_and_proof
    hDisciplined hMem hCanon hPublished

theorem unique_semantic_owner_preserved
    {objects : ProtocolMachineSemanticObjects}
    {operation₁ operation₂ : OperationInstance}
    (hUnique : objects.uniqueSemanticOwner)
    (hMem₁ : operation₁ ∈ objects.operationInstances)
    (hMem₂ : operation₂ ∈ objects.operationInstances)
    (hId : operation₁.operationId = operation₂.operationId)
    (hOwner₁ : operation₁.phase.requiresActiveOwner)
    (hOwner₂ : operation₂.phase.requiresActiveOwner) :
    operation₁.ownerId = operation₂.ownerId :=
  hUnique operation₁ hMem₁ operation₂ hMem₂ hId hOwner₁ hOwner₂

end Conservation
end Proofs
end Runtime
