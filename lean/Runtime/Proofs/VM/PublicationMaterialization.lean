import Runtime.VM.Model.SemanticObjects.AuthoritativeReadsPublicationLemmas
import Runtime.VM.Model.SemanticObjects.MaterializationSuccessLemmas

set_option autoImplicit false

/-! # Runtime.Proofs.VM.PublicationMaterialization

Proof-facing surface for canonical publication-path uniqueness,
authoritative materialization adequacy, and canonical-materialization
non-forgeability.
-/

namespace Runtime
namespace Proofs
namespace VM

abbrev canonicalPublicationSurfaceExclusive :=
  Runtime.VM.Model.ProtocolMachineSemanticObjects.canonicalPublicationSurfaceExclusive

abbrev authoritativeMaterializationAdequate :=
  Runtime.VM.Model.ProtocolMachineSemanticObjects.authoritativeMaterializationAdequate

abbrev canonicalHandleDomainUnique :=
  Runtime.VM.Model.ProtocolMachineSemanticObjects.canonicalHandleDomainUnique

abbrev weakerPublicationInsufficient :=
  Runtime.VM.Model.ProtocolMachineSemanticObjects.weakerPublicationInsufficient

theorem canonical_publication_surface_exclusive_for_operation
    {objects : Runtime.VM.Model.ProtocolMachineSemanticObjects}
    (hExclusive : objects.canonicalPublicationSurfaceExclusive)
    {event₁ event₂ : Runtime.VM.Model.PublicationEvent}
    (hMem₁ : event₁ ∈ objects.publicationEvents)
    (hMem₂ : event₂ ∈ objects.publicationEvents)
    (hCanon₁ : event₁.observerClass = .canonical)
    (hCanon₂ : event₂.observerClass = .canonical)
    (hPub₁ : event₁.status = .published)
    (hPub₂ : event₂.status = .published)
    (hOp : event₁.operationId = event₂.operationId)
    (hSession : event₁.session = event₂.session) :
    event₁.publicationId = event₂.publicationId ∧
    event₁.proofRef = event₂.proofRef ∧
    event₁.handleRef = event₂.handleRef :=
  Runtime.VM.Model.canonical_publication_surface_exclusive_for_operation
    hExclusive hMem₁ hMem₂ hCanon₁ hCanon₂ hPub₁ hPub₂ hOp hSession

theorem commitment_publication_requires_handle_and_proof
    {objects : Runtime.VM.Model.ProtocolMachineSemanticObjects}
    {ctx : Runtime.VM.Model.AuthoritativeCommitmentContext}
    (hDisciplined : objects.commitmentPublicationDisciplined ctx)
    (hCommit : objects.authoritativeCommitPermitted ctx) :
    ∃ event ∈ objects.publicationEvents,
      event.canonicalPublicationFor ctx ∧
      event.ownerId.isSome ∧
      event.proofRef.isSome ∧
      event.handleRef.isSome :=
  Runtime.VM.Model.commitment_publication_requires_handle_and_proof
    hDisciplined hCommit

theorem authoritativeMaterializationAdequate_requires_publication
    {objects : Runtime.VM.Model.ProtocolMachineSemanticObjects}
    {ctx : Runtime.VM.Model.SuccessProofContext}
    (hAdequate : objects.authoritativeMaterializationAdequate ctx) :
    ∃ proof ∈ objects.materializationProofs,
      proof.adequateForSuccessContext ctx ∧
      ∃ handle ∈ objects.canonicalHandles,
        handle.adequateForSuccessContext ctx proof ∧
        ∃ event ∈ objects.publicationEvents,
          event.adequateForSuccessContext ctx proof handle ∧
          event.hasCanonicalAuthorityEvidence :=
  Runtime.VM.Model.authoritativeMaterializationAdequate_requires_publication
    hAdequate

theorem weakerPublicationInsufficient_prevents_noncanonical_forgery
    {objects : Runtime.VM.Model.ProtocolMachineSemanticObjects}
    {ctx : Runtime.VM.Model.SuccessProofContext}
    (hWeak : objects.weakerPublicationInsufficient ctx)
    {event : Runtime.VM.Model.PublicationEvent}
    (hMem : event ∈ objects.publicationEvents)
    (hNonCanonical : event.observerClass ≠ .canonical)
    {proof : Runtime.VM.Model.MaterializationProof}
    (hProof : proof ∈ objects.materializationProofs)
    {handle : Runtime.VM.Model.CanonicalHandle}
    (hHandle : handle ∈ objects.canonicalHandles) :
    ¬ event.adequateForSuccessContext ctx proof handle :=
  Runtime.VM.Model.weakerPublicationInsufficient_prevents_noncanonical_forgery
    hWeak hMem hNonCanonical hProof hHandle

theorem canonical_handle_domain_unique_for_success_context
    {objects : Runtime.VM.Model.ProtocolMachineSemanticObjects}
    {ctx : Runtime.VM.Model.SuccessProofContext}
    (hUnique : objects.canonicalHandleDomainUnique ctx)
    {handle₁ handle₂ : Runtime.VM.Model.CanonicalHandle}
    (hHandle₁ : handle₁ ∈ objects.canonicalHandles)
    (hHandle₂ : handle₂ ∈ objects.canonicalHandles)
    (hAdequate₁ : ∃ proof ∈ objects.materializationProofs,
        proof.adequateForSuccessContext ctx ∧
        handle₁.adequateForSuccessContext ctx proof)
    (hAdequate₂ : ∃ proof ∈ objects.materializationProofs,
        proof.adequateForSuccessContext ctx ∧
        handle₂.adequateForSuccessContext ctx proof) :
    handle₁.handleId = handle₂.handleId :=
  Runtime.VM.Model.canonical_handle_domain_unique_for_success_context
    hUnique hHandle₁ hHandle₂ hAdequate₁ hAdequate₂

theorem publication_backed_materialization_has_canonical_surface
    {objects : Runtime.VM.Model.ProtocolMachineSemanticObjects}
    {ctx : Runtime.VM.Model.SuccessProofContext}
    (hAdequate : objects.authoritativeMaterializationAdequate ctx) :
    ∃ event ∈ objects.publicationEvents,
      event.observerClass = .canonical ∧
      event.status = .published ∧
      event.proofRef.isSome ∧
      event.handleRef.isSome :=
  Runtime.VM.Model.publication_backed_materialization_has_canonical_surface
    hAdequate

theorem proofless_or_handleless_publication_cannot_materialize
    {ctx : Runtime.VM.Model.SuccessProofContext}
    {event : Runtime.VM.Model.PublicationEvent}
    {proof : Runtime.VM.Model.MaterializationProof}
    {handle : Runtime.VM.Model.CanonicalHandle}
    (hMissing : event.proofRef.isNone ∨ event.handleRef.isNone) :
    ¬ event.adequateForSuccessContext ctx proof handle :=
  Runtime.VM.Model.proofless_or_handleless_publication_cannot_materialize
    hMissing

end VM
end Proofs
end Runtime
