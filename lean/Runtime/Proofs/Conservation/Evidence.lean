import Runtime.Proofs.ProtocolMachine.SemanticObjects.AuthoritativeReadsPublication
import Runtime.Proofs.ProtocolMachine.SemanticObjects.MaterializationSuccess

set_option autoImplicit false

/-!
# Runtime.Proofs.Conservation.Evidence

Direct theorem surface for evidence conservation.
-/

namespace Runtime
namespace Proofs
namespace Conservation

open Runtime.ProtocolMachine.Model

theorem observed_read_cannot_author_truth
    (read : ObservedRead)
    (ctx : AuthoritativeCommitmentContext) :
    ¬ read.satisfiesCommitmentContext ctx :=
  Runtime.ProtocolMachine.Model.observedRead_never_satisfies_commitment_context read ctx

theorem authoritative_commit_requires_authoritative_read
    {objects : ProtocolMachineSemanticObjects}
    {ctx : AuthoritativeCommitmentContext}
    (hCommit : objects.authoritativeCommitPermitted ctx) :
    ∃ read ∈ objects.authoritativeReads,
      read.hasAuthorityContext ∧ read.satisfiesCommitmentContext ctx :=
  Runtime.ProtocolMachine.Model.authoritativeCommitPermitted_requires_authorityContext hCommit

theorem observed_materialization_cannot_establish_canonical_success
    {objects : ProtocolMachineSemanticObjects}
    {ctx : SuccessProofContext}
    (hObserved : objects.observedMaterializationInsufficient ctx)
    {read : ObservedRead}
    (hMem : read ∈ objects.observedReads) :
    ¬ read.establishesCanonicalMaterialization ctx :=
  Runtime.ProtocolMachine.Model.observedMaterializationInsufficient_prevents_observed_promotion
    hObserved hMem

theorem weaker_publication_cannot_forge_canonical_materialization
    {objects : ProtocolMachineSemanticObjects}
    {ctx : SuccessProofContext}
    (hWeak : objects.weakerPublicationInsufficient ctx)
    {event : PublicationEvent}
    (hMem : event ∈ objects.publicationEvents)
    (hNonCanonical : event.observerClass ≠ .canonical)
    {proof : MaterializationProof}
    (hProof : proof ∈ objects.materializationProofs)
    {handle : CanonicalHandle}
    (hHandle : handle ∈ objects.canonicalHandles) :
    ¬ event.adequateForSuccessContext ctx proof handle :=
  Runtime.ProtocolMachine.Model.weakerPublicationInsufficient_prevents_noncanonical_forgery
    hWeak hMem hNonCanonical hProof hHandle

theorem canonical_success_requires_canonical_publication_surface
    {objects : ProtocolMachineSemanticObjects}
    {ctx : SuccessProofContext}
    (hAdequate : objects.authoritativeMaterializationAdequate ctx) :
    ∃ event ∈ objects.publicationEvents,
      event.observerClass = .canonical ∧
      event.status = .published ∧
      event.proofRef.isSome ∧
      event.handleRef.isSome :=
  Runtime.ProtocolMachine.Model.publication_backed_materialization_has_canonical_surface
    hAdequate

theorem observed_reads_are_non_authoritative
    (read : ObservedRead) :
    read.isNonAuthoritative :=
  trivial

end Conservation
end Proofs
end Runtime
