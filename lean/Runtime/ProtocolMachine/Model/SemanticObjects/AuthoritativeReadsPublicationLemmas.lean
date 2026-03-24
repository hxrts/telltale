import Runtime.ProtocolMachine.Model.SemanticObjects.AuthoritativeReadsPublication

set_option autoImplicit false

/-!
# Runtime.ProtocolMachine.Model.SemanticObjects.AuthoritativeReadsPublicationLemmas

The Problem.
The read/publication model needs theorem-facing consequences: observed reads
must never satisfy authoritative commitment contexts, canonical publication
paths must be unique, and observer-class projections must be noninterfering with
respect to blind publications.

Solution Structure.
This module proves the core read/publication lemmas and packages a semantic-
object observer-projection story using projection, blindness, and
noninterference terminology that mirrors the broader runtime/protocol proofs.
-/

namespace Runtime.ProtocolMachine.Model

/-! ## Commitment Lemmas -/

theorem observedRead_never_satisfies_commitment_context
    (read : ObservedRead)
    (ctx : AuthoritativeCommitmentContext) :
    ¬ read.satisfiesCommitmentContext ctx := by
  simp [ObservedRead.satisfiesCommitmentContext]

theorem authoritativeCommitPermitted_requires_authorityContext
    {objects : ProtocolMachineSemanticObjects}
    {ctx : AuthoritativeCommitmentContext}
    (hCommit : objects.authoritativeCommitPermitted ctx) :
    ∃ read ∈ objects.authoritativeReads,
      read.hasAuthorityContext ∧ read.satisfiesCommitmentContext ctx := by
  rcases hCommit with ⟨read, hMem, hSatisfies⟩
  exact ⟨read, hMem, hSatisfies.1, hSatisfies⟩

theorem observedStateCannotAuthorTruth_of_authoritativeCommitPermitted
    {objects : ProtocolMachineSemanticObjects}
    {ctx : AuthoritativeCommitmentContext}
    (hObserved : objects.observedStateCannotAuthorTruth ctx)
    (hCommit : objects.authoritativeCommitPermitted ctx) :
    ∃ read ∈ objects.authoritativeReads,
      read.satisfiesCommitmentContext ctx := by
  simpa [ProtocolMachineSemanticObjects.authoritativeCommitPermitted] using hCommit

/-! ## Publication Uniqueness / Discipline -/

theorem canonical_publication_unique_for_operation
    {objects : ProtocolMachineSemanticObjects}
    (hUnique : objects.canonicalPublicationPathUnique)
    {event₁ event₂ : PublicationEvent}
    (hMem₁ : event₁ ∈ objects.publicationEvents)
    (hMem₂ : event₂ ∈ objects.publicationEvents)
    (hCanon₁ : event₁.observerClass = .canonical)
    (hCanon₂ : event₂.observerClass = .canonical)
    (hPub₁ : event₁.status = .published)
    (hPub₂ : event₂.status = .published)
    (hOp : event₁.operationId = event₂.operationId)
    (hSession : event₁.session = event₂.session) :
    event₁.publicationId = event₂.publicationId :=
  hUnique event₁ hMem₁ event₂ hMem₂ hCanon₁ hCanon₂ hPub₁ hPub₂ hOp hSession

theorem canonical_publication_surface_exclusive_for_operation
    {objects : ProtocolMachineSemanticObjects}
    (hExclusive : objects.canonicalPublicationSurfaceExclusive)
    {event₁ event₂ : PublicationEvent}
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
  hExclusive event₁ hMem₁ event₂ hMem₂ hCanon₁ hCanon₂ hPub₁ hPub₂ hOp hSession

theorem canonical_published_event_requires_owner_and_proof
    {objects : ProtocolMachineSemanticObjects}
    (hDisciplined : objects.publicationObserverClassDisciplined)
    {event : PublicationEvent}
    (hMem : event ∈ objects.publicationEvents)
    (hCanon : event.observerClass = .canonical)
    (hPublished : event.status = .published) :
    event.ownerId.isSome ∧ event.proofRef.isSome ∧ event.handleRef.isSome :=
  hDisciplined event hMem hCanon hPublished

theorem commitment_publication_requires_handle_and_proof
    {objects : ProtocolMachineSemanticObjects}
    {ctx : AuthoritativeCommitmentContext}
    (hDisciplined : objects.commitmentPublicationDisciplined ctx)
    (hCommit : objects.authoritativeCommitPermitted ctx) :
    ∃ event ∈ objects.publicationEvents,
      event.canonicalPublicationFor ctx ∧
      event.ownerId.isSome ∧ event.proofRef.isSome ∧ event.handleRef.isSome := by
  rcases hDisciplined hCommit with ⟨event, hMem, hCanon, hEvidence⟩
  exact ⟨event, hMem, hCanon, hEvidence.1, hEvidence.2.1, hEvidence.2.2⟩

/-! ## Observer Projection / Blindness / Noninterference -/

def PublicationBlindTo
    (observerClass : PublicationObserverClass)
    (event : PublicationEvent) : Prop :=
  event.observerClass ≠ observerClass

theorem blind_publication_preserves_observer_projection
    (objects : ProtocolMachineSemanticObjects)
    (observerClass : PublicationObserverClass)
    (event : PublicationEvent)
    (hBlind : PublicationBlindTo observerClass event) :
    ProtocolMachineSemanticObjects.observerPublicationProjection
        { objects with publicationEvents := event :: objects.publicationEvents }
        observerClass =
      objects.observerPublicationProjection observerClass := by
  cases hStatus : event.status with
  | rejected =>
      simp [ProtocolMachineSemanticObjects.observerPublicationProjection, hStatus]
  | published =>
      have hNe : event.observerClass ≠ observerClass := hBlind
      simp [ProtocolMachineSemanticObjects.observerPublicationProjection, hStatus, hNe]

theorem observed_read_blind_to_authoritative_commit
    (objects : ProtocolMachineSemanticObjects)
    (ctx : AuthoritativeCommitmentContext)
    (read : ObservedRead) :
    ({ objects with observedReads := read :: objects.observedReads }).authoritativeCommitPermitted ctx =
      objects.authoritativeCommitPermitted ctx := by
  simp [ProtocolMachineSemanticObjects.authoritativeCommitPermitted]

theorem audit_publication_blind_to_canonical_projection
    (objects : ProtocolMachineSemanticObjects)
    (event : PublicationEvent)
    (hAudit : event.observerClass = .audit) :
    ProtocolMachineSemanticObjects.observerPublicationProjection
        { objects with publicationEvents := event :: objects.publicationEvents }
        .canonical =
      objects.observerPublicationProjection .canonical := by
  apply blind_publication_preserves_observer_projection
  simp [PublicationBlindTo, hAudit]

theorem noncanonical_projection_cannot_contain_canonical_publication
    (objects : ProtocolMachineSemanticObjects)
    (observerClass : PublicationObserverClass)
    (hNonCanonical : observerClass ≠ .canonical)
    {event : PublicationEvent}
    (hMem : event ∈ objects.observerPublicationProjection observerClass) :
    ¬ event.canonicalPublicationFor
      { operationId := event.operationId
      , session := event.session
      , ownerId := event.ownerId
      , requiredKind := .outputCondition
      , requiredGeneration := none
      , requiresWitness := false
      , publicationObserverClass := .canonical } := by
  intro hCanon
  rcases List.mem_filter.mp hMem with ⟨_, hVisible⟩
  have hCls : event.observerClass = observerClass := by
    cases hStatus : event.status with
    | rejected =>
        simp [hStatus] at hVisible
    | published =>
        simp [hStatus] at hVisible
        exact hVisible
  have hCanonicalClass : event.observerClass = .canonical := by
    exact hCanon.2.2.1
  have : observerClass = .canonical := by
    simpa [hCls] using hCanonicalClass
  exact hNonCanonical this

theorem observer_projection_noninterference_of_blind_publication
    (objects : ProtocolMachineSemanticObjects)
    (observerClass : PublicationObserverClass)
    (event : PublicationEvent)
    (hBlind : PublicationBlindTo observerClass event) :
    ProtocolMachineSemanticObjects.observerPublicationProjection
        { objects with publicationEvents := event :: objects.publicationEvents }
        observerClass =
      objects.observerPublicationProjection observerClass := by
  exact blind_publication_preserves_observer_projection objects observerClass event hBlind

end Runtime.ProtocolMachine.Model
