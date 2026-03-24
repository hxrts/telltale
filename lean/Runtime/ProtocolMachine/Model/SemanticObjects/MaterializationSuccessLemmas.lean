import Runtime.ProtocolMachine.Model.SemanticObjects.MaterializationSuccess

set_option autoImplicit false

/-!
# Runtime.ProtocolMachine.Model.SemanticObjects.MaterializationSuccessLemmas

The Problem.
The success/materialization model needs theorem-facing consequences: targeted
semantic success must be proof-backed, materialization proofs and canonical
handles must be adequate for the success context, and weaker observations must
not establish canonical materialization.

Solution Structure.
This module proves the core success/materialization lemmas over the
implementation-level semantic objects introduced in
`MaterializationSuccess.lean`.
-/

namespace Runtime.ProtocolMachine.Model

theorem observedRead_never_establishes_canonical_materialization
    (read : ObservedRead)
    (ctx : SuccessProofContext) :
    ¬ read.establishesCanonicalMaterialization ctx := by
  simp [ObservedRead.establishesCanonicalMaterialization]

theorem semanticSuccessPermitted_requires_success_artifacts
    {objects : ProtocolMachineSemanticObjects}
    {ctx : SuccessProofContext}
    (hSuccess : objects.semanticSuccessPermitted ctx) :
    ∃ operation ∈ objects.operationInstances,
      operation.requiresSuccessProofFor ctx ∧
      objects.hasAdequateSuccessArtifacts ctx := by
  simpa [ProtocolMachineSemanticObjects.semanticSuccessPermitted] using hSuccess

theorem successProofBacked_requires_proof_and_handle
    {objects : ProtocolMachineSemanticObjects}
    {ctx : SuccessProofContext}
    (hBacked : objects.successProofBacked ctx)
    {operation : OperationInstance}
    (hMem : operation ∈ objects.operationInstances)
    (hRequires : operation.requiresSuccessProofFor ctx) :
    ∃ proof ∈ objects.materializationProofs,
      proof.adequateForSuccessContext ctx ∧
      ∃ handle ∈ objects.canonicalHandles,
        handle.adequateForSuccessContext ctx proof := by
  exact hBacked operation hMem hRequires

theorem authoritativeMaterializationAdequate_requires_publication
    {objects : ProtocolMachineSemanticObjects}
    {ctx : SuccessProofContext}
    (hAdequate : objects.authoritativeMaterializationAdequate ctx) :
    ∃ proof ∈ objects.materializationProofs,
      proof.adequateForSuccessContext ctx ∧
      ∃ handle ∈ objects.canonicalHandles,
        handle.adequateForSuccessContext ctx proof ∧
        ∃ event ∈ objects.publicationEvents,
          event.adequateForSuccessContext ctx proof handle ∧
          event.hasCanonicalAuthorityEvidence := by
  exact hAdequate

theorem proofless_success_impossible_for_targeted_operation
    {objects : ProtocolMachineSemanticObjects}
    {ctx : SuccessProofContext}
    (hBacked : objects.successProofBacked ctx)
    {operation : OperationInstance}
    (hMem : operation ∈ objects.operationInstances)
    (hRequires : operation.requiresSuccessProofFor ctx) :
    ¬ (¬ ∃ proof ∈ objects.materializationProofs,
          proof.adequateForSuccessContext ctx ∧
          ∃ handle ∈ objects.canonicalHandles,
            handle.adequateForSuccessContext ctx proof) := by
  intro hNoProof
  exact hNoProof (successProofBacked_requires_proof_and_handle hBacked hMem hRequires)

theorem observedMaterializationInsufficient_prevents_observed_promotion
    {objects : ProtocolMachineSemanticObjects}
    {ctx : SuccessProofContext}
    (hObserved : objects.observedMaterializationInsufficient ctx)
    {read : ObservedRead}
    (hMem : read ∈ objects.observedReads) :
    ¬ read.establishesCanonicalMaterialization ctx :=
  hObserved read hMem

theorem weakerPublicationInsufficient_prevents_noncanonical_forgery
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
  hWeak event hMem hNonCanonical proof hProof handle hHandle

theorem adequate_success_artifacts_require_passed_proof
    {objects : ProtocolMachineSemanticObjects}
    {ctx : SuccessProofContext}
    (hArtifacts : objects.hasAdequateSuccessArtifacts ctx) :
    ∃ proof ∈ objects.materializationProofs,
      proof.passed ∧
      ∃ handle ∈ objects.canonicalHandles,
        handle.proofRef = some proof.proofId := by
  rcases hArtifacts with ⟨proof, hProofMem, hProofAdequate, handle, hHandleMem, hHandleAdequate⟩
  rcases hProofAdequate with ⟨_, _, _, _, hPassed⟩
  rcases hHandleAdequate with ⟨_, _, hProofRef⟩
  exact ⟨proof, hProofMem, hPassed, handle, hHandleMem, hProofRef⟩

theorem canonical_handle_domain_unique_for_success_context
    {objects : ProtocolMachineSemanticObjects}
    {ctx : SuccessProofContext}
    (hUnique : objects.canonicalHandleDomainUnique ctx)
    {handle₁ handle₂ : CanonicalHandle}
    (hHandle₁ : handle₁ ∈ objects.canonicalHandles)
    (hHandle₂ : handle₂ ∈ objects.canonicalHandles)
    (hAdequate₁ : ∃ proof ∈ objects.materializationProofs,
        proof.adequateForSuccessContext ctx ∧
        handle₁.adequateForSuccessContext ctx proof)
    (hAdequate₂ : ∃ proof ∈ objects.materializationProofs,
        proof.adequateForSuccessContext ctx ∧
        handle₂.adequateForSuccessContext ctx proof) :
    handle₁.handleId = handle₂.handleId :=
  hUnique handle₁ hHandle₁ handle₂ hHandle₂ hAdequate₁ hAdequate₂

theorem publication_backed_materialization_has_canonical_surface
    {objects : ProtocolMachineSemanticObjects}
    {ctx : SuccessProofContext}
    (hAdequate : objects.authoritativeMaterializationAdequate ctx) :
    ∃ event ∈ objects.publicationEvents,
      event.observerClass = .canonical ∧
      event.status = .published ∧
      event.proofRef.isSome ∧
      event.handleRef.isSome := by
  rcases hAdequate with ⟨proof, hProofMem, hProof, handle, hHandleMem, hHandle, event, hEventMem, hEvent, hEvidence⟩
  refine ⟨event, hEventMem, hEvent.2.2.2.1, hEvent.2.2.1, hEvidence.2.1, hEvidence.2.2⟩

theorem proofless_or_handleless_publication_cannot_materialize
    {ctx : SuccessProofContext}
    {event : PublicationEvent}
    {proof : MaterializationProof}
    {handle : CanonicalHandle}
    (hMissing : event.proofRef.isNone ∨ event.handleRef.isNone) :
    ¬ event.adequateForSuccessContext ctx proof handle := by
  intro hAdequate
  rcases hAdequate with ⟨_, _, _, _, hProofRef, hHandleRef⟩
  cases hMissing with
  | inl hNoProof =>
      simp [hProofRef] at hNoProof
  | inr hNoHandle =>
      simp [hHandleRef] at hNoHandle

end Runtime.ProtocolMachine.Model
