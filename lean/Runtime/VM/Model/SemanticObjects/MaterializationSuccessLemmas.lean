import Runtime.VM.Model.SemanticObjects.MaterializationSuccess

set_option autoImplicit false

/-!
# Runtime.VM.Model.SemanticObjects.MaterializationSuccessLemmas

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

namespace Runtime.VM.Model

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

end Runtime.VM.Model
