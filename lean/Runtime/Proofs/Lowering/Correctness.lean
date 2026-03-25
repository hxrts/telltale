import Runtime.Proofs.Lowering.Core

set_option autoImplicit false

/-!
# Runtime.Proofs.Lowering.Correctness

Correctness and rejection theorems for the proof-oriented lowering chain.
-/

namespace Runtime
namespace Proofs
namespace Lowering

universe u

open Classical

theorem parseSurface_refines
    (surface : TelltaleSurfaceSpec) :
    SurfaceRefinesAST surface (parseSurface surface) :=
  rfl

theorem parseSurface_preserves_globalType
    (surface : TelltaleSurfaceSpec) :
    (parseSurface surface).globalType = surface.globalType :=
  rfl

theorem parseSurface_preserves_requestedRoles
    (surface : TelltaleSurfaceSpec) :
    (parseSurface surface).requestedRoles = surface.requestedRoles :=
  rfl

theorem parseSurface_initializes_projection_payload_empty
    (surface : TelltaleSurfaceSpec) :
    (parseSurface surface).projectedLocalTypes = [] :=
  rfl

theorem lowerASTToSemanticObjects_refines
    (ast : ParsedProtocolAST)
    (objects : Runtime.ProtocolMachine.Model.ProtocolMachineSemanticObjects) :
    ASTRefinesSemanticObjects ast (lowerASTToSemanticObjects ast objects) :=
  rfl

theorem lowerSemanticToProtocolMachine_refines
    (semantic : SemanticLowering) :
    SemanticObjectsRefineProtocolMachine semantic (lowerSemanticToProtocolMachine semantic) :=
  rfl

theorem lowerProtocolMachineToArtifacts_refines
    {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    [Inhabited (EffectRuntime.EffectAction ε)]
    (lowering : ProtocolMachineLowering) :
    ProtocolMachineRefinesArtifacts lowering
      (lowerProtocolMachineToArtifacts (γ := γ) (ε := ε) lowering) :=
  rfl

theorem emitted_local_type_matches_projection
    (lowering : ProtocolMachineLowering)
    {role : Role}
    {lt : SessionTypes.LocalTypeR.LocalTypeR}
    (hMem : (role, lt) ∈ lowering.emittedLocalTypes) :
    (role, lt) ∈ lowering.semantic.ast.projectedLocalTypes := by
  simpa [ProtocolMachineLowering.emittedLocalTypes] using hMem

theorem executable_role_has_projection
    {ast : ParsedProtocolAST}
    (hExec : ast.executable)
    {role : Role}
    (hRole : role ∈ ast.requestedRoles) :
    ∃ lt, (role, lt) ∈ ast.projectedLocalTypes :=
  hExec.2.1 role hRole

theorem generated_artifacts_preserve_globalType
    {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    [Inhabited (EffectRuntime.EffectAction ε)]
    (lowering : ProtocolMachineLowering) :
    (lowerProtocolMachineToArtifacts (γ := γ) (ε := ε) lowering).image.globalType =
      lowering.semantic.ast.globalType := by
  simp [lowerProtocolMachineToArtifacts, CodeImage.fromLocalTypes]

theorem executable_implies_fullSpec
    {ast : ParsedProtocolAST}
    (hExec : ast.executable) :
    ast.fullSpec :=
  hExec.1

theorem executable_implies_projectable
    {ast : ParsedProtocolAST}
    (hExec : ast.executable) :
    ast.projectable :=
  hExec.2.1

theorem non_projectable_rejects_executable_forms
    {ast : ParsedProtocolAST}
    (hNot : ¬ ast.projectable) :
    ¬ ast.executable := by
  intro hExec
  exact hNot hExec.2.1

theorem proof_only_rejects_executable_forms
    {ast : ParsedProtocolAST}
    (hProofOnly : ast.proofOnly) :
    ¬ ast.executable := by
  intro hExec
  exact hExec.2.2 hProofOnly

private theorem missing_projected_role_is_reported
    {ast : ParsedProtocolAST}
    {role : Role}
    (hRole : role ∈ ast.requestedRoles)
    (hMissing : ¬ ∃ lt, (role, lt) ∈ ast.projectedLocalTypes) :
    LoweringRejectionReason.nonProjectableRole role ∈ ast.rejectionReasons := by
  classical
  unfold ParsedProtocolAST.rejectionReasons
  have hFold :
      LoweringRejectionReason.nonProjectableRole role ∈
        ast.requestedRoles.foldr
          (fun role acc =>
            if h : ∃ lt, (role, lt) ∈ ast.projectedLocalTypes then
              acc
            else
              LoweringRejectionReason.nonProjectableRole role :: acc)
          [] := by
    revert role
    induction ast.requestedRoles with
    | nil =>
        intro role hRole
        cases hRole
    | cons head tail ih =>
        intro role hRole hMissing
        simp at hRole
        by_cases hHead : ∃ lt, (head, lt) ∈ ast.projectedLocalTypes
        · simp [hHead]
          cases hRole with
          | inl hEq =>
              cases hEq
              exact False.elim (hMissing hHead)
          | inr hTail =>
              exact ih hTail hMissing
        · simp [hHead]
          cases hRole with
          | inl hEq =>
              cases hEq
              simp
          | inr hTail =>
              exact Or.inr (ih hTail hMissing)
  exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hFold)))

theorem non_projectable_role_is_reported
    {ast : ParsedProtocolAST}
    (hWitness : ∃ role ∈ ast.requestedRoles, ¬ ∃ lt, (role, lt) ∈ ast.projectedLocalTypes) :
    ∃ role, LoweringRejectionReason.nonProjectableRole role ∈ ast.rejectionReasons := by
  rcases hWitness with ⟨role, hRole, hMissing⟩
  exact ⟨role, missing_projected_role_is_reported hRole hMissing⟩

theorem proof_only_surface_is_reported
    {ast : ParsedProtocolAST}
    (hProofOnly : ast.proofOnly) :
    LoweringRejectionReason.proofOnlySurface ∈ ast.rejectionReasons := by
  classical
  unfold ParsedProtocolAST.rejectionReasons
  exact List.mem_append.2 (Or.inr (by
    have hForms : ast.proofOnlyForms = true := hProofOnly
    simp [ParsedProtocolAST.proofOnly, hForms]))

theorem duplicate_requested_roles_are_reported
    {ast : ParsedProtocolAST}
    (hDup : ¬ ast.fullSpec) :
    LoweringRejectionReason.duplicateRequestedRoles ∈ ast.rejectionReasons := by
  classical
  unfold ParsedProtocolAST.rejectionReasons
  exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (by simp [hDup]))))

theorem non_executable_surface_rejects_generated_execution
    {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (artifacts : GeneratedArtifactSurface γ ε)
    (hNot : ¬ artifacts.lowering.semantic.ast.executable) :
    ¬ artifacts.supportsExecution := by
  exact hNot

end Lowering
end Proofs
end Runtime
