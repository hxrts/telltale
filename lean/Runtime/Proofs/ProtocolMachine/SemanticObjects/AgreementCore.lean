import Runtime.ProtocolMachine.Model.SemanticObjects.AgreementCore

set_option autoImplicit false

/-!
# Runtime.Proofs.ProtocolMachine.SemanticObjects.AgreementCore

The Problem.
The agreement/finality executable core needs a minimal theorem envelope before
Rust mirrors it. In particular, prestate binding, provisional usability,
finalization admissibility, and named-contract reuse should all have direct
theorem-facing consequences.

Solution Structure.
This module proves the core lemmas over the agreement/finality model without
attempting the full theorem-pack integration yet.
-/

namespace Runtime.ProtocolMachine.Model

theorem bindsOperation_preserves_identity
    {binding : PrestateBinding}
    {operation : OperationInstance}
    (hBinding : binding.bindsOperation operation) :
    binding.operationId = operation.operationId ∧
    binding.session = operation.session :=
  hBinding

theorem profile_supportsContract_preserves_generic_core
    {profile : AgreementProfile}
    {contract : AgreementContract}
    (hSupport : profile.supportsContract contract) :
    contract.profileName = some profile.profileName ∧
    contract.visibility = profile.visibility ∧
    contract.rule = profile.rule ∧
    contract.usableAt = profile.usableAt ∧
    contract.finalizedAt = profile.finalizedAt ∧
    contract.requiredEvidenceKind = profile.requiredEvidenceKind :=
  hSupport

theorem provisionalUsable_requires_tracked_contract
    {contract : AgreementContract}
    {state : AgreementState}
    (hUsable : contract.provisionalUsable state) :
    state.tracksContract contract :=
  hUsable.1

theorem provisionalUsable_requires_visibility_permission
    {contract : AgreementContract}
    {state : AgreementState}
    (hUsable : contract.provisionalUsable state) :
    contract.visibility.permitsUseAt state.level :=
  hUsable.2.2.1

theorem provisionalUsable_excludes_aborted
    {contract : AgreementContract}
    {state : AgreementState}
    (hUsable : contract.provisionalUsable state) :
    state.finalization ≠ some .aborted :=
  hUsable.2.2.2.1

theorem finalizationAdmissible_requires_prestate_binding
    {contract : AgreementContract}
    {binding : PrestateBinding}
    {evidence : AgreementEvidence}
    {state : AgreementState}
    (hFinal : contract.finalizationAdmissible binding evidence state) :
    binding.operationId = contract.operationId ∧
    binding.session = contract.session := by
  rcases hFinal with ⟨_, hBindOp, hBindSession, _, _, _, _⟩
  exact ⟨hBindOp, hBindSession⟩

theorem finalizationAdmissible_requires_explicit_evidence
    {contract : AgreementContract}
    {binding : PrestateBinding}
    {evidence : AgreementEvidence}
    {state : AgreementState}
    (hFinal : contract.finalizationAdmissible binding evidence state) :
    evidence.satisfiesContract contract ∧
    evidence.level.atLeast contract.finalizedAt := by
  rcases hFinal with ⟨_, _, _, hEvidence, hLevel, _, _⟩
  exact ⟨hEvidence, hLevel⟩

theorem finalizationAdmissible_requires_authoritative_evidence
    {contract : AgreementContract}
    {binding : PrestateBinding}
    {evidence : AgreementEvidence}
    {state : AgreementState}
    (hFinal : contract.finalizationAdmissible binding evidence state) :
    evidence.authoritative := by
  rcases hFinal with ⟨_, _, _, hEvidence, _, _, _⟩
  exact hEvidence.2.2.2.2

theorem commitmentAlignment_succeeded_requires_finalized
    {operation : OperationInstance}
    {state : AgreementState}
    (hAligned : operation.commitmentAlignedWithAgreementState state)
    (hSucceeded : operation.phase = .succeeded) :
    state.finalization = some .finalized :=
by
  rcases hAligned with ⟨_, _, hSucceededImplies, _, _⟩
  exact hSucceededImplies hSucceeded

theorem commitmentAlignment_finalized_requires_terminal_commitment
    {operation : OperationInstance}
    {state : AgreementState}
    (hAligned : operation.commitmentAlignedWithAgreementState state)
    (hFinalized : state.finalization = some .finalized) :
    operation.phase = .succeeded ∨ operation.phase = .handedOff :=
by
  rcases hAligned with ⟨_, _, _, hFinalizedImplies, _⟩
  exact hFinalizedImplies hFinalized

theorem provisional_can_escalate_to_softSafe :
    AgreementEscalation .provisional none .softSafe none :=
  .provisional_softSafe

theorem softSafe_can_escalate_to_finalized :
    AgreementEscalation .softSafe none .finalized (some .finalized) :=
  .softSafe_finalized

theorem softSafe_can_escalate_to_aborted :
    AgreementEscalation .softSafe none .softSafe (some .aborted) :=
  .softSafe_aborted

theorem escalation_preserves_subject
    {current next : AgreementState}
    (hEscalates : current.escalatesTo next) :
    current.operationId = next.operationId ∧
    current.session = next.session ∧
    current.ownerId = next.ownerId ∧
    current.contractName = next.contractName := by
  exact ⟨hEscalates.1, hEscalates.2.1, hEscalates.2.2.1, hEscalates.2.2.2.1⟩

end Runtime.ProtocolMachine.Model
