import Runtime.ProtocolMachine.Model.SemanticObjects.Core

set_option autoImplicit false

/-!
# Runtime.ProtocolMachine.Model.SemanticObjects.AgreementCore

The Problem.
The protocol-machine needs a more general semantic core for operation
visibility, agreement grade, evidence upgrade, prestate binding, and
finalization. Commitment resolution alone is too narrow: downstream systems
need to model provisional, soft-safe, finalized, and aborted flows without
hard-coding one consensus worldview into the executable core.

Solution Structure.
This module defines executable relations over the canonical agreement/finality
objects in `Core`. It keeps commitment state and agreement state distinct while
providing the operational predicates needed by later proof and Rust-mirroring
phases.
-/

namespace Runtime.ProtocolMachine.Model

def AgreementLevel.rank : AgreementLevel → Nat
  | .none => 0
  | .provisional => 1
  | .softSafe => 2
  | .finalized => 3

def AgreementLevel.atLeast (current required : AgreementLevel) : Prop :=
  required.rank ≤ current.rank

def OperationVisibility.permitsUseAt
    (visibility : OperationVisibility)
    (level : AgreementLevel) : Prop :=
  match visibility with
  | .immediate => True
  | .pending => level.atLeast .provisional
  | .blockedUntilFinalized => level.atLeast .finalized

def PrestateBinding.bindsOperation
    (binding : PrestateBinding)
    (operation : OperationInstance) : Prop :=
  binding.operationId = operation.operationId ∧
  binding.session = operation.session

def AgreementProfile.supportsContract
    (profile : AgreementProfile)
    (contract : AgreementContract) : Prop :=
  contract.profileName = some profile.profileName ∧
  contract.visibility = profile.visibility ∧
  contract.rule = profile.rule ∧
  contract.usableAt = profile.usableAt ∧
  contract.finalizedAt = profile.finalizedAt ∧
  contract.requiredEvidenceKind = profile.requiredEvidenceKind

def AgreementContract.tracksOperation
    (contract : AgreementContract)
    (operation : OperationInstance) : Prop :=
  contract.operationId = operation.operationId ∧
  contract.session = operation.session ∧
  contract.ownerId = operation.ownerId

def AgreementState.tracksContract
    (state : AgreementState)
    (contract : AgreementContract) : Prop :=
  state.operationId = contract.operationId ∧
  state.session = contract.session ∧
  state.ownerId = contract.ownerId ∧
  state.contractName = contract.contractName

def AgreementState.isTerminal (state : AgreementState) : Prop :=
  state.finalization.isSome

def AgreementEvidence.satisfiesContract
    (evidence : AgreementEvidence)
    (contract : AgreementContract) : Prop :=
  evidence.operationId = contract.operationId ∧
  evidence.session = contract.session ∧
  evidence.ownerId = contract.ownerId ∧
  evidence.kind = contract.requiredEvidenceKind ∧
  evidence.authoritative

def PublicationEvent.supportsAgreementEvidence
    (event : PublicationEvent)
    (evidence : AgreementEvidence) : Prop :=
  evidence.kind = .publication ∧
  evidence.reference = event.publicationId ∧
  evidence.operationId = event.operationId ∧
  evidence.session = event.session ∧
  evidence.ownerId = event.ownerId ∧
  evidence.authoritative = (event.proofRef.isSome ∧ event.handleRef.isSome)

def MaterializationProof.supportsAgreementEvidence
    (proof : MaterializationProof)
    (evidence : AgreementEvidence) : Prop :=
  evidence.kind = .materialization ∧
  evidence.reference = proof.proofId ∧
  evidence.session = proof.session ∧
  evidence.authoritative = proof.passed

def CanonicalHandle.supportsAgreementEvidence
    (handle : CanonicalHandle)
    (evidence : AgreementEvidence) : Prop :=
  evidence.reference = handle.handleId ∧
  evidence.session = handle.session ∧
  evidence.ownerId = handle.ownerId

def SemanticHandoff.relocatesAgreementState
    (handoff : SemanticHandoff)
    (state : AgreementState) : Prop :=
  state.session = some handoff.session ∧
  state.ownerId = some handoff.activatedOwnerId

def AgreementContract.provisionalUsable
    (contract : AgreementContract)
    (state : AgreementState) : Prop :=
  state.tracksContract contract ∧
  state.level.atLeast contract.usableAt ∧
  contract.visibility.permitsUseAt state.level ∧
  state.finalization ≠ some .aborted ∧
  state.finalization ≠ some .rejected ∧
  state.finalization ≠ some .timedOut

def AgreementContract.finalizationAdmissible
    (contract : AgreementContract)
    (binding : PrestateBinding)
    (evidence : AgreementEvidence)
    (state : AgreementState) : Prop :=
  state.tracksContract contract ∧
  binding.operationId = contract.operationId ∧
  binding.session = contract.session ∧
  evidence.satisfiesContract contract ∧
  evidence.level.atLeast contract.finalizedAt ∧
  state.level = contract.finalizedAt ∧
  state.finalization = some .finalized

def AgreementContract.abortedState
    (contract : AgreementContract)
    (state : AgreementState) : Prop :=
  state.tracksContract contract ∧
  state.finalization = some .aborted

def OperationInstance.commitmentAlignedWithAgreementState
    (operation : OperationInstance)
    (state : AgreementState) : Prop :=
  state.operationId = operation.operationId ∧
  state.session = operation.session ∧
  (operation.phase = .succeeded → state.finalization = some .finalized) ∧
  (state.finalization = some .finalized →
    operation.phase = .succeeded ∨ operation.phase = .handedOff) ∧
  (state.finalization = some .aborted →
    operation.phase = .failed ∨
    operation.phase = .cancelled ∨
    operation.phase = .timedOut)

inductive AgreementEscalation :
    AgreementLevel → Option FinalizationOutcome →
    AgreementLevel → Option FinalizationOutcome → Prop where
  | provisional_softSafe :
      AgreementEscalation .provisional none .softSafe none
  | provisional_finalized :
      AgreementEscalation .provisional none .finalized (some .finalized)
  | provisional_aborted :
      AgreementEscalation .provisional none .provisional (some .aborted)
  | softSafe_finalized :
      AgreementEscalation .softSafe none .finalized (some .finalized)
  | softSafe_aborted :
      AgreementEscalation .softSafe none .softSafe (some .aborted)
  | softSafe_rejected :
      AgreementEscalation .softSafe none .softSafe (some .rejected)
  | softSafe_timedOut :
      AgreementEscalation .softSafe none .softSafe (some .timedOut)

def AgreementState.escalatesTo
    (current next : AgreementState) : Prop :=
  current.operationId = next.operationId ∧
  current.session = next.session ∧
  current.ownerId = next.ownerId ∧
  current.contractName = next.contractName ∧
  AgreementEscalation current.level current.finalization next.level next.finalization

def ProtocolMachineSemanticObjects.namedAgreementProfileAvailable
    (objects : ProtocolMachineSemanticObjects)
    (profileName : String) : Prop :=
  ∃ profile ∈ objects.agreementProfiles,
    profile.profileName = profileName

def ProtocolMachineSemanticObjects.agreementContractForOperation
    (objects : ProtocolMachineSemanticObjects)
    (operation : OperationInstance) : Prop :=
  ∃ contract ∈ objects.agreementContracts,
    contract.tracksOperation operation

def ProtocolMachineSemanticObjects.agreementStateForOperation
    (objects : ProtocolMachineSemanticObjects)
    (operation : OperationInstance) : Prop :=
  ∃ state ∈ objects.agreementStates,
    state.operationId = operation.operationId ∧
    state.session = operation.session

def ProtocolMachineSemanticObjects.prestateBindingForOperation
    (objects : ProtocolMachineSemanticObjects)
    (operation : OperationInstance) : Prop :=
  ∃ binding ∈ objects.prestateBindings,
    binding.bindsOperation operation

def ProtocolMachineSemanticObjects.agreementEvidenceForOperation
    (objects : ProtocolMachineSemanticObjects)
    (operation : OperationInstance) : Prop :=
  ∃ evidence ∈ objects.agreementEvidence,
    evidence.operationId = operation.operationId ∧
    evidence.session = operation.session

def ProtocolMachineSemanticObjects.provisionalAgreementUsable
    (objects : ProtocolMachineSemanticObjects)
    (operation : OperationInstance) : Prop :=
  ∃ contract ∈ objects.agreementContracts,
    ∃ state ∈ objects.agreementStates,
      contract.tracksOperation operation ∧
      contract.provisionalUsable state

def ProtocolMachineSemanticObjects.finalizationBacked
    (objects : ProtocolMachineSemanticObjects)
    (operation : OperationInstance) : Prop :=
  ∃ contract ∈ objects.agreementContracts,
    ∃ binding ∈ objects.prestateBindings,
      ∃ evidence ∈ objects.agreementEvidence,
        ∃ state ∈ objects.agreementStates,
          contract.tracksOperation operation ∧
          contract.finalizationAdmissible binding evidence state

end Runtime.ProtocolMachine.Model
