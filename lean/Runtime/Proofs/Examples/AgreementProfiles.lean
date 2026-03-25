import Runtime.ProtocolMachine.Model.SemanticObjects.AgreementCore

set_option autoImplicit false

/-! # Runtime.Proofs.Examples.AgreementProfiles

Small example witnesses for reusable named agreement profiles over the generic
agreement/finality core.
-/

namespace Runtime
namespace Proofs
namespace Examples

open Runtime.ProtocolMachine.Model

def thresholdFinalizedProfile : AgreementProfile :=
  { profileName := "ThresholdSoftSafeFinalized"
  , visibility := .pending
  , rule := .threshold 3
  , usableAt := .softSafe
  , finalizedAt := .finalized
  , requiredEvidenceKind := .commitFact
  }

def ceremonyOperation : OperationInstance :=
  { operationId := "ceremony-42"
  , session := some 12
  , ownerId := some "coordinator"
  , kind := "establish_context"
  , phase := .succeeded
  , handlerIdentity := none
  , effectIds := []
  , dependentOperationIds := []
  , terminalPublication := some "CommitFact"
  , budgetTicks := some 8
  , requiresProof := true
  }

def thresholdAgreementContract : AgreementContract :=
  { contractName := "ThresholdContextAgreement"
  , operationId := "ceremony-42"
  , session := some 12
  , ownerId := some "coordinator"
  , profileName := some "ThresholdSoftSafeFinalized"
  , visibility := .pending
  , rule := .threshold 3
  , usableAt := .softSafe
  , finalizedAt := .finalized
  , requiredEvidenceKind := .commitFact
  }

def ceremonyBinding : PrestateBinding :=
  { bindingId := "binding-42"
  , operationId := "ceremony-42"
  , session := some 12
  , stateDigest := "prestate-digest"
  , epochRef := some "epoch-3"
  , participantDigest := some "participants-digest"
  }

def commitFactEvidence : AgreementEvidence :=
  { evidenceId := "commit-fact-42"
  , operationId := "ceremony-42"
  , session := some 12
  , ownerId := some "coordinator"
  , level := .finalized
  , kind := .commitFact
  , reference := "CommitFact#42"
  , authoritative := true
  }

def softSafeState : AgreementState :=
  { operationId := "ceremony-42"
  , session := some 12
  , ownerId := some "coordinator"
  , contractName := "ThresholdContextAgreement"
  , level := .softSafe
  , finalization := none
  , evidenceIds := []
  , lastUpdatedTick := some 6
  , reason := some "soft-safe certificate emitted"
  }

def finalizedState : AgreementState :=
  { operationId := "ceremony-42"
  , session := some 12
  , ownerId := some "coordinator"
  , contractName := "ThresholdContextAgreement"
  , level := .finalized
  , finalization := some .finalized
  , evidenceIds := ["commit-fact-42"]
  , lastUpdatedTick := some 8
  , reason := some "commit fact materialized"
  }

def agreementObjects : ProtocolMachineSemanticObjects :=
  { operationInstances := [ceremonyOperation]
  , outstandingEffects := []
  , semanticHandoffs := []
  , transformationObligations := []
  , authoritativeReads := []
  , observedReads := []
  , materializationProofs := []
  , canonicalHandles := []
  , publicationEvents := []
  , prestateBindings := [ceremonyBinding]
  , agreementProfiles := [thresholdFinalizedProfile]
  , agreementContracts := [thresholdAgreementContract]
  , agreementEvidence := [commitFactEvidence]
  , agreementStates := [softSafeState, finalizedState]
  , regions := []
  , progressContracts := []
  , progressTransitions := []
  }

theorem profile_available :
    agreementObjects.namedAgreementProfileAvailable "ThresholdSoftSafeFinalized" := by
  refine ⟨thresholdFinalizedProfile, by simp [agreementObjects], rfl⟩

theorem softSafe_usable :
    thresholdAgreementContract.provisionalUsable softSafeState := by
  simp [AgreementContract.provisionalUsable, AgreementState.tracksContract,
    AgreementLevel.atLeast, AgreementLevel.rank,
    OperationVisibility.permitsUseAt, thresholdAgreementContract, softSafeState]

theorem finalization_admissible :
    thresholdAgreementContract.finalizationAdmissible
      ceremonyBinding commitFactEvidence finalizedState := by
  simp [AgreementContract.finalizationAdmissible, AgreementState.tracksContract,
    AgreementEvidence.satisfiesContract, thresholdAgreementContract, ceremonyBinding,
    commitFactEvidence, finalizedState, AgreementLevel.atLeast, AgreementLevel.rank]

theorem commitment_aligned :
    ceremonyOperation.commitmentAlignedWithAgreementState finalizedState := by
  simp [OperationInstance.commitmentAlignedWithAgreementState,
    ceremonyOperation, finalizedState]

end Examples
end Proofs
end Runtime
