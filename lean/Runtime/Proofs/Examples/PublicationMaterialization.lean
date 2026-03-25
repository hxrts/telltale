import Runtime.ProtocolMachine.Model

set_option autoImplicit false

/-! # Runtime.Proofs.Examples.PublicationMaterialization

Small example witnesses for canonical publication-path uniqueness and
authoritative materialization adequacy.
-/

namespace Runtime
namespace Proofs
namespace Examples

open Runtime.ProtocolMachine.Model

def publicationCtx : AuthoritativeCommitmentContext :=
  { operationId := "op-accept"
  , session := some 7
  , ownerId := some "owner-a"
  , requiredKind := .outputCondition
  , requiredGeneration := none
  , requiresWitness := false
  , publicationObserverClass := .canonical
  }

def successCtx : SuccessProofContext :=
  { operationId := "op-accept"
  , operationKind := "accept_invite"
  , session := some 7
  , requiredPredicateRef := "accepted"
  , requiredHandleKind := .materialization
  , requiredOutputDigest := some "digest-1"
  , requiresWitnessRef := false
  }

def successOp : OperationInstance :=
  { operationId := "op-accept"
  , session := some 7
  , ownerId := some "owner-a"
  , kind := "accept_invite"
  , phase := .succeeded
  , handlerIdentity := none
  , effectIds := []
  , dependentOperationIds := []
  , terminalPublication := none
  , budgetTicks := none
  , requiresProof := true
  }

def successProof : MaterializationProof :=
  { proofId := "proof-1"
  , session := some 7
  , predicateRef := "accepted"
  , witnessRef := none
  , outputDigest := "digest-1"
  , passed := true
  }

def successHandle : CanonicalHandle :=
  { handleId := "handle-1"
  , session := some 7
  , ownerId := some "owner-a"
  , kind := .materialization
  , proofRef := some "proof-1"
  }

def successPublication : PublicationEvent :=
  { publicationId := "pub-1"
  , session := some 7
  , operationId := "op-accept"
  , ownerId := some "owner-a"
  , publication := "Accepted(channel)"
  , observerClass := .canonical
  , status := .published
  , proofRef := some "proof-1"
  , handleRef := some "handle-1"
  , reason := none
  }

def auditPublication : PublicationEvent :=
  { publicationId := "pub-audit"
  , session := some 7
  , operationId := "op-accept"
  , ownerId := none
  , publication := "Accepted(redacted)"
  , observerClass := .audit
  , status := .published
  , proofRef := none
  , handleRef := none
  , reason := none
  }

def invitationAgreementProfile : AgreementProfile :=
  { profileName := "InvitationSoftSafeFinalized"
  , visibility := .pending
  , rule := .threshold 2
  , usableAt := .softSafe
  , finalizedAt := .finalized
  , requiredEvidenceKind := .materialization
  }

def invitationAgreementContract : AgreementContract :=
  { contractName := "AcceptInviteAgreement"
  , operationId := "op-accept"
  , session := some 7
  , ownerId := some "owner-a"
  , profileName := some "InvitationSoftSafeFinalized"
  , visibility := .pending
  , rule := .threshold 2
  , usableAt := .softSafe
  , finalizedAt := .finalized
  , requiredEvidenceKind := .materialization
  }

def invitationPrestateBinding : PrestateBinding :=
  { bindingId := "binding-1"
  , operationId := "op-accept"
  , session := some 7
  , stateDigest := "prestate-1"
  , epochRef := some "epoch-7"
  , participantDigest := some "participants-a"
  }

def invitationAgreementEvidence : AgreementEvidence :=
  { evidenceId := "agreement-evidence-1"
  , operationId := "op-accept"
  , session := some 7
  , ownerId := some "owner-a"
  , level := .finalized
  , kind := .materialization
  , reference := "proof-1"
  , authoritative := true
  }

def invitationSoftSafeState : AgreementState :=
  { operationId := "op-accept"
  , session := some 7
  , ownerId := some "owner-a"
  , contractName := "AcceptInviteAgreement"
  , level := .softSafe
  , finalization := none
  , evidenceIds := []
  , lastUpdatedTick := some 4
  , reason := some "soft-safe witness set reached"
  }

def invitationFinalizedState : AgreementState :=
  { operationId := "op-accept"
  , session := some 7
  , ownerId := some "owner-a"
  , contractName := "AcceptInviteAgreement"
  , level := .finalized
  , finalization := some .finalized
  , evidenceIds := ["agreement-evidence-1"]
  , lastUpdatedTick := some 5
  , reason := some "materialization committed"
  }

def publicationObjects : ProtocolMachineSemanticObjects :=
  { operationInstances := [successOp]
  , outstandingEffects := []
  , semanticHandoffs := []
  , transformationObligations := []
  , authoritativeReads := []
  , observedReads := []
  , materializationProofs := [successProof]
  , canonicalHandles := [successHandle]
  , publicationEvents := [successPublication, auditPublication]
  , prestateBindings := [invitationPrestateBinding]
  , agreementProfiles := [invitationAgreementProfile]
  , agreementContracts := [invitationAgreementContract]
  , agreementEvidence := [invitationAgreementEvidence]
  , agreementStates := [invitationSoftSafeState, invitationFinalizedState]
  , regions := []
  , progressContracts := []
  , progressTransitions := []
  }

theorem publicationObjects_exclusive :
    publicationObjects.canonicalPublicationSurfaceExclusive := by
  intro event₁ hMem₁ event₂ hMem₂ hCanon₁ hCanon₂ hPub₁ hPub₂ hOp hSession
  have hEvent₁ : event₁ = successPublication := by
    simp [publicationObjects] at hMem₁
    rcases hMem₁ with rfl | rfl
    · rfl
    · simp [auditPublication] at hCanon₁
  have hEvent₂ : event₂ = successPublication := by
    simp [publicationObjects] at hMem₂
    rcases hMem₂ with rfl | rfl
    · rfl
    · simp [auditPublication] at hCanon₂
  subst hEvent₁
  subst hEvent₂
  simp [successPublication]

theorem publicationObjects_materialization_adequate :
    publicationObjects.authoritativeMaterializationAdequate successCtx := by
  refine ⟨successProof, by simp [publicationObjects], ?_, successHandle, by simp [publicationObjects], ?_, successPublication, by simp [publicationObjects], ?_, ?_⟩
  · simp [MaterializationProof.adequateForSuccessContext, successProof, successCtx]
  · simp [CanonicalHandle.adequateForSuccessContext, successHandle, successCtx, successProof]
  · simp [PublicationEvent.adequateForSuccessContext, successPublication, successCtx, successProof, successHandle]
  · simp [PublicationEvent.hasCanonicalAuthorityEvidence, successPublication]

theorem publicationObjects_noncanonical_forgery_blocked :
    publicationObjects.weakerPublicationInsufficient successCtx := by
  intro event hMem hNonCanonical proof hProof handle hHandle
  have hProofEq : proof = successProof := by
    simpa [publicationObjects] using hProof
  have hHandleEq : handle = successHandle := by
    simpa [publicationObjects] using hHandle
  simp [publicationObjects] at hMem
  rcases hMem with rfl | rfl
  · exfalso
    exact hNonCanonical (by simp [successPublication])
  · subst proof
    subst handle
    intro hAdequate
    simp [PublicationEvent.adequateForSuccessContext, auditPublication,
      successCtx, successProof, successHandle] at hAdequate

theorem publicationObjects_named_agreement_available :
    publicationObjects.namedAgreementProfileAvailable "InvitationSoftSafeFinalized" := by
  refine ⟨invitationAgreementProfile, by simp [publicationObjects], rfl⟩

theorem invitationSoftSafeState_usable :
    invitationAgreementContract.provisionalUsable invitationSoftSafeState := by
  simp [AgreementContract.provisionalUsable, AgreementState.tracksContract,
    AgreementLevel.atLeast, AgreementLevel.rank,
    OperationVisibility.permitsUseAt, invitationAgreementContract,
    invitationSoftSafeState]

theorem invitationFinalization_admissible :
    invitationAgreementContract.finalizationAdmissible
      invitationPrestateBinding invitationAgreementEvidence invitationFinalizedState := by
  simp [AgreementContract.finalizationAdmissible, AgreementState.tracksContract,
    AgreementEvidence.satisfiesContract, invitationAgreementContract,
    invitationPrestateBinding, invitationAgreementEvidence, invitationFinalizedState,
    AgreementLevel.atLeast, AgreementLevel.rank]

theorem publicationObjects_finalization_backed :
    publicationObjects.finalizationBacked successOp := by
  refine ⟨invitationAgreementContract, by simp [publicationObjects], invitationPrestateBinding,
    by simp [publicationObjects], invitationAgreementEvidence, by simp [publicationObjects],
    invitationFinalizedState, by simp [publicationObjects], ?_, ?_⟩
  · simp [AgreementContract.tracksOperation, invitationAgreementContract, successOp]
  · exact invitationFinalization_admissible

example :
    publicationObjects.authoritativeMaterializationAdequate successCtx := by
  exact publicationObjects_materialization_adequate

example :
    publicationObjects.canonicalHandleDomainUnique successCtx := by
  intro handle₁ hHandle₁ handle₂ hHandle₂ hAdequate₁ hAdequate₂
  have h₁ : handle₁ = successHandle := by
    simpa [publicationObjects] using hHandle₁
  have h₂ : handle₂ = successHandle := by
    simpa [publicationObjects] using hHandle₂
  subst h₁
  subst h₂
  rfl

end Examples
end Proofs
end Runtime
