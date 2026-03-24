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
