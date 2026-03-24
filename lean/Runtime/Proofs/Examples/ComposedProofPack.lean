import Runtime.Proofs.TheoremPack.API
import Runtime.Proofs.Examples.CrossTargetProgressDependentWork
import Runtime.Proofs.Examples.EffectContracts
import Runtime.Proofs.Examples.PublicationMaterialization
import Runtime.Proofs.Examples.ReplayFailureExactness

set_option autoImplicit false

/-! # Runtime.Proofs.Examples.ComposedProofPack

End-to-end examples building theorem packs from composed proof spaces.
-/

namespace Runtime
namespace Proofs
namespace Examples

universe u v

section

variable {ν : Type u} [VerificationModel ν]
variable {store₀ : SessionStore ν} {State : Type v}

def baseComposedSpace :
    ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.mk
    (Adapters.ProtocolMachineInvariantSpaceWithDistributedProfiles.mk
      (ProtocolMachineInvariantSpace.mk none none none none)
      {})
    {}

def emptySemanticObjects : Runtime.ProtocolMachine.Model.ProtocolMachineSemanticObjects :=
  { operationInstances := []
  , outstandingEffects := []
  , semanticHandoffs := []
  , transformationObligations := []
  , authoritativeReads := []
  , observedReads := []
  , materializationProofs := []
  , canonicalHandles := []
  , publicationEvents := []
  , progressContracts := []
  , progressTransitions := []
  }

def coreSemanticObjectWitness :
    CoreSemanticObjectWitness :=
  { objects := emptySemanticObjects
  , invariants := by
      simp [Runtime.ProtocolMachine.Model.ProtocolMachineSemanticObjects.coreSemanticObjectInvariants,
        Runtime.ProtocolMachine.Model.ProtocolMachineSemanticObjects.explicitOperationIdentity,
        Runtime.ProtocolMachine.Model.ProtocolMachineSemanticObjects.explicitOutstandingEffectIdentity,
        Runtime.ProtocolMachine.Model.ProtocolMachineSemanticObjects.uniqueOperationIds,
        Runtime.ProtocolMachine.Model.ProtocolMachineSemanticObjects.uniqueOutstandingEffectIds,
        Runtime.ProtocolMachine.Model.ProtocolMachineSemanticObjects.uniqueSemanticOwner,
        Runtime.ProtocolMachine.Model.ProtocolMachineSemanticObjects.explicitHandoffs,
        Runtime.ProtocolMachine.Model.ProtocolMachineSemanticObjects.nonAuthoritativeObservedReads,
        Runtime.ProtocolMachine.Model.ProtocolMachineSemanticObjects.disjointReadIdentities,
        emptySemanticObjects]
  }

def semanticWitnessBundle : SemanticObjectWitnessBundle :=
  let authoritativeRead : Runtime.ProtocolMachine.Model.AuthoritativeRead :=
    { readId := "read-accept"
    , session := some 7
    , ownerId := some "owner-a"
    , kind := .outputCondition
    , lifecycle := .verified
    , predicateRef := some "accepted"
    , witnessId := none
    , generation := none
    , reason := none
    }
  let publicationObjectsWithRead : Runtime.ProtocolMachine.Model.ProtocolMachineSemanticObjects :=
    { publicationObjects with authoritativeReads := [authoritativeRead] }
  let authoritativeReadWitness : AuthoritativeReadPublicationWitness :=
    { objects := publicationObjectsWithRead
    , ctx := publicationCtx
    , read := authoritativeRead
    , readMember := by simp [publicationObjectsWithRead]
    , readSatisfiesContext := by
        simp [Runtime.ProtocolMachine.Model.AuthoritativeRead.satisfiesCommitmentContext,
          Runtime.ProtocolMachine.Model.AuthoritativeRead.hasAuthorityContext,
          authoritativeRead, publicationCtx]
    , commitmentPermitted := by
        refine ⟨authoritativeRead, by simp [publicationObjectsWithRead], ?_⟩
        simp [Runtime.ProtocolMachine.Model.AuthoritativeRead.satisfiesCommitmentContext,
          Runtime.ProtocolMachine.Model.AuthoritativeRead.hasAuthorityContext,
          authoritativeRead, publicationCtx]
    , observedCannotAuthorTruth := by
        intro read hMem
        simp [Runtime.ProtocolMachine.Model.ObservedRead.satisfiesCommitmentContext]
    , canonicalPublicationPathUnique := by
        intro event₁ hMem₁ event₂ hMem₂ hCanon₁ hCanon₂ hPub₁ hPub₂ hOp hSession
        have hEvent₁ : event₁ = successPublication := by
          have hMem₁' : event₁ = successPublication ∨ event₁ = auditPublication := by
            simpa [publicationObjectsWithRead, publicationObjects] using hMem₁
          rcases hMem₁' with rfl | rfl
          · rfl
          · simp [auditPublication] at hCanon₁
        have hEvent₂ : event₂ = successPublication := by
          have hMem₂' : event₂ = successPublication ∨ event₂ = auditPublication := by
            simpa [publicationObjectsWithRead, publicationObjects] using hMem₂
          rcases hMem₂' with rfl | rfl
          · rfl
          · simp [auditPublication] at hCanon₂
        subst hEvent₁
        subst hEvent₂
        simp [successPublication]
    , canonicalPublicationSurfaceExclusive := by
        simpa [publicationObjectsWithRead] using publicationObjects_exclusive
    , publicationObserverClassDisciplined := by
        intro event hMem hCanon hPublished
        have hMem' : event = successPublication ∨ event = auditPublication := by
          simpa [publicationObjectsWithRead, publicationObjects] using hMem
        rcases hMem' with rfl | rfl
        · simp [Runtime.ProtocolMachine.Model.PublicationEvent.hasCanonicalAuthorityEvidence,
            successPublication]
        · simp [auditPublication] at hCanon
    }
  let materializationWitness : MaterializationSuccessWitness :=
    { objects := publicationObjects
    , ctx := successCtx
    , operation := successOp
    , proof := successProof
    , handle := successHandle
    , operationMember := by simp [publicationObjects]
    , proofMember := by simp [publicationObjects]
    , handleMember := by simp [publicationObjects]
    , operationRequiresSuccessProof := by
        simp [Runtime.ProtocolMachine.Model.OperationInstance.requiresSuccessProofFor,
          successOp, successCtx]
    , proofAdequate := by
        simp [Runtime.ProtocolMachine.Model.MaterializationProof.adequateForSuccessContext,
          successProof, successCtx]
    , handleAdequate := by
        simp [Runtime.ProtocolMachine.Model.CanonicalHandle.adequateForSuccessContext,
          successHandle, successCtx, successProof]
    , successProofBacked := by
        intro operation hMem hRequires
        have hOperation : operation = successOp := by
          simpa [publicationObjects] using hMem
        subst hOperation
        refine ⟨successProof, by simp [publicationObjects], ?_,
          successHandle, by simp [publicationObjects], ?_⟩
        · simp [Runtime.ProtocolMachine.Model.MaterializationProof.adequateForSuccessContext,
            successProof, successCtx]
        · simp [Runtime.ProtocolMachine.Model.CanonicalHandle.adequateForSuccessContext,
            successHandle, successCtx, successProof]
    , authoritativeMaterializationAdequate := publicationObjects_materialization_adequate
    , canonicalHandleDomainUnique := by
        intro handle₁ hHandle₁ handle₂ hHandle₂ hAdequate₁ hAdequate₂
        have h₁ : handle₁ = successHandle := by
          simpa [publicationObjects] using hHandle₁
        have h₂ : handle₂ = successHandle := by
          simpa [publicationObjects] using hHandle₂
        subst h₁
        subst h₂
        rfl
    , observedMaterializationInsufficient := by
        intro read hMem
        simp [publicationObjects] at hMem
    , weakerPublicationInsufficient := publicationObjects_noncanonical_forgery_blocked
    }
  let progressWitness : ProgressContractWitness :=
    { objects := replayFailureObjects
    , operation := replayFailedOp
    , contract := exactFailureContract
    , operationMember := by simp [replayFailureObjects]
    , tracksOperation := by
        simp [Runtime.ProtocolMachine.Model.ProgressContract.tracksOperation,
          Runtime.ProtocolMachine.Model.ProgressState.expectedOperationPhase,
          exactFailureContract, replayFailedOp]
    , trackedLiveness := by
        constructor
        · simp [Runtime.ProtocolMachine.Model.ProgressContract.hasBudgetDiscipline,
            exactFailureContract]
        · refine ⟨replayFailedOp, by simp [replayFailureObjects], ?_, ?_⟩
          · simp [Runtime.ProtocolMachine.Model.ProgressContract.tracksOperation,
              Runtime.ProtocolMachine.Model.ProgressState.expectedOperationPhase,
              exactFailureContract, replayFailedOp]
          · left
            simp [Runtime.ProtocolMachine.Model.ProgressContract.isTerminal,
              Runtime.ProtocolMachine.Model.ProgressState.isTerminal, exactFailureContract]
    }
  let effectWitness : EffectContractWitness :=
    { metadata := boundedAuthoritativeEffect
    , activeDomain := sameFootprintDomain
    , incomingDomain := sameFootprintDomain'
    , architecturallyLegal := boundedAuthoritativeEffect_legal
    , reentrancyPolicySound := by
        constructor
        · intro hAdmissible
          exact hAdmissible.2
        · intro hPolicy
          exact ⟨boundedAuthoritativeEffect_legal, hPolicy⟩
    }
  let replayWitness : ReplayFailureExactnessWitness :=
    { objects := replayFailureObjects
    , ctx := exactFailureCtx
    , operation := replayFailedOp
    , effect := lateEffect
    , contract := exactFailureContract
    , operationMember := by simp [replayFailureObjects]
    , effectMember := by simp [replayFailureObjects]
    , contractMember := by simp [replayFailureObjects]
    , contractMatchesContext := by
        simp [Runtime.ProtocolMachine.Model.ProgressContract.matchesReplayFailureContext,
          exactFailureContract, exactFailureCtx]
    , replayStableOperationIdentity := replayFailureObjects_identity_stable
    , terminalTruthStableUnderReplay := replayFailureObjects_terminal_truth_stable
    , staleLateResultRejected := replayFailureObjects_stale_late_rejected
    , failureAuditAligned := replayFailureObjects_exact_failure_audit
    , replayFailureConformanceAligned := by
        refine ⟨replayFailureObjects_identity_stable,
          replayFailureObjects_terminal_truth_stable,
          replayFailureObjects_stale_late_rejected,
          replayFailureObjects_exact_failure_audit⟩
    }
  let crossTargetWitness : CrossTargetProgressDependentWorkWitness :=
    { objects := dependentWorkObjects
    , left := nativeSucceeded
    , right := wasmSucceeded
    , parent := parentOp
    , contract := nativeSucceeded.contract
    , parentMember := by simp [dependentWorkObjects]
    , tracksOperation := by
        simp [Runtime.ProtocolMachine.Model.ProgressContract.tracksOperation,
          Runtime.ProtocolMachine.Model.ProgressState.expectedOperationPhase,
          nativeSucceeded, parentOp]
    , crossTargetProgressPreserved := success_views_cross_target_preserved
    , dependentWorkFullyResolved := dependent_work_fully_resolved
    , parentTerminalityComposedFromDependents := parent_terminality_composed
    }
  { coreInvariants? := some coreSemanticObjectWitness
  , authoritativeReadsPublication? := some authoritativeReadWitness
  , materializationSuccess? := some materializationWitness
  , progressContracts? := some progressWitness
  , effectContracts? := some effectWitness
  , replayFailureExactness? := some replayWitness
  , crossTargetProgressDependentWork? := some crossTargetWitness
  }

def semanticComposedSpace :
    ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State :=
  Runtime.Proofs.TheoremPackAPI.composeProofSpacesWithSemanticObjects
    (space := baseComposedSpace (ν := ν) (store₀ := store₀) (State := State))
    (liveness? := none)
    (distributed? := none)
    (classical? := none)
    (output? := none)
    (semanticObjects? := some semanticWitnessBundle)

def composedSpace (bundle : ProtocolMachineLivenessBundle store₀) (ow : OutputConditionWitness) :
    ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State :=
  Runtime.Proofs.TheoremPackAPI.composeProofSpaces
    (space := baseComposedSpace (ν := ν) (store₀ := store₀) (State := State))
    (liveness? := some bundle)
    (distributed? := some ({} : Adapters.DistributedProfiles))
    (classical? := some ({} : Adapters.ClassicalProfiles State))
    (output? := some ow)

/-- Composed spaces can be turned into theorem packs through the API facade. -/
example (bundle : ProtocolMachineLivenessBundle store₀) (ow : OutputConditionWitness) :
    let space := composedSpace (ν := ν) (store₀ := store₀) (State := State) bundle ow
    True := by
  intro
  trivial

/-- Minimal deterministic capability inventories can be extracted from composed packs. -/
example (bundle : ProtocolMachineLivenessBundle store₀) (ow : OutputConditionWitness) :
    let space := composedSpace (ν := ν) (store₀ := store₀) (State := State) bundle ow
    let pack := Runtime.Proofs.TheoremPackAPI.mk (space := space)
    True := by
  intro
  trivial

/-- Semantic-object witness bundles flow through the same theorem-pack API surface. -/
example :
    ("semantic_object_core_invariants", true) ∈
      Runtime.Proofs.TheoremPackAPI.semanticObjectInventory
        (pack := Runtime.Proofs.TheoremPackAPI.mk
          (space := semanticComposedSpace (ν := ν) (store₀ := store₀) (State := State))) := by
  change ("semantic_object_core_invariants", true) ∈
      Runtime.Proofs.SemanticObjectArtifacts.inventory
        (some (Runtime.Proofs.SemanticObjectArtifacts.ofWitnessBundle semanticWitnessBundle))
  simp [Runtime.Proofs.SemanticObjectArtifacts.inventory,
    Runtime.Proofs.SemanticObjectArtifacts.ofWitnessBundle, semanticWitnessBundle]

/-- The newer semantic-object theorem families share the same theorem-pack inventory path. -/
example :
    ("semantic_object_effect_contracts", true) ∈
      Runtime.Proofs.TheoremPackAPI.semanticObjectInventory
        (pack := Runtime.Proofs.TheoremPackAPI.mk
          (space := semanticComposedSpace (ν := ν) (store₀ := store₀) (State := State))) := by
  change ("semantic_object_effect_contracts", true) ∈
      Runtime.Proofs.SemanticObjectArtifacts.inventory
        (some (Runtime.Proofs.SemanticObjectArtifacts.ofWitnessBundle semanticWitnessBundle))
  simp [Runtime.Proofs.SemanticObjectArtifacts.inventory,
    Runtime.Proofs.SemanticObjectArtifacts.ofWitnessBundle, semanticWitnessBundle]

/-- Replay/failure exactness is no longer an isolated theorem island. -/
example :
    ("semantic_object_replay_failure_exactness", true) ∈
      Runtime.Proofs.TheoremPackAPI.semanticObjectInventory
        (pack := Runtime.Proofs.TheoremPackAPI.mk
          (space := semanticComposedSpace (ν := ν) (store₀ := store₀) (State := State))) := by
  change ("semantic_object_replay_failure_exactness", true) ∈
      Runtime.Proofs.SemanticObjectArtifacts.inventory
        (some (Runtime.Proofs.SemanticObjectArtifacts.ofWitnessBundle semanticWitnessBundle))
  simp [Runtime.Proofs.SemanticObjectArtifacts.inventory,
    Runtime.Proofs.SemanticObjectArtifacts.ofWitnessBundle, semanticWitnessBundle]

/-- Cross-target progress / dependent-work witnesses also compose through theorem packs. -/
example :
    ("semantic_object_cross_target_progress_dependent_work", true) ∈
      Runtime.Proofs.TheoremPackAPI.semanticObjectInventory
        (pack := Runtime.Proofs.TheoremPackAPI.mk
          (space := semanticComposedSpace (ν := ν) (store₀ := store₀) (State := State))) := by
  change ("semantic_object_cross_target_progress_dependent_work", true) ∈
      Runtime.Proofs.SemanticObjectArtifacts.inventory
        (some (Runtime.Proofs.SemanticObjectArtifacts.ofWitnessBundle semanticWitnessBundle))
  simp [Runtime.Proofs.SemanticObjectArtifacts.inventory,
    Runtime.Proofs.SemanticObjectArtifacts.ofWitnessBundle, semanticWitnessBundle]

end

end Examples
end Proofs
end Runtime
