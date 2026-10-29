import Runtime.Proofs.InvariantSpace
import Runtime.Proofs.TheoremPack.Profiles

/-! # Theorem Pack Artifacts: Core

Semantic-object artifact family and proof-carrying artifact metadata. -/

set_option autoImplicit false

namespace Runtime
namespace Proofs

universe u v

section

variable {ν : Type u} [VerificationModel ν]
variable [EntropyAPI.AnalysisLaws]

/-! ## Semantic Object Artifact Family -/

/-- Packaged theorem-pack view of protocol-machine semantic-object witnesses. -/
structure SemanticObjectArtifacts where
  coreInvariants? : Option CoreSemanticObjectWitness := none
  outstandingEffects? : Option OutstandingEffectSemanticWitness := none
  semanticHandoffs? : Option SemanticHandoffWitness := none
  authoritativeReadsPublication? : Option AuthoritativeReadPublicationWitness := none
  materializationSuccess? : Option MaterializationSuccessWitness := none
  progressContracts : ProgressContractWitness
  effectContracts? : Option EffectContractWitness := none
  replayFailureExactness? : Option ReplayFailureExactnessWitness := none
  crossTargetProgressDependentWork? :
    Option CrossTargetProgressDependentWorkWitness := none
  transformationLocalObligations? : Option TransformationLocalObligationWitness := none

/-- Lift invariant-space semantic witnesses into the theorem-pack artifact layer. -/
def SemanticObjectArtifacts.ofWitnessBundle
    (bundle : SemanticObjectWitnessBundle) : SemanticObjectArtifacts :=
  { coreInvariants? := bundle.coreInvariants?
  , outstandingEffects? := bundle.outstandingEffects?
  , semanticHandoffs? := bundle.semanticHandoffs?
  , authoritativeReadsPublication? := bundle.authoritativeReadsPublication?
  , materializationSuccess? := bundle.materializationSuccess?
  , progressContracts := bundle.progressContracts
  , effectContracts? := bundle.effectContracts?
  , replayFailureExactness? := bundle.replayFailureExactness?
  , crossTargetProgressDependentWork? := bundle.crossTargetProgressDependentWork?
  , transformationLocalObligations? := bundle.transformationLocalObligations?
  }

/-- Inventory view for semantic-object theorem families carried by one theorem pack. -/
def SemanticObjectArtifacts.inventory
    (artifacts? : Option SemanticObjectArtifacts) : List (String × Bool) :=
  match artifacts? with
  | some artifacts =>
      [ ("semantic_object_core_invariants", artifacts.coreInvariants?.isSome)
      , ("semantic_object_outstanding_effects", artifacts.outstandingEffects?.isSome)
      , ("semantic_object_semantic_handoffs", artifacts.semanticHandoffs?.isSome)
      , ("semantic_object_authoritative_reads_publication",
          artifacts.authoritativeReadsPublication?.isSome)
      , ("semantic_object_materialization_success", artifacts.materializationSuccess?.isSome)
      , ("semantic_object_progress_contracts", true)
      , ("semantic_object_effect_contracts", artifacts.effectContracts?.isSome)
      , ("semantic_object_replay_failure_exactness",
          artifacts.replayFailureExactness?.isSome)
      , ("semantic_object_cross_target_progress_dependent_work",
          artifacts.crossTargetProgressDependentWork?.isSome)
      , ("semantic_object_transformation_local_obligations",
          artifacts.transformationLocalObligations?.isSome)
      ]
  | none =>
      [ ("semantic_object_core_invariants", false)
      , ("semantic_object_outstanding_effects", false)
      , ("semantic_object_semantic_handoffs", false)
      , ("semantic_object_authoritative_reads_publication", false)
      , ("semantic_object_materialization_success", false)
      , ("semantic_object_progress_contracts", false)
      , ("semantic_object_effect_contracts", false)
      , ("semantic_object_replay_failure_exactness", false)
      , ("semantic_object_cross_target_progress_dependent_work", false)
      , ("semantic_object_transformation_local_obligations", false)
      ]

/-- Compact enabled semantic-object attachment names carried by the theorem pack. -/
def SemanticObjectArtifacts.attachmentPoints
    (artifacts? : Option SemanticObjectArtifacts) : List String :=
  (SemanticObjectArtifacts.inventory artifacts?).foldr
    (fun entry acc => if entry.2 then entry.1 :: acc else acc) []

/-! ## Proof-Carrying Artifact Metadata -/

/-- Profile metadata carried alongside theorem-pack artifacts. -/
structure ProfileArtifactMetadata where
  executionProfile : ProtocolMachineExecutionProfile
  theoremPackEligibility : List (String × Bool)

/-- Progress metadata carried alongside theorem-pack artifacts.

Each flag records that a premise bundle was supplied, not that anything was
proved from it. -/
structure ProgressArtifactMetadata where
  /-- Semantic-object witnesses (with their mandatory progress contracts) supplied. -/
  parityCriticalOperationsProtected : Bool
  /-- Replay/failure-exactness witness supplied (links the failure taxonomy). -/
  failureTaxonomyLinked : Bool

/-- Envelope/adherence metadata: presence flags for supplied premise bundles. -/
structure EnvelopeArtifactMetadata where
  protocolMachineEnvelopeAdherence : Bool
  protocolMachineEnvelopeAdmission : Bool
  protocolEnvelopeBridge : Bool
  adequacyLinked : Bool
  adherenceLinked : Bool

/-- Canonical proof-carrying artifact metadata surface for one theorem pack. -/
structure ProofCarryingArtifactMetadata where
  profile : ProfileArtifactMetadata
  progress : ProgressArtifactMetadata
  envelope : EnvelopeArtifactMetadata

/-- Build proof-carrying artifact metadata from the current invariant space and
derived artifact presence. -/
def ProofCarryingArtifactMetadata.ofInvariantSpace
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (semanticObjects? : Option SemanticObjectArtifacts)
    (hasProtocolMachineEnvelopeAdherence : Bool)
    (hasProtocolMachineEnvelopeAdmission : Bool)
    (hasProtocolEnvelopeBridge : Bool) :
    ProofCarryingArtifactMetadata :=
  let executionProfile := space.executionProfile
  { profile :=
      { executionProfile := executionProfile
      , theoremPackEligibility := executionProfile.theoremPackEligibility
      }
  , progress :=
      { parityCriticalOperationsProtected := semanticObjects?.isSome
      , failureTaxonomyLinked :=
          semanticObjects?.any (·.replayFailureExactness?.isSome)
      }
  , envelope :=
      { protocolMachineEnvelopeAdherence := hasProtocolMachineEnvelopeAdherence
      , protocolMachineEnvelopeAdmission := hasProtocolMachineEnvelopeAdmission
      , protocolEnvelopeBridge := hasProtocolEnvelopeBridge
      , adequacyLinked :=
          hasProtocolMachineEnvelopeAdherence || hasProtocolMachineEnvelopeAdmission
      , adherenceLinked :=
          hasProtocolMachineEnvelopeAdherence && hasProtocolEnvelopeBridge
      }
  }

end

end Proofs
end Runtime
