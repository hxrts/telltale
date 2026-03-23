import Runtime.Proofs.TheoremPack.API

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
    VMInvariantSpaceWithProfiles (ν := ν) store₀ State :=
  VMInvariantSpaceWithProfiles.mk
    (Adapters.VMInvariantSpaceWithDistributed.mk
      (VMInvariantSpace.mk none none none none)
      {})
    {}

def emptySemanticObjects : Runtime.VM.Model.ProtocolMachineSemanticObjects :=
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
      simp [Runtime.VM.Model.ProtocolMachineSemanticObjects.coreSemanticObjectInvariants,
        Runtime.VM.Model.ProtocolMachineSemanticObjects.explicitOperationIdentity,
        Runtime.VM.Model.ProtocolMachineSemanticObjects.explicitOutstandingEffectIdentity,
        Runtime.VM.Model.ProtocolMachineSemanticObjects.uniqueOperationIds,
        Runtime.VM.Model.ProtocolMachineSemanticObjects.uniqueOutstandingEffectIds,
        Runtime.VM.Model.ProtocolMachineSemanticObjects.uniqueSemanticOwner,
        Runtime.VM.Model.ProtocolMachineSemanticObjects.explicitHandoffs,
        Runtime.VM.Model.ProtocolMachineSemanticObjects.nonAuthoritativeObservedReads,
        Runtime.VM.Model.ProtocolMachineSemanticObjects.disjointReadIdentities,
        emptySemanticObjects]
  }

def semanticWitnessBundle : SemanticObjectWitnessBundle :=
  { coreInvariants? := some coreSemanticObjectWitness }

def semanticComposedSpace :
    VMInvariantSpaceWithProfiles (ν := ν) store₀ State :=
  Runtime.Proofs.TheoremPackAPI.withSemanticObjectWitnesses
    (space := baseComposedSpace (ν := ν) (store₀ := store₀) (State := State))
    semanticWitnessBundle

def composedSpace (bundle : VMLivenessBundle store₀) (ow : OutputConditionWitness) :
    VMInvariantSpaceWithProfiles (ν := ν) store₀ State :=
  Runtime.Proofs.TheoremPackAPI.composeProofSpaces
    (space := baseComposedSpace (ν := ν) (store₀ := store₀) (State := State))
    (liveness? := some bundle)
    (distributed? := some ({} : Adapters.DistributedProfiles))
    (classical? := some ({} : Adapters.ClassicalProfiles State))
    (output? := some ow)

/-- Composed spaces can be turned into theorem packs through the API facade. -/
example (bundle : VMLivenessBundle store₀) (ow : OutputConditionWitness) :
    let space := composedSpace (ν := ν) (store₀ := store₀) (State := State) bundle ow
    True := by
  intro
  trivial

/-- Minimal deterministic capability inventories can be extracted from composed packs. -/
example (bundle : VMLivenessBundle store₀) (ow : OutputConditionWitness) :
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
  simp [semanticComposedSpace, Runtime.Proofs.TheoremPackAPI.withSemanticObjectWitnesses,
    VMInvariantSpace.withSemanticObjectWitnesses, Runtime.Proofs.TheoremPackAPI.mk,
    Runtime.Proofs.buildVMTheoremPack,
    Runtime.Proofs.TheoremPackAPI.semanticObjectInventory, Runtime.Proofs.semanticObjectInventory,
    Runtime.Proofs.SemanticObjectArtifacts.inventory,
    Runtime.Proofs.SemanticObjectArtifacts.ofWitnessBundle,
    semanticWitnessBundle, coreSemanticObjectWitness, baseComposedSpace]

end

end Examples
end Proofs
end Runtime
