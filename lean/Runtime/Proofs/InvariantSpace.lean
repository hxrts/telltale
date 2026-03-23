import Runtime.Proofs.ProgressApi
import Runtime.VM.Model.OutputCondition
import Runtime.VM.Model.SemanticObjects.AuthoritativeReadsPublication
import Runtime.VM.Model.SemanticObjects.ProgressContracts
import Runtime.VM.Model.SemanticObjects.TransformationLocalObligations

set_option autoImplicit false

/-! # Runtime.Proofs.InvariantSpace

Proof-carrying invariant-space bundle for VM theorem derivation.
-/

namespace Runtime
namespace Proofs

universe u v

section

variable {ν : Type u} [VerificationModel ν]

/-- Classical transport witness expected by transported theorem adapters. -/
structure ClassicalTransportWitness (State : Type v) where
  coherent : State → Prop
  harmony : Prop
  finiteState : Prop

/-- Output-condition witness expected by theorem-pack adapters. -/
structure OutputConditionWitness where
  verify : OutputConditionClaim → Bool
  accepted : OutputConditionClaim → Prop := fun _ => True
  sound : ∀ claim, verify claim = true → accepted claim

/-- Attachment surface for core semantic-object invariants. -/
structure CoreSemanticObjectWitness where
  objects : Runtime.VM.Model.ProtocolMachineSemanticObjects
  invariants : objects.coreSemanticObjectInvariants

/-- Attachment surface for outstanding-effect invalidation / late-result proofs. -/
structure OutstandingEffectSemanticWitness where
  effect : Runtime.VM.Model.OutstandingEffect
  ownerId : Option String
  tick : Nat
  rejected : effect.resultIsLate ownerId tick
  rejectedPreventsCommit : ¬ effect.admissibleForCommit ownerId tick

/-- Attachment surface for semantic handoff proofs. -/
structure SemanticHandoffWitness where
  operation : Runtime.VM.Model.OperationInstance
  handoff : Runtime.VM.Model.SemanticHandoff
  obligation : Runtime.VM.Model.TransformationObligation
  handoffCommitted : handoff.isCommitted
  obligationCommitted : obligation.isCommitted
  eligible : operation.handoffEligible
  affected : operation.operationId ∈ obligation.affectedOperationIds
  activatedOwner :
    (operation.applyHandoff handoff obligation).ownerId = some handoff.activatedOwnerId

/-- Attachment surface for authoritative-read / publication discipline. -/
structure AuthoritativeReadPublicationWitness where
  objects : Runtime.VM.Model.ProtocolMachineSemanticObjects
  ctx : Runtime.VM.Model.AuthoritativeCommitmentContext
  observedCannotAuthorTruth : objects.observedStateCannotAuthorTruth ctx
  canonicalPublicationPathUnique : objects.canonicalPublicationPathUnique
  publicationObserverClassDisciplined : objects.publicationObserverClassDisciplined

/-- Attachment surface for proof-backed materialization / success. -/
structure MaterializationSuccessWitness where
  objects : Runtime.VM.Model.ProtocolMachineSemanticObjects
  ctx : Runtime.VM.Model.SuccessProofContext
  successProofBacked : objects.successProofBacked ctx
  observedMaterializationInsufficient : objects.observedMaterializationInsufficient ctx

/-- Attachment surface for progress-contract / escalation discipline. -/
structure ProgressContractWitness where
  objects : Runtime.VM.Model.ProtocolMachineSemanticObjects
  contract : Runtime.VM.Model.ProgressContract
  trackedLiveness : objects.ownerInternalLivenessContract contract

/-- Attachment surface for transformation-local obligation bundles. -/
structure TransformationLocalObligationWitness where
  objects : Runtime.VM.Model.ProtocolMachineSemanticObjects
  bundle : Runtime.VM.Model.TransformationLocalObligationBundle
  explicitLocalBundle : bundle.explicitLocalBundle objects

/-- Canonical theorem-pack attachment points for semantic-object proof families. -/
structure SemanticObjectWitnessBundle where
  coreInvariants? : Option CoreSemanticObjectWitness := none
  outstandingEffects? : Option OutstandingEffectSemanticWitness := none
  semanticHandoffs? : Option SemanticHandoffWitness := none
  authoritativeReadsPublication? : Option AuthoritativeReadPublicationWitness := none
  materializationSuccess? : Option MaterializationSuccessWitness := none
  progressContracts? : Option ProgressContractWitness := none
  transformationLocalObligations? : Option TransformationLocalObligationWitness := none

/-- Core VM invariant space:
- optional liveness bundle (enables termination/progress theorems when provided),
- optional classical transport witness for theorem transport,
- optional output-condition witness for predicate-gated output semantics,
- optional semantic-object witness bundle for protocol-machine proof families. -/
structure VMInvariantSpace (store₀ : SessionStore ν) (State : Type v) where
  liveness? : Option (VMLivenessBundle store₀) := none
  classicalWitness? : Option (ClassicalTransportWitness State) := none
  outputConditionWitness? : Option OutputConditionWitness := none
  semanticObjectWitnesses? : Option SemanticObjectWitnessBundle := none

/-- Attach a liveness bundle to an invariant space. -/
def VMInvariantSpace.withLiveness
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpace store₀ State)
    (bundle : VMLivenessBundle store₀) : VMInvariantSpace store₀ State :=
  { space with liveness? := some bundle }

/-- True iff an invariant space carries a liveness bundle. -/
def VMInvariantSpace.hasLiveness
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpace store₀ State) : Bool :=
  space.liveness?.isSome

/-- Attach a classical witness to an invariant space. -/
def VMInvariantSpace.withClassicalWitness
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpace store₀ State)
    (w : ClassicalTransportWitness State) : VMInvariantSpace store₀ State :=
  { space with classicalWitness? := some w }

/-- True iff an invariant space carries a classical transport witness. -/
def VMInvariantSpace.hasClassicalWitness
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpace store₀ State) : Bool :=
  space.classicalWitness?.isSome

/-- Attach an output-condition witness to an invariant space. -/
def VMInvariantSpace.withOutputConditionWitness
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpace store₀ State)
    (w : OutputConditionWitness) : VMInvariantSpace store₀ State :=
  { space with outputConditionWitness? := some w }

/-- True iff an invariant space carries output-condition witness evidence. -/
def VMInvariantSpace.hasOutputConditionWitness
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpace store₀ State) : Bool :=
  space.outputConditionWitness?.isSome

/-- Attach semantic-object proof-family witnesses to an invariant space. -/
def VMInvariantSpace.withSemanticObjectWitnesses
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpace store₀ State)
    (w : SemanticObjectWitnessBundle) : VMInvariantSpace store₀ State :=
  { space with semanticObjectWitnesses? := some w }

/-- True iff an invariant space carries semantic-object proof-family evidence. -/
def VMInvariantSpace.hasSemanticObjectWitnesses
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpace store₀ State) : Bool :=
  space.semanticObjectWitnesses?.isSome

end

end Proofs
end Runtime
