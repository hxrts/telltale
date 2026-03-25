import Runtime.Proofs.ProgressApi
import Runtime.Proofs.ProtocolMachine.SemanticObjects.ProgressContracts
import Runtime.Adequacy.EnvelopeCore.FailureTaxonomy.Core
import Runtime.ProtocolMachine.Model.Effects
import Runtime.ProtocolMachine.Model.OutputCondition
import Runtime.ProtocolMachine.Model.SemanticObjects.AuthoritativeReadsPublication
import Runtime.ProtocolMachine.Model.SemanticObjects.CrossTargetProgressDependentWork
import Runtime.ProtocolMachine.Model.SemanticObjects.ProgressContracts
import Runtime.ProtocolMachine.Model.SemanticObjects.ReplayFailureExactness
import Runtime.ProtocolMachine.Model.SemanticObjects.TransformationLocalObligations

set_option autoImplicit false

/-! # Runtime.Proofs.InvariantSpace

Proof-carrying invariant-space bundle for protocol machine theorem derivation.
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
  objects : Runtime.ProtocolMachine.Model.ProtocolMachineSemanticObjects
  invariants : objects.coreSemanticObjectInvariants

/-- Attachment surface for outstanding-effect invalidation / late-result proofs. -/
structure OutstandingEffectSemanticWitness where
  effect : Runtime.ProtocolMachine.Model.OutstandingEffect
  ownerId : Option String
  tick : Nat
  rejected : effect.resultIsLate ownerId tick
  rejectedPreventsCommit : ¬ effect.admissibleForCommit ownerId tick

/-- Attachment surface for semantic handoff proofs. -/
structure SemanticHandoffWitness where
  operation : Runtime.ProtocolMachine.Model.OperationInstance
  handoff : Runtime.ProtocolMachine.Model.SemanticHandoff
  obligation : Runtime.ProtocolMachine.Model.TransformationObligation
  handoffCommitted : handoff.isCommitted
  obligationCommitted : obligation.isCommitted
  eligible : operation.handoffEligible
  affected : operation.operationId ∈ obligation.affectedOperationIds
  activatedOwner :
    (operation.applyHandoff handoff obligation).ownerId = some handoff.activatedOwnerId

/-- Attachment surface for authoritative-read / publication discipline. -/
structure AuthoritativeReadPublicationWitness where
  objects : Runtime.ProtocolMachine.Model.ProtocolMachineSemanticObjects
  ctx : Runtime.ProtocolMachine.Model.AuthoritativeCommitmentContext
  read : Runtime.ProtocolMachine.Model.AuthoritativeRead
  readMember : read ∈ objects.authoritativeReads
  readSatisfiesContext : read.satisfiesCommitmentContext ctx
  commitmentPermitted : objects.authoritativeCommitPermitted ctx
  observedCannotAuthorTruth : objects.observedStateCannotAuthorTruth ctx
  canonicalPublicationPathUnique : objects.canonicalPublicationPathUnique
  canonicalPublicationSurfaceExclusive : objects.canonicalPublicationSurfaceExclusive
  publicationObserverClassDisciplined : objects.publicationObserverClassDisciplined

/-- Attachment surface for proof-backed materialization / success. -/
structure MaterializationSuccessWitness where
  objects : Runtime.ProtocolMachine.Model.ProtocolMachineSemanticObjects
  ctx : Runtime.ProtocolMachine.Model.SuccessProofContext
  operation : Runtime.ProtocolMachine.Model.OperationInstance
  proof : Runtime.ProtocolMachine.Model.MaterializationProof
  handle : Runtime.ProtocolMachine.Model.CanonicalHandle
  operationMember : operation ∈ objects.operationInstances
  proofMember : proof ∈ objects.materializationProofs
  handleMember : handle ∈ objects.canonicalHandles
  operationRequiresSuccessProof : operation.requiresSuccessProofFor ctx
  proofAdequate : proof.adequateForSuccessContext ctx
  handleAdequate : handle.adequateForSuccessContext ctx proof
  successProofBacked : objects.successProofBacked ctx
  authoritativeMaterializationAdequate : objects.authoritativeMaterializationAdequate ctx
  canonicalHandleDomainUnique : objects.canonicalHandleDomainUnique ctx
  observedMaterializationInsufficient : objects.observedMaterializationInsufficient ctx
  weakerPublicationInsufficient : objects.weakerPublicationInsufficient ctx

/-- Attachment surface for progress-contract / escalation discipline. -/
structure ProgressContractWitness where
  objects : Runtime.ProtocolMachine.Model.ProtocolMachineSemanticObjects
  operation : Runtime.ProtocolMachine.Model.OperationInstance
  contract : Runtime.ProtocolMachine.Model.ProgressContract
  operationMember : operation ∈ objects.operationInstances
  contractMember : contract ∈ objects.progressContracts
  parityCritical : operation.isParityCritical
  tracksOperation : contract.tracksOperation operation
  explicitContractPresent : objects.progressContractForOperation operation
  trackedLiveness : objects.ownerInternalLivenessContract contract
  schedulingBoundCompatible : contract.schedulingBoundCompatible
  failureEvidence :
    contract.failureEvidence?.isSome = true ∨ contract.failureEvidence?.isSome = false

/-- Attachment surface for effect admissibility / reentrancy contracts. -/
structure EffectContractWitness where
  metadata : Runtime.ProtocolMachine.Model.EffectInterfaceMetadata
  activeDomain : Runtime.ProtocolMachine.Model.EffectResponsibilityDomain
  incomingDomain : Runtime.ProtocolMachine.Model.EffectResponsibilityDomain
  architecturallyLegal : metadata.architecturallyLegal
  reentrancyPolicySound :
    metadata.reentrancyAdmissible activeDomain incomingDomain ↔
      metadata.reentrancyPolicy.admits activeDomain incomingDomain

/-- Attachment surface for replay stability / failure exactness discipline. -/
structure ReplayFailureExactnessWitness where
  objects : Runtime.ProtocolMachine.Model.ProtocolMachineSemanticObjects
  ctx : Runtime.ProtocolMachine.Model.ReplayFailureContext
  operation : Runtime.ProtocolMachine.Model.OperationInstance
  effect : Runtime.ProtocolMachine.Model.OutstandingEffect
  contract : Runtime.ProtocolMachine.Model.ProgressContract
  operationMember : operation ∈ objects.operationInstances
  effectMember : effect ∈ objects.outstandingEffects
  contractMember : contract ∈ objects.progressContracts
  contractMatchesContext : contract.matchesReplayFailureContext ctx
  replayStableOperationIdentity : objects.replayStableOperationIdentity
  terminalTruthStableUnderReplay : objects.terminalTruthStableUnderReplay
  staleLateResultRejected : objects.staleLateResultRejected
  failureAuditAligned : objects.failureAuditAligned ctx
  replayFailureConformanceAligned : objects.replayFailureConformanceAligned ctx

/-- Attachment surface for cross-target progress / dependent-work composition. -/
structure CrossTargetProgressDependentWorkWitness where
  objects : Runtime.ProtocolMachine.Model.ProtocolMachineSemanticObjects
  left : Runtime.ProtocolMachine.Model.RealizedProgressView
  right : Runtime.ProtocolMachine.Model.RealizedProgressView
  parent : Runtime.ProtocolMachine.Model.OperationInstance
  contract : Runtime.ProtocolMachine.Model.ProgressContract
  parentMember : parent ∈ objects.operationInstances
  tracksOperation : contract.tracksOperation parent
  crossTargetProgressPreserved : objects.crossTargetProgressPreserved left right
  dependentWorkFullyResolved : objects.dependentWorkFullyResolved parent
  parentTerminalityComposedFromDependents :
    objects.parentTerminalityComposedFromDependents parent contract

/-- Attachment surface for transformation-local obligation bundles. -/
structure TransformationLocalObligationWitness where
  objects : Runtime.ProtocolMachine.Model.ProtocolMachineSemanticObjects
  bundle : Runtime.ProtocolMachine.Model.TransformationLocalObligationBundle
  explicitLocalBundle : bundle.explicitLocalBundle objects

/-- Canonical theorem-pack attachment points for semantic-object proof families. -/
structure SemanticObjectWitnessBundle where
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

/-- Core protocol machine invariant space:
- optional liveness bundle (enables termination/progress theorems when provided),
- optional classical transport witness for theorem transport,
- optional output-condition witness for predicate-gated output semantics,
- optional semantic-object witness bundle for protocol-machine proof families. -/
structure ProtocolMachineInvariantSpace (store₀ : SessionStore ν) (State : Type v) where
  liveness? : Option (ProtocolMachineLivenessBundle store₀) := none
  classicalWitness? : Option (ClassicalTransportWitness State) := none
  outputConditionWitness? : Option OutputConditionWitness := none
  semanticObjectWitnesses? : Option SemanticObjectWitnessBundle := none

/-- Attach a liveness bundle to an invariant space. -/
def ProtocolMachineInvariantSpace.withLiveness
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpace store₀ State)
    (bundle : ProtocolMachineLivenessBundle store₀) : ProtocolMachineInvariantSpace store₀ State :=
  { space with liveness? := some bundle }

/-- True iff an invariant space carries a liveness bundle. -/
def ProtocolMachineInvariantSpace.hasLiveness
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpace store₀ State) : Bool :=
  space.liveness?.isSome

/-- Attach a classical witness to an invariant space. -/
def ProtocolMachineInvariantSpace.withClassicalWitness
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpace store₀ State)
    (w : ClassicalTransportWitness State) : ProtocolMachineInvariantSpace store₀ State :=
  { space with classicalWitness? := some w }

/-- True iff an invariant space carries a classical transport witness. -/
def ProtocolMachineInvariantSpace.hasClassicalWitness
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpace store₀ State) : Bool :=
  space.classicalWitness?.isSome

/-- Attach an output-condition witness to an invariant space. -/
def ProtocolMachineInvariantSpace.withOutputConditionWitness
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpace store₀ State)
    (w : OutputConditionWitness) : ProtocolMachineInvariantSpace store₀ State :=
  { space with outputConditionWitness? := some w }

/-- True iff an invariant space carries output-condition witness evidence. -/
def ProtocolMachineInvariantSpace.hasOutputConditionWitness
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpace store₀ State) : Bool :=
  space.outputConditionWitness?.isSome

/-- Attach semantic-object proof-family witnesses to an invariant space. -/
def ProtocolMachineInvariantSpace.withSemanticObjectWitnesses
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpace store₀ State)
    (w : SemanticObjectWitnessBundle) : ProtocolMachineInvariantSpace store₀ State :=
  { space with semanticObjectWitnesses? := some w }

/-- True iff an invariant space carries semantic-object proof-family evidence. -/
def ProtocolMachineInvariantSpace.hasSemanticObjectWitnesses
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpace store₀ State) : Bool :=
  space.semanticObjectWitnesses?.isSome

end

end Proofs
end Runtime
