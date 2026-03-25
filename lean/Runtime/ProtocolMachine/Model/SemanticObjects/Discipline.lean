import Runtime.ProtocolMachine.Model.SemanticObjects.Core

set_option autoImplicit false

/-!
# Runtime.ProtocolMachine.Model.SemanticObjects.Discipline

Semantic-object predicate surface for the protocol-machine model.

This file intentionally contains semantic predicates only. Proof theorems over
these predicates live under `Runtime/Proofs/ProtocolMachine/`.
-/

namespace Runtime.ProtocolMachine.Model

def OperationPhase.requiresActiveOwner : OperationPhase → Prop
  | .pending | .blocked => True
  | .succeeded | .failed | .cancelled | .timedOut | .handedOff => False

def OperationInstance.hasExplicitIdentity (operation : OperationInstance) : Prop :=
  operation.operationId ≠ ""

def OperationInstance.hasMinimumTrackedFields (operation : OperationInstance) : Prop :=
  operation.hasExplicitIdentity ∧ operation.kind ≠ ""

def OutstandingEffect.hasExplicitIdentity (effect : OutstandingEffect) : Prop :=
  effect.effectInterface.isSome ∧ effect.effectOperation.isSome

def OutstandingEffect.hasInvalidationSurface (effect : OutstandingEffect) : Prop :=
  effect.invalidationToken ≠ ""

def OutstandingEffect.hasMinimumTrackedFields (effect : OutstandingEffect) : Prop :=
  effect.hasExplicitIdentity ∧ effect.hasInvalidationSurface ∧ effect.handlerIdentity ≠ ""

def SemanticHandoff.hasExplicitOwnerTransition (handoff : SemanticHandoff) : Prop :=
  handoff.revokedOwnerId ≠ "" ∧
  handoff.activatedOwnerId ≠ "" ∧
  handoff.revokedOwnerId ≠ handoff.activatedOwnerId

def AuthoritativeRead.hasAuthorityContext (read : AuthoritativeRead) : Prop :=
  read.ownerId.isSome ∨ read.witnessId.isSome ∨ read.generation.isSome

def ObservedRead.isNonAuthoritative (read : ObservedRead) : Prop :=
  read.effectInterface.isSome ∧
  read.effectOperation.isSome ∧
  read.handlerIdentity ≠ ""

def ProtocolMachineSemanticObjects.explicitOperationIdentity
    (objects : ProtocolMachineSemanticObjects) : Prop :=
  ∀ operation ∈ objects.operationInstances, operation.hasMinimumTrackedFields

def ProtocolMachineSemanticObjects.explicitOutstandingEffectIdentity
    (objects : ProtocolMachineSemanticObjects) : Prop :=
  ∀ effect ∈ objects.outstandingEffects, effect.hasMinimumTrackedFields

def ProtocolMachineSemanticObjects.uniqueOperationIds
    (objects : ProtocolMachineSemanticObjects) : Prop :=
  (objects.operationInstances.map OperationInstance.operationId).Nodup

def ProtocolMachineSemanticObjects.uniqueOutstandingEffectIds
    (objects : ProtocolMachineSemanticObjects) : Prop :=
  (objects.outstandingEffects.map OutstandingEffect.effectId).Nodup

def ProtocolMachineSemanticObjects.uniqueSemanticOwner
    (objects : ProtocolMachineSemanticObjects) : Prop :=
  ∀ operation₁ ∈ objects.operationInstances,
    ∀ operation₂ ∈ objects.operationInstances,
      operation₁.operationId = operation₂.operationId →
      operation₁.phase.requiresActiveOwner →
      operation₂.phase.requiresActiveOwner →
      operation₁.ownerId = operation₂.ownerId

def ProtocolMachineSemanticObjects.explicitHandoffs
    (objects : ProtocolMachineSemanticObjects) : Prop :=
  ∀ handoff ∈ objects.semanticHandoffs, handoff.hasExplicitOwnerTransition

def ProtocolMachineSemanticObjects.nonAuthoritativeObservedReads
    (objects : ProtocolMachineSemanticObjects) : Prop :=
  ∀ read ∈ objects.observedReads, read.isNonAuthoritative

def ProtocolMachineSemanticObjects.disjointReadIdentities
    (objects : ProtocolMachineSemanticObjects) : Prop :=
  ∀ readId,
    readId ∈ objects.authoritativeReads.map AuthoritativeRead.readId →
    readId ∈ objects.observedReads.map ObservedRead.readId →
    False

def ProtocolMachineSemanticObjects.coreSemanticObjectInvariants
    (objects : ProtocolMachineSemanticObjects) : Prop :=
  objects.explicitOperationIdentity ∧
  objects.explicitOutstandingEffectIdentity ∧
  objects.uniqueOperationIds ∧
  objects.uniqueOutstandingEffectIds ∧
  objects.uniqueSemanticOwner ∧
  objects.explicitHandoffs ∧
  objects.nonAuthoritativeObservedReads ∧
  objects.disjointReadIdentities

end Runtime.ProtocolMachine.Model
