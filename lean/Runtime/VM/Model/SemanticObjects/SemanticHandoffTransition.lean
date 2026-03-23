import Runtime.VM.Model.SemanticObjects.OutstandingEffects

set_option autoImplicit false

/-!
# Runtime.VM.Model.SemanticObjects.SemanticHandoffTransition

The Problem.
`SemanticHandoff` is more than a log object: it is the runtime-facing record of
owner revocation, owner activation, effect transfer, dependent-work transfer,
and publication-right transfer.

Solution Structure.
This module defines the implementation-level transition vocabulary around
`SemanticHandoff` and `TransformationObligation`. The companion lemma module
proves one-owner-before/after and publication-revocation facts over this model.
-/

namespace Runtime.VM.Model

/-! ## Publication Authority -/

structure PublicationAuthority where
  operationId : String
  ownerId : Option String
  observerClass : PublicationObserverClass
  deriving Repr, DecidableEq

def PublicationAuthority.permits
    (authority : PublicationAuthority) (event : PublicationEvent) : Prop :=
  event.operationId = authority.operationId ∧
  event.ownerId = authority.ownerId ∧
  event.observerClass = authority.observerClass ∧
  event.status = .published

/-! ## Handoff / Obligation Selectors -/

def SemanticHandoff.isCommitted (handoff : SemanticHandoff) : Prop :=
  handoff.status = .committed

def TransformationObligation.isCommitted (obligation : TransformationObligation) : Prop :=
  obligation.status = .committed

def TransformationObligation.affectsOperation
    (obligation : TransformationObligation) (operation : OperationInstance) : Prop :=
  operation.operationId ∈ obligation.affectedOperationIds

def TransformationObligation.affectsEffect
    (obligation : TransformationObligation) (effect : OutstandingEffect) : Prop :=
  effect.effectId ∈ obligation.affectedEffectIds

def TransformationObligation.transportsEffect
    (obligation : TransformationObligation) (effect : OutstandingEffect) : Prop :=
  effect.effectId ∈ obligation.transportedEffectIds

def TransformationObligation.invalidatesEffect
    (obligation : TransformationObligation) (effect : OutstandingEffect) : Prop :=
  effect.effectId ∈ obligation.invalidatedEffectIds

def TransformationObligation.affectsPublication
    (obligation : TransformationObligation) (event : PublicationEvent) : Prop :=
  event.operationId ∈ obligation.affectedOperationIds

def OperationInstance.handoffEligible (operation : OperationInstance) : Prop :=
  operation.phase = .pending ∨ operation.phase = .blocked

def OperationInstance.dependentWorkTransferredBy
    (operation : OperationInstance)
    (obligation : TransformationObligation) : List String :=
  if operation.operationId ∈ obligation.affectedOperationIds then
    operation.dependentOperationIds
  else
    []

/-! ## Transition Realization -/

def OperationInstance.applyHandoff
    (operation : OperationInstance)
    (handoff : SemanticHandoff)
    (obligation : TransformationObligation) : OperationInstance :=
  if hCommit : handoff.status = .committed ∧ obligation.status = .committed ∧
      operation.operationId ∈ obligation.affectedOperationIds then
    { operation with
      ownerId := some handoff.activatedOwnerId
      phase := if operation.phase = .pending ∨ operation.phase = .blocked then .handedOff else operation.phase
    }
  else
    operation

def OutstandingEffect.applyHandoff
    (effect : OutstandingEffect)
    (handoff : SemanticHandoff)
    (obligation : TransformationObligation) : OutstandingEffect :=
  if hCommit : handoff.status = .committed ∧ obligation.status = .committed then
    if hInvalidate : effect.effectId ∈ obligation.invalidatedEffectIds then
      { (effect.applyEvent (.invalidated handoff.tick handoff.reason)) with
        ownerId := some handoff.activatedOwnerId
      }
    else if hTransport : effect.effectId ∈ obligation.transportedEffectIds then
      { effect with ownerId := some handoff.activatedOwnerId }
    else
      effect
  else
    effect

def PublicationEvent.applyHandoff
    (event : PublicationEvent)
    (handoff : SemanticHandoff)
    (obligation : TransformationObligation) : PublicationEvent :=
  if hCommit : handoff.status = .committed ∧ obligation.status = .committed ∧
      event.operationId ∈ obligation.affectedOperationIds then
    if event.ownerId = some handoff.revokedOwnerId then
      { event with
        status := .rejected
        reason := some "revoked_by_handoff"
      }
    else
      event
  else
    event

def PublicationAuthority.transferredBy
    (authority : PublicationAuthority)
    (handoff : SemanticHandoff)
    (obligation : TransformationObligation) : PublicationAuthority :=
  if hCommit : handoff.status = .committed ∧ obligation.status = .committed ∧
      authority.operationId ∈ obligation.affectedOperationIds then
    if authority.ownerId = some handoff.revokedOwnerId then
      { authority with ownerId := some handoff.activatedOwnerId }
    else
      authority
  else
    authority

end Runtime.VM.Model
