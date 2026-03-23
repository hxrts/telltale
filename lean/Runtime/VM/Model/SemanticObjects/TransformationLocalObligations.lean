import Runtime.VM.Model.SemanticObjects.MaterializationSuccess
import Runtime.VM.Model.SemanticObjects.SemanticHandoffTransition

set_option autoImplicit false

/-!
# Runtime.VM.Model.SemanticObjects.TransformationLocalObligations

The Problem.
Structural transformations should not leave in-flight work, proofs, or
publication rights implicit. `TransformationObligation` already records the
affected operations and effects, but the local handling of witnesses,
publications, and late results still needs an explicit bundle shape.

Solution Structure.
This module defines transformation-local obligation bundles over the existing
`TransformationObligation` record. The bundle makes witness/effect/operation/
publication handling explicit for `link`, delegation, detach, and
reconfiguration.
-/

namespace Runtime.VM.Model

inductive TransformationKind where
  | link
  | delegation
  | detach
  | reconfiguration
  deriving Repr, DecidableEq

inductive WitnessDisposition where
  | preserve
  | transport
  | invalidate
  | reissue
  deriving Repr, DecidableEq

inductive EffectDisposition where
  | preserve
  | transport
  | invalidate
  deriving Repr, DecidableEq

inductive OperationDisposition where
  | preserve
  | transport
  | detach
  | reissue
  deriving Repr, DecidableEq

inductive PublicationDisposition where
  | preserve
  | revoke
  | activate
  | reissue
  deriving Repr, DecidableEq

inductive LateResultPolicy where
  | reject
  | transport
  | reissue
  deriving Repr, DecidableEq

structure WitnessLocalObligation where
  proofRef : String
  handleRef : Option String
  disposition : WitnessDisposition
  deriving Repr, DecidableEq

structure EffectLocalObligation where
  effectId : Nat
  disposition : EffectDisposition
  deriving Repr, DecidableEq

structure OperationLocalObligation where
  operationId : String
  disposition : OperationDisposition
  deriving Repr, DecidableEq

structure PublicationLocalObligation where
  operationId : String
  observerClass : PublicationObserverClass
  revokedOwner : Option String
  activatedOwner : Option String
  disposition : PublicationDisposition
  deriving Repr, DecidableEq

structure TransformationLocalObligationBundle where
  kind : TransformationKind
  obligation : TransformationObligation
  witnessObligations : List WitnessLocalObligation
  effectObligations : List EffectLocalObligation
  operationObligations : List OperationLocalObligation
  publicationObligations : List PublicationLocalObligation
  lateResultPolicy : LateResultPolicy
  deriving Repr, DecidableEq

def WitnessLocalObligation.matchesProof
    (entry : WitnessLocalObligation) (proof : MaterializationProof) : Prop :=
  entry.proofRef = proof.proofId

def WitnessLocalObligation.matchesHandle
    (entry : WitnessLocalObligation) (handle : CanonicalHandle) : Prop :=
  entry.handleRef = some handle.handleId ∨ handle.proofRef = some entry.proofRef

def EffectLocalObligation.matchesEffect
    (entry : EffectLocalObligation) (effect : OutstandingEffect) : Prop :=
  entry.effectId = effect.effectId

def OperationLocalObligation.matchesOperation
    (entry : OperationLocalObligation) (operation : OperationInstance) : Prop :=
  entry.operationId = operation.operationId

def PublicationLocalObligation.matchesEvent
    (entry : PublicationLocalObligation) (event : PublicationEvent) : Prop :=
  entry.operationId = event.operationId ∧
  entry.observerClass = event.observerClass

def PublicationLocalObligation.matchesAuthority
    (entry : PublicationLocalObligation) (authority : PublicationAuthority) : Prop :=
  entry.operationId = authority.operationId ∧
  entry.observerClass = authority.observerClass

def TransformationLocalObligationBundle.explicitOperationHandling
    (bundle : TransformationLocalObligationBundle) : Prop :=
  ∀ operationId ∈ bundle.obligation.affectedOperationIds,
    ∃ entry ∈ bundle.operationObligations, entry.operationId = operationId

def TransformationLocalObligationBundle.explicitEffectHandling
    (bundle : TransformationLocalObligationBundle) : Prop :=
  (∀ effectId ∈ bundle.obligation.affectedEffectIds,
      ∃ entry ∈ bundle.effectObligations, entry.effectId = effectId) ∧
  (∀ effectId ∈ bundle.obligation.transportedEffectIds,
      ∃ entry ∈ bundle.effectObligations,
        entry.effectId = effectId ∧ entry.disposition = .transport) ∧
  (∀ effectId ∈ bundle.obligation.invalidatedEffectIds,
      ∃ entry ∈ bundle.effectObligations,
        entry.effectId = effectId ∧ entry.disposition = .invalidate)

def TransformationLocalObligationBundle.explicitWitnessHandling
    (bundle : TransformationLocalObligationBundle)
    (objects : ProtocolMachineSemanticObjects) : Prop :=
  ∀ event ∈ objects.publicationEvents,
    event.operationId ∈ bundle.obligation.affectedOperationIds →
    ∀ proofRef, event.proofRef = some proofRef →
      ∃ entry ∈ bundle.witnessObligations, entry.proofRef = proofRef

def TransformationLocalObligationBundle.explicitPublicationHandling
    (bundle : TransformationLocalObligationBundle)
    (objects : ProtocolMachineSemanticObjects) : Prop :=
  ∀ event ∈ objects.publicationEvents,
    event.operationId ∈ bundle.obligation.affectedOperationIds →
      ∃ entry ∈ bundle.publicationObligations,
        entry.matchesEvent event

def TransformationLocalObligationBundle.explicitLateResultHandling
    (bundle : TransformationLocalObligationBundle) : Prop :=
  bundle.lateResultPolicy = .reject ∨
  bundle.lateResultPolicy = .transport ∨
  bundle.lateResultPolicy = .reissue

def TransformationLocalObligationBundle.explicitLocalBundle
    (bundle : TransformationLocalObligationBundle)
    (objects : ProtocolMachineSemanticObjects) : Prop :=
  bundle.explicitOperationHandling ∧
  bundle.explicitEffectHandling ∧
  bundle.explicitWitnessHandling objects ∧
  bundle.explicitPublicationHandling objects ∧
  bundle.explicitLateResultHandling

def TransformationLocalObligationBundle.linkAdmissible
    (bundle : TransformationLocalObligationBundle) : Prop :=
  match bundle with
  | { kind := .link, effectObligations, operationObligations, witnessObligations,
      publicationObligations, lateResultPolicy, .. } =>
      (∀ entry ∈ effectObligations,
        entry.disposition = .preserve ∨ entry.disposition = .transport) ∧
      (∀ entry ∈ operationObligations,
        entry.disposition = .preserve ∨ entry.disposition = .transport) ∧
      (∀ entry ∈ witnessObligations,
        entry.disposition = .preserve ∨ entry.disposition = .transport) ∧
      (∀ entry ∈ publicationObligations,
        entry.disposition = .preserve ∨ entry.disposition = .activate) ∧
      lateResultPolicy ≠ .reissue
  | _ => True

def TransformationLocalObligationBundle.delegationAdmissible
    (bundle : TransformationLocalObligationBundle) : Prop :=
  match bundle with
  | { kind := .delegation, effectObligations, operationObligations, witnessObligations,
      publicationObligations, .. } =>
      (∀ entry ∈ effectObligations,
        entry.disposition = .transport ∨ entry.disposition = .invalidate) ∧
      (∀ entry ∈ operationObligations, entry.disposition = .transport) ∧
      (∀ entry ∈ witnessObligations,
        entry.disposition = .transport ∨ entry.disposition = .reissue) ∧
      (∃ entry ∈ publicationObligations, entry.disposition = .revoke) ∧
      (∃ entry ∈ publicationObligations, entry.disposition = .activate)
  | _ => True

def TransformationLocalObligationBundle.detachAdmissible
    (bundle : TransformationLocalObligationBundle) : Prop :=
  match bundle with
  | { kind := .detach, effectObligations, operationObligations, witnessObligations,
      publicationObligations, lateResultPolicy, .. } =>
      (∀ entry ∈ effectObligations, entry.disposition = .invalidate) ∧
      (∀ entry ∈ operationObligations,
        entry.disposition = .detach ∨ entry.disposition = .reissue) ∧
      (∀ entry ∈ witnessObligations,
        entry.disposition = .invalidate ∨ entry.disposition = .reissue) ∧
      (∀ entry ∈ publicationObligations,
        entry.disposition = .revoke ∨ entry.disposition = .reissue) ∧
      lateResultPolicy ≠ .transport
  | _ => True

def TransformationLocalObligationBundle.reconfigurationAdmissible
    (bundle : TransformationLocalObligationBundle) : Prop :=
  match bundle with
  | { kind := .reconfiguration, effectObligations, operationObligations,
      witnessObligations, publicationObligations, .. } =>
      (∀ entry ∈ effectObligations,
        entry.disposition = .preserve ∨
        entry.disposition = .transport ∨
        entry.disposition = .invalidate) ∧
      (∀ entry ∈ operationObligations,
        entry.disposition = .preserve ∨
        entry.disposition = .transport ∨
        entry.disposition = .detach ∨
        entry.disposition = .reissue) ∧
      (∀ entry ∈ witnessObligations,
        entry.disposition = .preserve ∨
        entry.disposition = .transport ∨
        entry.disposition = .invalidate ∨
        entry.disposition = .reissue) ∧
      (∀ entry ∈ publicationObligations,
        entry.disposition = .preserve ∨
        entry.disposition = .revoke ∨
        entry.disposition = .activate ∨
        entry.disposition = .reissue)
  | _ => True

end Runtime.VM.Model
