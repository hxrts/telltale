import Runtime.Proofs.Capabilities
import Runtime.ProtocolMachine.Model.SemanticObjects.MaterializationSuccess
import Runtime.ProtocolMachine.Model.SemanticObjects.SemanticHandoffTransition

set_option autoImplicit false

/-!
# Runtime.Proofs.CapabilityModel

The Problem.
Rust now exposes first-class capability lifecycle, finalization, semantic
handoff, and runtime-upgrade artifacts. Lean needs a matching vocabulary so
these objects are not merely documentation-level structure.

Solution Structure.
Define lightweight Lean mirrors for the claim-critical capability/finalization
surface, derive canonical finalization stages from explicit artifacts, and tie
the result back to existing materialization and semantic-handoff model
predicates.
-/

namespace Runtime
namespace Proofs

/-- Lean-side read classification for one finalization path. -/
inductive FinalizationReadClass where
  | none
  | observedOnly
  | authoritativeOnly
  | mixed
  deriving DecidableEq, Repr

/-- Lean-side canonicalization stage for one finalization path. -/
inductive FinalizationStage where
  | observed
  | authoritative
  | materialized
  | canonical
  | invalidated
  | rejected
  deriving DecidableEq, Repr

/-- Phase for a transition/runtime-upgrade artifact. -/
inductive TransitionArtifactPhase where
  | staged
  | admitted
  | committedCutover
  | rolledBack
  | failed
  deriving DecidableEq, Repr

/-- Pending-effect treatment required by a runtime upgrade. -/
inductive PendingEffectTreatment where
  | preservePending
  | invalidateBlocked
  deriving DecidableEq, Repr

/-- Canonical publication continuity contract for a runtime upgrade. -/
inductive CanonicalPublicationContinuity where
  | preserveCanonicalTruth
  | reissueCanonicalTruth
  deriving DecidableEq, Repr

/-- Execution-profile constraint for a runtime upgrade. -/
inductive RuntimeUpgradeExecutionConstraint where
  | preserveBundleProfile
  | mixedDeterminismAllowed
  deriving DecidableEq, Repr

/-- Canonical finalization path mirrored from the Rust semantic-object surface. -/
structure FinalizationPath where
  operationId : String
  session : Option Nat
  ownerId : Option String
  readClass : FinalizationReadClass
  stage : FinalizationStage
  observedReadIds : List String
  authoritativeReadIds : List String
  proofIds : List String
  canonicalHandleIds : List String
  publicationIds : List String
  invalidatedByHandoffIds : List Nat
  rejectedPublicationIds : List String
  deriving DecidableEq, Repr

/-- Canonical runtime-upgrade compatibility contract. -/
structure RuntimeUpgradeCompatibility where
  executionConstraint : RuntimeUpgradeExecutionConstraint
  ownershipContinuityRequired : Bool
  pendingEffectTreatment : PendingEffectTreatment
  canonicalPublicationContinuity : CanonicalPublicationContinuity
  deriving DecidableEq, Repr

/-- Canonical runtime-upgrade artifact mirrored from the Rust transition surface. -/
structure RuntimeUpgradeArtifact where
  upgradeId : String
  phase : TransitionArtifactPhase
  previousMembers : List String
  nextMembers : List String
  compatibility : RuntimeUpgradeCompatibility
  carriedPublicationIds : List String
  invalidatedPublicationIds : List String
  carriedObligationIds : List String
  invalidatedObligationIds : List String
  reason : Option String
  deriving DecidableEq, Repr

/-- Whether a finalization path reaches canonical protocol truth. -/
def FinalizationPath.isCanonical (path : FinalizationPath) : Prop :=
  path.stage = .canonical

/-- Whether a finalization path is explicitly invalidated by transition state. -/
def FinalizationPath.isInvalidated (path : FinalizationPath) : Prop :=
  path.stage = .invalidated

/-- Whether a runtime upgrade committed a new active cutover. -/
def RuntimeUpgradeArtifact.isCommittedCutover (artifact : RuntimeUpgradeArtifact) : Prop :=
  artifact.phase = .committedCutover

/-- Canonical stage derivation mirrored from Rust's first-class finalization path. -/
def deriveFinalizationStage
    (readClass : FinalizationReadClass)
    (proofIds canonicalHandleIds : List String)
    (invalidatedByHandoffIds : List Nat)
    (rejectedPublicationIds : List String) : FinalizationStage :=
  if invalidatedByHandoffIds.isEmpty = false then
    .invalidated
  else if rejectedPublicationIds.isEmpty = false then
    .rejected
  else if proofIds.isEmpty = false ∧ canonicalHandleIds.isEmpty = false then
    .canonical
  else if proofIds.isEmpty = false then
    .materialized
  else match readClass with
    | .authoritativeOnly | .mixed => .authoritative
    | .none | .observedOnly => .observed

/-- Build a canonical finalization path from explicit artifact ids. -/
def deriveFinalizationPath
    (operationId : String)
    (session : Option Nat)
    (ownerId : Option String)
    (readClass : FinalizationReadClass)
    (observedReadIds authoritativeReadIds proofIds canonicalHandleIds publicationIds : List String)
    (invalidatedByHandoffIds : List Nat)
    (rejectedPublicationIds : List String) : FinalizationPath :=
  { operationId := operationId
  , session := session
  , ownerId := ownerId
  , readClass := readClass
  , stage := deriveFinalizationStage readClass proofIds canonicalHandleIds
      invalidatedByHandoffIds rejectedPublicationIds
  , observedReadIds := observedReadIds
  , authoritativeReadIds := authoritativeReadIds
  , proofIds := proofIds
  , canonicalHandleIds := canonicalHandleIds
  , publicationIds := publicationIds
  , invalidatedByHandoffIds := invalidatedByHandoffIds
  , rejectedPublicationIds := rejectedPublicationIds }

theorem deriveFinalizationStage_canonical_requires_artifacts
    {readClass : FinalizationReadClass}
    {proofIds canonicalHandleIds : List String}
    {invalidatedByHandoffIds : List Nat}
    {rejectedPublicationIds : List String}
    (hStage :
      deriveFinalizationStage readClass proofIds canonicalHandleIds
        invalidatedByHandoffIds rejectedPublicationIds = .canonical) :
    proofIds ≠ [] ∧ canonicalHandleIds ≠ [] := by
  cases proofIds with
  | nil =>
      exfalso
      cases invalidatedByHandoffIds <;>
        cases rejectedPublicationIds <;>
        cases readClass <;>
        simp [deriveFinalizationStage] at hStage
      all_goals
        cases hStage
  | cons _ _ =>
      cases canonicalHandleIds with
      | nil =>
          exfalso
          cases invalidatedByHandoffIds <;>
            cases rejectedPublicationIds <;>
            simp [deriveFinalizationStage] at hStage
          all_goals
            cases hStage
      | cons _ _ =>
          simp

theorem deriveFinalizationStage_invalidated_not_canonical
    {readClass : FinalizationReadClass}
    {proofIds canonicalHandleIds : List String}
    {invalidatedByHandoffIds : List Nat}
    {rejectedPublicationIds : List String}
    (hStage :
      deriveFinalizationStage readClass proofIds canonicalHandleIds
        invalidatedByHandoffIds rejectedPublicationIds = .invalidated) :
    deriveFinalizationStage readClass proofIds canonicalHandleIds
      invalidatedByHandoffIds rejectedPublicationIds ≠ .canonical := by
  simp [hStage]

theorem runtimeUpgradeArtifact_rolledBack_not_committed
    (artifact : RuntimeUpgradeArtifact)
    (hRollback : artifact.phase = .rolledBack) :
    ¬ artifact.isCommittedCutover := by
  simp [RuntimeUpgradeArtifact.isCommittedCutover, hRollback]

/-- Finalization path induced by an adequate proof/handle pair. -/
def finalizationPathFromSuccessArtifacts
    (ctx : Runtime.ProtocolMachine.Model.SuccessProofContext)
    (operation : Runtime.ProtocolMachine.Model.OperationInstance)
    (proof : Runtime.ProtocolMachine.Model.MaterializationProof)
    (handle : Runtime.ProtocolMachine.Model.CanonicalHandle) : FinalizationPath :=
  deriveFinalizationPath
    operation.operationId
    operation.session
    operation.ownerId
    .authoritativeOnly
    []
    [ctx.requiredPredicateRef]
    [proof.proofId]
    [handle.handleId]
    []
    []
    []

theorem finalizationPathFromSuccessArtifacts_canonical
    {ctx : Runtime.ProtocolMachine.Model.SuccessProofContext}
    {operation : Runtime.ProtocolMachine.Model.OperationInstance}
    {proof : Runtime.ProtocolMachine.Model.MaterializationProof}
    {handle : Runtime.ProtocolMachine.Model.CanonicalHandle}
    (hOperation :
      Runtime.ProtocolMachine.Model.OperationInstance.requiresSuccessProofFor operation ctx)
    (hProof :
      Runtime.ProtocolMachine.Model.MaterializationProof.adequateForSuccessContext proof ctx)
    (hHandle :
      Runtime.ProtocolMachine.Model.CanonicalHandle.adequateForSuccessContext handle ctx proof) :
    (finalizationPathFromSuccessArtifacts ctx operation proof handle).stage = .canonical := by
  simp [finalizationPathFromSuccessArtifacts, deriveFinalizationPath, deriveFinalizationStage]

/-- Finalization invalidation induced by a committed semantic handoff. -/
def finalizationPathFromCommittedHandoff
    (operation : Runtime.ProtocolMachine.Model.OperationInstance)
    (handoff : Runtime.ProtocolMachine.Model.SemanticHandoff) : FinalizationPath :=
  deriveFinalizationPath
    operation.operationId
    operation.session
    operation.ownerId
    .authoritativeOnly
    []
    []
    []
    []
    []
    [handoff.handoffId]
    []

theorem committedHandoff_invalidatesFinalization
    {operation : Runtime.ProtocolMachine.Model.OperationInstance}
    {handoff : Runtime.ProtocolMachine.Model.SemanticHandoff}
    (hCommitted : Runtime.ProtocolMachine.Model.SemanticHandoff.isCommitted handoff) :
    (finalizationPathFromCommittedHandoff operation handoff).stage = .invalidated := by
  simp [finalizationPathFromCommittedHandoff, deriveFinalizationPath,
    deriveFinalizationStage, Runtime.ProtocolMachine.Model.SemanticHandoff.isCommitted] at *

end Proofs
end Runtime
