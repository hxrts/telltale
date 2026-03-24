import Runtime.ProtocolMachine.Model

set_option autoImplicit false

/-! # Runtime.Proofs.Examples.CrossTargetProgressDependentWork

Small example witnesses for native/wasm progress compatibility and declared
dependent-work discharge.
-/

namespace Runtime
namespace Proofs
namespace Examples

open Runtime.ProtocolMachine.Model

def parentOp : OperationInstance :=
  { operationId := "accept-invite"
  , session := some 23
  , ownerId := some "coord"
  , kind := "accept_invite"
  , phase := .succeeded
  , handlerIdentity := none
  , effectIds := []
  , dependentOperationIds := ["sync-membership"]
  , terminalPublication := some "Accepted(channel-1)"
  , budgetTicks := some 5
  , requiresProof := true
  }

def childOp : OperationInstance :=
  { operationId := "sync-membership"
  , session := some 23
  , ownerId := some "coord"
  , kind := "sync_membership"
  , phase := .succeeded
  , handlerIdentity := none
  , effectIds := []
  , dependentOperationIds := []
  , terminalPublication := some "Synced(channel-1)"
  , budgetTicks := some 3
  , requiresProof := false
  }

def terminalPublication : PublicationEvent :=
  { publicationId := "pub-parent"
  , session := some 23
  , operationId := "accept-invite"
  , ownerId := some "coord"
  , publication := "Accepted(channel-1)"
  , observerClass := .canonical
  , status := .published
  , proofRef := some "proof-parent"
  , handleRef := some "handle-parent"
  , reason := none
  }

def nativeBlocked : RealizedProgressView :=
  { realization := .nativeThreaded
  , contract :=
      { operationId := "accept-invite"
      , session := some 23
      , state := .blocked
      , lastOrderingKey := some 1
      , bounded := true
      , budgetTicks := some 5
      , lastProgressTick := some 2
      , escalatedAtTick := none
      , reason := some "waiting_membership" } }

def wasmNoProgress : RealizedProgressView :=
  { realization := .wasmSingleThreaded
  , contract :=
      { operationId := "accept-invite"
      , session := some 23
      , state := .noProgress
      , lastOrderingKey := some 1
      , bounded := true
      , budgetTicks := some 5
      , lastProgressTick := some 2
      , escalatedAtTick := some 3
      , reason := some "waiting_membership" } }

def nativeSucceeded : RealizedProgressView :=
  { realization := .nativeCooperative
  , contract :=
      { operationId := "accept-invite"
      , session := some 23
      , state := .succeeded
      , lastOrderingKey := some 2
      , bounded := true
      , budgetTicks := some 5
      , lastProgressTick := some 4
      , escalatedAtTick := none
      , reason := none } }

def wasmSucceeded : RealizedProgressView :=
  { realization := .wasmSingleThreaded
  , contract :=
      { operationId := "accept-invite"
      , session := some 23
      , state := .succeeded
      , lastOrderingKey := some 2
      , bounded := true
      , budgetTicks := some 5
      , lastProgressTick := some 4
      , escalatedAtTick := none
      , reason := none } }

def dependentWorkObjects : ProtocolMachineSemanticObjects :=
  { operationInstances := [parentOp, childOp]
  , outstandingEffects := []
  , semanticHandoffs := []
  , transformationObligations := []
  , authoritativeReads := []
  , observedReads := []
  , materializationProofs := []
  , canonicalHandles := []
  , publicationEvents := [terminalPublication]
  , progressContracts := [nativeBlocked.contract, wasmNoProgress.contract, nativeSucceeded.contract]
  , progressTransitions := []
  }

theorem waiting_views_cross_target_compatible :
    nativeBlocked.crossTargetCompatible wasmNoProgress := by
  constructor
  · simp [RealizedProgressView.sameSubject, nativeBlocked, wasmNoProgress]
  · exact Runtime.ProtocolMachine.Model.blocked_noProgress_crossTargetEquivalent

theorem success_views_cross_target_preserved :
    dependentWorkObjects.crossTargetProgressPreserved nativeSucceeded wasmSucceeded := by
  constructor
  · constructor
    · simp [RealizedProgressView.sameSubject, nativeSucceeded, wasmSucceeded]
    · simp [ProgressState.crossTargetEquivalent, ProgressState.crossTargetMeaning,
        nativeSucceeded, wasmSucceeded]
  constructor
  · intro hTerminal
    refine ⟨terminalPublication, by simp [dependentWorkObjects], ?_⟩
    simp [terminalPublication, nativeSucceeded]
  · intro hTerminal
    refine ⟨terminalPublication, by simp [dependentWorkObjects], ?_⟩
    simp [terminalPublication, wasmSucceeded]

theorem child_resolves_declared_work :
    parentOp.dependentWorkResolvedBy childOp := by
  constructor
  · constructor
    · simp [parentOp, childOp]
    · simp [parentOp, childOp]
  constructor
  · simp [childOp]
  · simp [OperationInstance.hasTerminalTruth, childOp]

theorem dependent_work_fully_resolved :
    dependentWorkObjects.dependentWorkFullyResolved parentOp := by
  intro childId hMem
  simp [parentOp] at hMem
  subst hMem
  refine ⟨childOp, by simp [dependentWorkObjects], ?_⟩
  simp [childOp, parentOp, OperationInstance.hasTerminalTruth]

theorem parent_terminality_composed :
    dependentWorkObjects.parentTerminalityComposedFromDependents
      parentOp nativeSucceeded.contract := by
  constructor
  · simp [ProgressContract.tracksOperation, nativeSucceeded, parentOp,
      ProgressState.expectedOperationPhase]
  constructor
  · exact dependent_work_fully_resolved
  · intro hTerminal
    refine ⟨by simp [OperationInstance.hasTerminalTruth, parentOp], ?_⟩
    refine ⟨terminalPublication, by simp [dependentWorkObjects], ?_⟩
    simp [terminalPublication, parentOp]

example :
    parentOp.hasTerminalTruth := by
  exact Runtime.ProtocolMachine.Model.parentTerminalityComposedFromDependents_terminal_truth
    parent_terminality_composed
    (by simp [ProgressContract.isTerminal, ProgressState.isTerminal, nativeSucceeded])

example :
    dependentWorkObjects.hasCanonicalTerminalPublicationFor
      parentOp.operationId parentOp.session := by
  exact Runtime.ProtocolMachine.Model.parentTerminalityComposedFromDependents_canonical_publication
    parent_terminality_composed
    (by simp [ProgressContract.isTerminal, ProgressState.isTerminal, nativeSucceeded])

end Examples
end Proofs
end Runtime
