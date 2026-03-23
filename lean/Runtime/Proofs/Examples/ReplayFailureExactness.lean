import Runtime.Proofs.VM.ReplayFailureExactness

set_option autoImplicit false

/-! # Runtime.Proofs.Examples.ReplayFailureExactness

Small example witnesses for replay-stable operation identity, terminal-truth
stability, and failure exactness / audit alignment.
-/

namespace Runtime
namespace Proofs
namespace Examples

open Runtime.VM.Model

def replayFailedOp : OperationInstance :=
  { operationId := "op-replay"
  , session := some 11
  , ownerId := some "owner-a"
  , kind := "sync_membership"
  , phase := .failed
  , handlerIdentity := none
  , effectIds := [7]
  , dependentOperationIds := []
  , terminalPublication := some "Rejected(permission_denied)"
  , budgetTicks := some 5
  , requiresProof := true
  }

def replayFailedOpReplica : OperationInstance :=
  { replayFailedOp with ownerId := some "owner-b" }

def lateEffect : OutstandingEffect :=
  { effectId := 7
  , operationId := "op-replay"
  , session := some 11
  , ownerId := some "owner-a"
  , effectInterface := some "membership"
  , effectOperation := some "sync"
  , effectKind := "required"
  , handlerIdentity := "handler-a"
  , status := .cancelled
  , orderingKey := 10
  , budgetTicks := some 1
  , retryPolicy := "forbidden"
  , invalidationToken := "inv-1"
  , completedAtTick := some 14
  , inputs := "[]"
  , outputs := "cancelled"
  }

def exactFailureContract : ProgressContract :=
  { operationId := "op-replay"
  , session := some 11
  , state := .failed
  , lastOrderingKey := some 10
  , bounded := true
  , budgetTicks := some 5
  , lastProgressTick := some 13
  , escalatedAtTick := some 14
  , reason := some "permission_denied"
  }

def degradedContract : ProgressContract :=
  { operationId := "op-replay"
  , session := some 11
  , state := .degraded
  , lastOrderingKey := some 10
  , bounded := true
  , budgetTicks := some 5
  , lastProgressTick := some 12
  , escalatedAtTick := some 13
  , reason := some "blocked"
  }

def degradedTransition : ProgressTransition :=
  { operationId := "op-replay"
  , session := some 11
  , fromState := .noProgress
  , toState := .degraded
  , tick := 13
  , reason := some "bounded_wait_exhausted"
  }

def failurePublication : PublicationEvent :=
  { publicationId := "pub-fail"
  , session := some 11
  , operationId := "op-replay"
  , ownerId := some "owner-a"
  , publication := "Rejected(permission_denied)"
  , observerClass := .canonical
  , status := .published
  , proofRef := some "proof-fail"
  , handleRef := some "handle-fail"
  , reason := none
  }

def exactFailureCtx : ReplayFailureContext :=
  { operationId := "op-replay"
  , session := some 11
  , expectedState := .failed
  }

def degradedCtx : ReplayFailureContext :=
  { operationId := "op-replay"
  , session := some 11
  , expectedState := .degraded
  }

def replayFailureObjects : ProtocolMachineSemanticObjects :=
  { operationInstances := [replayFailedOp, replayFailedOpReplica]
  , outstandingEffects := [lateEffect]
  , semanticHandoffs := []
  , transformationObligations := []
  , authoritativeReads := []
  , observedReads := []
  , materializationProofs := []
  , canonicalHandles := []
  , publicationEvents := [failurePublication]
  , progressContracts := [exactFailureContract, degradedContract]
  , progressTransitions := [degradedTransition]
  }

theorem replayFailureObjects_identity_stable :
    replayFailureObjects.replayStableOperationIdentity := by
  intro operation₁ hMem₁ operation₂ hMem₂ hReplay
  have h₁ : operation₁ = replayFailedOp ∨ operation₁ = replayFailedOpReplica := by
    simpa [replayFailureObjects] using hMem₁
  have h₂ : operation₂ = replayFailedOp ∨ operation₂ = replayFailedOpReplica := by
    simpa [replayFailureObjects] using hMem₂
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;>
    simp [OperationInstance.sameReplayIdentity, replayFailedOp, replayFailedOpReplica] at hReplay ⊢

theorem replayFailureObjects_terminal_truth_stable :
    replayFailureObjects.terminalTruthStableUnderReplay := by
  intro operation₁ hMem₁ operation₂ hMem₂ hReplay hTruth₁ hTruth₂
  have h₁ : operation₁ = replayFailedOp ∨ operation₁ = replayFailedOpReplica := by
    simpa [replayFailureObjects] using hMem₁
  have h₂ : operation₂ = replayFailedOp ∨ operation₂ = replayFailedOpReplica := by
    simpa [replayFailureObjects] using hMem₂
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;>
    simp [OperationInstance.sameReplayIdentity, OperationInstance.hasTerminalTruth,
      replayFailedOp, replayFailedOpReplica] at hReplay hTruth₁ hTruth₂ ⊢

theorem replayFailureObjects_stale_late_rejected :
    replayFailureObjects.staleLateResultRejected := by
  intro effect hMem ownerId tick hLate
  have hEffect : effect = lateEffect := by
    simpa [replayFailureObjects] using hMem
  subst hEffect
  exact hLate.2

theorem replayFailureObjects_exact_failure_audit :
    replayFailureObjects.failureAuditAligned exactFailureCtx := by
  intro contract hMem hCtx
  constructor
  · intro hExact
    refine ⟨failurePublication, by simp [replayFailureObjects], ?_⟩
    simp [PublicationEvent.matchesCanonicalReplayAudit, failurePublication, exactFailureCtx]
  · intro hAbstraction
    simp [exactFailureCtx, ProgressState.failureExactness] at hAbstraction

theorem replayFailureObjects_degraded_audit :
    replayFailureObjects.failureAuditAligned degradedCtx := by
  intro contract hMem hCtx
  constructor
  · intro hExact
    simp [degradedCtx, ProgressState.failureExactness] at hExact
  · intro hAbstraction
    refine ⟨degradedTransition, by simp [replayFailureObjects], ?_⟩
    simp [ProgressTransition.matchesReplayFailureContext, degradedTransition, degradedCtx]

example :
    replayFailureObjects.replayFailureConformanceAligned exactFailureCtx := by
  refine ⟨replayFailureObjects_identity_stable,
    replayFailureObjects_terminal_truth_stable,
    replayFailureObjects_stale_late_rejected,
    replayFailureObjects_exact_failure_audit⟩

example :
    replayFailureObjects.replayFailureConformanceAligned degradedCtx := by
  refine ⟨replayFailureObjects_identity_stable,
    replayFailureObjects_terminal_truth_stable,
    replayFailureObjects_stale_late_rejected,
    replayFailureObjects_degraded_audit⟩

example :
    ProgressState.failureObservationallyEquivalent .blocked .noProgress := by
  exact Runtime.Proofs.VM.blocked_and_noProgress_are_wait_equivalent

example :
    ¬ ProgressState.failureObservationallyEquivalent .degraded .blocked := by
  exact Runtime.Proofs.VM.degraded_is_not_wait_equivalent

end Examples
end Proofs
end Runtime
