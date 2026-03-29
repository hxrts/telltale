import Runtime.Proofs.Conservation.API
import Runtime.Proofs.ProtocolMachine.SemanticObjects.ProgressContracts
import Runtime.Proofs.Examples.PublicationMaterialization
import Runtime.Proofs.Examples.ReplayFailureExactness

set_option autoImplicit false

/-! # Runtime.Proofs.AuthorityMetatheory

This module makes the supported authority theorem slice explicit.

The current decision is intentionally narrow:

- do **not** extend the session-type theorem story to every authority-bearing DSL form
- keep the broad conservation theorems over protocol-machine semantic objects
- treat the smallest first-class authority slice as:
  - evidence-bearing authoritative reads
  - canonical publication/materialization
  - explicit progress contracts for the parity-critical operation they protect

This gives a principled theorem story for the supported slice without pretending
that handoff, dependent work, timeout/cancellation, or the wider lifecycle
family are already session-typed theorems.
-/

namespace Runtime
namespace Proofs

open Runtime.ProtocolMachine.Model
open Runtime.Proofs.Conservation

/-- The currently supported theorem slice for authority-bearing semantics. -/
def SupportedAuthoritySemanticSlice
    (objects : ProtocolMachineSemanticObjects)
    (ctx : AuthoritativeCommitmentContext) : Prop :=
  objects.authoritativeCommitPermitted ctx ∧
  objects.commitmentPublicationDisciplined ctx

/-- Preservation-style consequence for the supported authority slice:
an admitted authoritative commitment keeps both its authoritative read witness
and its canonical publication path. -/
theorem supportedAuthoritySemanticSlice_preservation
    {objects : ProtocolMachineSemanticObjects}
    {ctx : AuthoritativeCommitmentContext}
    (hSlice : SupportedAuthoritySemanticSlice objects ctx) :
    ∃ read ∈ objects.authoritativeReads,
      read.hasAuthorityContext ∧
      read.satisfiesCommitmentContext ctx ∧
      ∃ event ∈ objects.publicationEvents,
        event.canonicalPublicationFor ctx ∧
        event.ownerId.isSome ∧
        event.proofRef.isSome ∧
        event.handleRef.isSome := by
  rcases hSlice with ⟨hCommit, hDisciplined⟩
  rcases authoritative_commit_requires_authoritative_read hCommit with
    ⟨read, hReadMem, hHasAuthority, hSatisfies⟩
  rcases Runtime.ProtocolMachine.Model.commitment_publication_requires_handle_and_proof
      hDisciplined hCommit with
    ⟨event, hEventMem, hCanonical, hOwner, hProof, hHandle⟩
  exact ⟨read, hReadMem, hHasAuthority, hSatisfies,
    event, hEventMem, hCanonical, hOwner, hProof, hHandle⟩

/-- Progress-style consequence for the supported authority slice:
every parity-critical protected operation has an explicit progress contract that
already satisfies the generic Lyapunov/progress interface. -/
theorem supportedAuthoritySemanticSlice_progress
    {objects : ProtocolMachineSemanticObjects}
    {operation : OperationInstance}
    (hContracts : objects.parityCriticalOperationsHaveProgressContract)
    (hMem : operation ∈ objects.operationInstances)
    (hParity : operation.isParityCritical) :
    ∃ contract ∈ objects.progressContracts,
      contract.tracksOperation operation ∧
      contract.lyapunovCompatible := by
  rcases Runtime.ProtocolMachine.Model.parityCriticalOperationsHaveProgressContract_explicit
      hContracts hMem hParity with
    ⟨contract, hContractMem, hTracks⟩
  exact ⟨contract, hContractMem, hTracks,
    Runtime.ProtocolMachine.Model.lyapunovCompatible_of_progressContract contract⟩

/-- Non-terminal parity-critical protected operations enjoy an explicit
one-step progress witness via their contract. -/
theorem supportedAuthoritySemanticSlice_nonterminal_progress
    {objects : ProtocolMachineSemanticObjects}
    {operation : OperationInstance}
    (hContracts : objects.parityCriticalOperationsHaveProgressContract)
    (hMem : operation ∈ objects.operationInstances)
    (hParity : operation.isParityCritical) :
    ∃ contract ∈ objects.progressContracts,
      contract.tracksOperation operation ∧
      (¬ contract.isTerminal →
        ∃ next, contract.syntheticStep = some next ∧
          next.progressMeasure < contract.progressMeasure) := by
  rcases Runtime.ProtocolMachine.Model.parityCriticalOperationsHaveProgressContract_explicit
      hContracts hMem hParity with
    ⟨contract, hContractMem, hTracks⟩
  refine ⟨contract, hContractMem, hTracks, ?_⟩
  intro hNonTerminal
  exact Runtime.ProtocolMachine.Model.schedulingBoundCompatible_of_progressContract contract
    hNonTerminal

/-! ## Concrete Witnesses -/

private def publicationRead : AuthoritativeRead :=
  { readId := "read-accept"
  , session := some 7
  , ownerId := some "owner-a"
  , kind := .outputCondition
  , lifecycle := .verified
  , predicateRef := some "accepted"
  , witnessId := none
  , generation := none
  , reason := none
  }

private def publicationObjectsWithRead : ProtocolMachineSemanticObjects :=
  { Examples.publicationObjects with authoritativeReads := [publicationRead] }

example :
    SupportedAuthoritySemanticSlice publicationObjectsWithRead
      Examples.publicationCtx := by
  constructor
  · refine ⟨publicationRead, by simp [publicationObjectsWithRead, publicationRead], ?_⟩
    simp [AuthoritativeRead.satisfiesCommitmentContext,
      AuthoritativeRead.hasAuthorityContext, publicationRead, Examples.publicationCtx]
  · intro _hCommit
    refine ⟨Examples.successPublication, by
      simp [publicationObjectsWithRead, Examples.publicationObjects], ?_, ?_⟩
    · simp [PublicationEvent.canonicalPublicationFor,
        Examples.successPublication, Examples.publicationCtx]
    · simp [PublicationEvent.hasCanonicalAuthorityEvidence, Examples.successPublication]

example :
    ∃ contract ∈ Examples.replayFailureObjects.progressContracts,
      contract.tracksOperation Examples.replayFailedOp ∧
      contract.lyapunovCompatible := by
  have hContracts :
      Examples.replayFailureObjects.parityCriticalOperationsHaveProgressContract := by
    intro operation hMem hParity
    refine ⟨Examples.exactFailureContract, by simp [Examples.replayFailureObjects], ?_⟩
    have hCases :
        operation = Examples.replayFailedOp ∨
          operation = Examples.replayFailedOpReplica := by
      simpa [Examples.replayFailureObjects] using hMem
    rcases hCases with rfl | rfl <;>
      simp [ProgressContract.tracksOperation,
        ProgressState.expectedOperationPhase, Examples.exactFailureContract,
        Examples.replayFailedOp, Examples.replayFailedOpReplica]
  exact supportedAuthoritySemanticSlice_progress hContracts
    (by simp [Examples.replayFailureObjects])
    (by left; simp [Examples.replayFailedOp])

end Proofs
end Runtime
