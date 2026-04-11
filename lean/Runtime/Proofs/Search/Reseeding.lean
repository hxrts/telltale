import Runtime.Proofs.Search.FullMachine

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.Reseeding

Parameterized epoch-reseeding vocabulary for the executable full-machine lane.

The legacy proof surface only modeled "reset frontier and reseed from start".
This module lifts epoch reconfiguration to an explicit reseeding policy so the
proof vocabulary matches the runtime's typed reseeding surface.
-/

namespace Runtime
namespace Proofs
namespace Search

/-- Supported proof-side epoch reseeding policies. -/
inductive SearchReseedingPolicy where
  | startOnly
  | preserveOpenAndIncons
  deriving DecidableEq, Repr

/-- Full-machine epoch reconfiguration under an explicit reseeding policy. -/
def fullCommitEpochReconfigurationWithPolicy
    (sem : FullSearchSemantics)
    (nextEpoch nextSnapshot : Nat)
    (policy : SearchReseedingPolicy)
    (state : FullSearchMachineState) : FullSearchMachineState :=
  match policy with
  | .startOnly =>
      fullCommitEpochReconfiguration sem nextEpoch nextSnapshot state
  | .preserveOpenAndIncons =>
      let reseededOpen :=
        state.openEntries.map fun entry =>
          fullFrontierEntryFor sem nextEpoch sem.goalNode state.epsilon entry.node entry.gScore
      { state with
        openEntries := reseededOpen
        incumbent := none
        phase := state.phase + 1
        graphEpoch := nextEpoch
        graphSnapshotId := nextSnapshot
        lastBatch := none
        normalizedCommitTrace := []
        incumbentPublicationTrace := []
      }

theorem full_commit_epoch_reconfiguration_start_only_eq_legacy
    (sem : FullSearchSemantics)
    (nextEpoch nextSnapshot : Nat)
    (state : FullSearchMachineState) :
    fullCommitEpochReconfigurationWithPolicy sem nextEpoch nextSnapshot .startOnly state =
      fullCommitEpochReconfiguration sem nextEpoch nextSnapshot state := by
  rfl

theorem full_commit_epoch_reconfiguration_with_policy_preserves_invariants
    {sem : FullSearchSemantics}
    {goal nextEpoch nextSnapshot : Nat}
    {policy : SearchReseedingPolicy}
    {state : FullSearchMachineState}
    (hInv : FullMachineInvariants goal state) :
    FullMachineInvariants goal
      (fullCommitEpochReconfigurationWithPolicy sem nextEpoch nextSnapshot policy state) := by
  cases policy with
  | startOnly =>
      simpa [full_commit_epoch_reconfiguration_start_only_eq_legacy] using
        (full_commit_epoch_reconfiguration_preserves_invariants
          (sem := sem) (goal := goal) (nextEpoch := nextEpoch)
          (nextSnapshot := nextSnapshot) (state := state))
  | preserveOpenAndIncons =>
      refine
        { openClosedDisjoint := ?_
        , inconsSubsetClosed := ?_
        , parentScoreCoherent := ?_
        , publicationTraceGoalCoherent := ?_
        , incumbentCoherent := ?_
        , openNodesNodup := ?_
        , closedNodesNodup := ?_
        , inconsNodesNodup := ?_
        }
      · intro entry hEntry
        simp [fullCommitEpochReconfigurationWithPolicy] at hEntry
        rcases hEntry with ⟨orig, hOrig, rfl⟩
        simpa [fullFrontierEntryFor] using hInv.openClosedDisjoint hOrig
      · simpa [FullInconsSubsetClosed, fullCommitEpochReconfigurationWithPolicy] using
          hInv.inconsSubsetClosed
      · simpa [FullParentScoreCoherent, fullCommitEpochReconfigurationWithPolicy] using
          hInv.parentScoreCoherent
      · simp [FullPublicationTraceGoalCoherent, fullCommitEpochReconfigurationWithPolicy]
      · simp [FullIncumbentCoherent, fullCommitEpochReconfigurationWithPolicy]
      · simpa [FullOpenNodesNodup, fullCommitEpochReconfigurationWithPolicy] using
          hInv.openNodesNodup
      · simpa [FullClosedNodesNodup, fullCommitEpochReconfigurationWithPolicy] using
          hInv.closedNodesNodup
      · simpa [FullInconsNodesNodup, fullCommitEpochReconfigurationWithPolicy] using
          hInv.inconsNodesNodup

/-- The start-only reseeding policy refines exactly to the legacy reduced
reconfiguration projection. -/
theorem reduced_start_only_reseeding_refines_legacy_projection
    (sem : FullSearchSemantics)
    (nextEpoch nextSnapshot : Nat)
    (state : FullSearchMachineState) :
    reducedStateOfFullState
      (fullCommitEpochReconfigurationWithPolicy sem nextEpoch nextSnapshot .startOnly state) =
      reducedStateOfFullState
        (fullCommitEpochReconfiguration sem nextEpoch nextSnapshot state) := by
  rfl

/-- Preserve-open-and-incons reseeding keeps the reduced open/closed/incons
partition and only clears the reduced selected result and replay-facing traces. -/
theorem reduced_preserve_open_and_incons_reseeding_projection
    (sem : FullSearchSemantics)
    (nextEpoch nextSnapshot : Nat)
    (state : FullSearchMachineState) :
    let next :=
      reducedStateOfFullState
        (fullCommitEpochReconfigurationWithPolicy sem nextEpoch nextSnapshot
          .preserveOpenAndIncons state)
    next.closedNodes = state.closedNodes ∧
      next.inconsNodes = state.inconsNodes ∧
      next.incumbent = none := by
  simp [fullCommitEpochReconfigurationWithPolicy, reducedStateOfFullState]

end Search
end Proofs
end Runtime
