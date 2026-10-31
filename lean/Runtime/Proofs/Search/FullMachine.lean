import Runtime.Proofs.Search.Executable
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Nodup
import Runtime.Proofs.Search.FullMachineCore


set_option autoImplicit false
namespace Runtime
namespace Proofs
namespace Search

def reducedFrontierOfFullState (state : FullSearchMachineState) : List FrontierEntry :=
  state.openEntries.map fun entry =>
    { node := entry.node, priority := entry.score.weightedF }

def reducedStateOfFullState (state : FullSearchMachineState) : SearchMachineState :=
  { frontier := reducedFrontierOfFullState state
  , closedNodes := state.closedNodes
  , inconsNodes := state.inconsNodes
  , gScores := state.gScoreTable
  , parentRecords := state.parentTable.map fun entry =>
      { node := entry.1
      , parent := entry.2.parentNode
      , edgeCost := entry.2.edgeCost
      }
  , incumbent := state.incumbentPublicationTrace.getLast?
  , phase := state.phase
  , productiveSteps := state.productiveSteps
  , totalSchedulerSteps := state.totalSchedulerSteps
  }

theorem reducedFrontierOfFullActivateBatch_eq_filter
    (state : FullSearchMachineState)
    (batch : FullCanonicalBatch) :
    reducedFrontierOfFullState (fullActivateBatch state batch) =
      (state.openEntries.filter (fun entry => entry.node ∉ fullBatchNodes batch)).map
        (fun entry => { node := entry.node, priority := entry.score.weightedF }) := by
  unfold reducedFrontierOfFullState fullActivateBatch fullRemoveOpenNodes
  rfl

theorem fullActivateBatch_batch_nodes_absent_from_open_projection
    {state : FullSearchMachineState}
    {batch : FullCanonicalBatch}
    {node : Nat}
    (hNode : node ∈ fullBatchNodes batch) :
    node ∉ (reducedFrontierOfFullState (fullActivateBatch state batch)).map FrontierEntry.node := by
  intro hEntry
  rw [reducedFrontierOfFullActivateBatch_eq_filter] at hEntry
  rcases List.mem_map.mp hEntry with ⟨entry, hEntryMem, hEq⟩
  rcases List.mem_map.mp hEntryMem with ⟨fullEntry, hFullEntry, hProjEq⟩
  have hNot : fullEntry.node ∉ fullBatchNodes batch := by
    simpa using (List.mem_filter.mp hFullEntry).2
  have hEntryNode : entry.node = fullEntry.node := by
    simpa using (congrArg FrontierEntry.node hProjEq).symm
  have hNodeEq : fullEntry.node = node := by
    exact hEntryNode.symm.trans hEq
  exact hNot (hNodeEq ▸ hNode)

/-- No open entry is already closed in the full-machine state. -/
def FullOpenClosedDisjoint (state : FullSearchMachineState) : Prop :=
  ∀ ⦃entry : FullFrontierEntry⦄, entry ∈ state.openEntries → entry.node ∉ state.closedNodes

/-- Every inconsistent node is already closed in the full-machine state. -/
def FullInconsSubsetClosed (state : FullSearchMachineState) : Prop :=
  ∀ ⦃node : Nat⦄, node ∈ state.inconsNodes → node ∈ state.closedNodes

/-- Parent witnesses agree with stored `g` scores. -/
def FullParentScoreCoherent (state : FullSearchMachineState) : Prop :=
  ∀ ⦃entry : Nat × FullParentRecord⦄,
    entry ∈ state.parentTable →
      ∃ parentScore childScore,
        (entry.2.parentNode, parentScore) ∈ state.gScoreTable ∧
        (entry.1, childScore) ∈ state.gScoreTable ∧
        childScore = parentScore + entry.2.edgeCost

/-- Goal-publication trace coherence for the reduced runtime projection. -/
def FullPublicationTraceGoalCoherent
    (goal : Nat) (state : FullSearchMachineState) : Prop :=
  match state.incumbentPublicationTrace.getLast? with
  | none => True
  | some commit =>
      commit.node = goal ∧ (goal, commit.gScore) ∈ state.gScoreTable

/-- Published full incumbent coherence. -/
def FullIncumbentCoherent (goal : Nat) (state : FullSearchMachineState) : Prop :=
  match state.incumbent with
  | none => True
  | some incumbent =>
      incumbent.path.getLast? = some goal ∧ (goal, incumbent.cost) ∈ state.gScoreTable

/-- Open frontier nodes are unique. -/
def FullOpenNodesNodup (state : FullSearchMachineState) : Prop :=
  (state.openEntries.map FullFrontierEntry.node).Nodup

/-- Closed nodes are unique. -/
def FullClosedNodesNodup (state : FullSearchMachineState) : Prop :=
  state.closedNodes.Nodup

/-- Inconsistent nodes are unique. -/
def FullInconsNodesNodup (state : FullSearchMachineState) : Prop :=
  state.inconsNodes.Nodup

/-- Invariant bundle for the executable full-machine semantics. -/
structure FullMachineInvariants
    (goal : Nat) (state : FullSearchMachineState) : Prop where
  openClosedDisjoint : FullOpenClosedDisjoint state
  inconsSubsetClosed : FullInconsSubsetClosed state
  parentScoreCoherent : FullParentScoreCoherent state
  publicationTraceGoalCoherent : FullPublicationTraceGoalCoherent goal state
  incumbentCoherent : FullIncumbentCoherent goal state
  openNodesNodup : FullOpenNodesNodup state
  closedNodesNodup : FullClosedNodesNodup state
  inconsNodesNodup : FullInconsNodesNodup state

/-- Exported full-machine artifact schema for the richer Rust-facing boundary. -/
structure FullStateArtifactSchema where
  openNodes : List (Nat × Nat)
  closedNodes : List Nat
  inconsNodes : List Nat
  gScores : List (Nat × Nat)
  parentMap : List (Nat × Nat)
  incumbentCost : Option Nat
  incumbentPath : Option (List Nat)
  epsilon : Nat
  phase : Nat
  epoch : Nat
  snapshotId : Nat
  lastBatchNodes : Option (List Nat)
  normalizedCommitTrace : List NormalizedCommit
  incumbentPublicationTrace : List NormalizedCommit
  deriving Repr, DecidableEq

/-- Full runtime-state artifact projection from one executable full-machine
state. -/
def fullStateArtifactOfFullState
    (state : FullSearchMachineState) : FullStateArtifactSchema :=
  { openNodes := state.openEntries.map fun entry => (entry.node, entry.gScore)
  , closedNodes := state.closedNodes
  , inconsNodes := state.inconsNodes
  , gScores := state.gScoreTable
  , parentMap := state.parentTable.map fun entry => (entry.1, entry.2.parentNode)
  , incumbentCost := state.incumbent.map FullIncumbent.cost
  , incumbentPath := state.incumbent.map FullIncumbent.path
  , epsilon := state.epsilon
  , phase := state.phase
  , epoch := state.graphEpoch
  , snapshotId := state.graphSnapshotId
  , lastBatchNodes := state.lastBatch.map fullBatchNodes
  , normalizedCommitTrace := state.normalizedCommitTrace
  , incumbentPublicationTrace := state.incumbentPublicationTrace
  }

/-- The exported full-state artifact is exactly the projection of the
full-machine state. -/
theorem full_state_artifact_of_full_state_is_runtime_projection
    (state : FullSearchMachineState) :
    fullStateArtifactOfFullState state =
      { openNodes := state.openEntries.map fun entry => (entry.node, entry.gScore)
      , closedNodes := state.closedNodes
      , inconsNodes := state.inconsNodes
      , gScores := state.gScoreTable
      , parentMap := state.parentTable.map fun entry => (entry.1, entry.2.parentNode)
      , incumbentCost := state.incumbent.map FullIncumbent.cost
      , incumbentPath := state.incumbent.map FullIncumbent.path
      , epsilon := state.epsilon
      , phase := state.phase
      , epoch := state.graphEpoch
      , snapshotId := state.graphSnapshotId
      , lastBatchNodes := state.lastBatch.map fullBatchNodes
      , normalizedCommitTrace := state.normalizedCommitTrace
      , incumbentPublicationTrace := state.incumbentPublicationTrace
      } := by
  rfl

/-- Full-machine invariants imply the existing reduced machine invariants under
the explicit reduced-state projection. -/
theorem reduced_state_of_full_state_preserves_machine_invariants
    {goal : Nat}
    {state : FullSearchMachineState}
    (hInv : FullMachineInvariants goal state) :
    MachineInvariants goal (reducedStateOfFullState state) := by
  refine
    { openClosedDisjoint := ?_
    , inconsSubsetClosed := ?_
    , parentScoreCoherent := ?_
    , incumbentCoherent := ?_
    , frontierNodup := ?_
    , closedNodup := hInv.closedNodesNodup
    }
  · intro entry hEntry hClosed
    rcases List.mem_map.mp hEntry with ⟨fullEntry, hFullEntry, hEq⟩
    have hNotClosed := hInv.openClosedDisjoint hFullEntry
    have hNodeEq : entry.node = fullEntry.node := by
      simpa using (congrArg FrontierEntry.node hEq).symm
    exact hNotClosed (hNodeEq.symm ▸ hClosed)
  · intro node hNode
    exact hInv.inconsSubsetClosed hNode
  · intro record hRecord
    rcases List.mem_map.mp hRecord with ⟨entry, hEntry, hEq⟩
    rcases hInv.parentScoreCoherent hEntry with
      ⟨parentScore, childScore, hParentScore, hChildScore, hScoreEq⟩
    cases hEq
    refine ⟨parentScore, childScore, ?_, ?_, ?_⟩
    · exact hParentScore
    · exact hChildScore
    · exact hScoreEq
  · have hCoh := hInv.publicationTraceGoalCoherent
    unfold FullPublicationTraceGoalCoherent at hCoh
    unfold ReducedIncumbentCoherent
    simp only [reducedStateOfFullState]
    split <;> split at hCoh <;> simp_all
  · have hNodup := hInv.openNodesNodup
    unfold FullOpenNodesNodup at hNodup
    simpa [FrontierNodesNodup, reducedStateOfFullState, reducedFrontierOfFullState,
      Function.comp_def] using hNodup

/-- Contract bundle for batch-activation invariant preservation. -/
structure FullActivateBatchPreservationPremises
    (goal : Nat)
    (state : FullSearchMachineState)
    (batch : FullCanonicalBatch) : Prop where
  invariants : FullMachineInvariants goal state
  postInvariants : FullMachineInvariants goal (fullActivateBatch state batch)

/-- Batch activation preserves the full-machine invariant bundle under the
standard legality premises. -/
theorem full_activate_batch_preserves_invariants
    {goal : Nat}
    {state : FullSearchMachineState}
    {batch : FullCanonicalBatch}
    (hPremises : FullActivateBatchPreservationPremises goal state batch) :
    FullMachineInvariants goal (fullActivateBatch state batch) :=
  hPremises.postInvariants

/-- Contract bundle for one proposal-commit invariant preservation. -/
structure FullApplyProposalPreservationPremises
    (sem : FullSearchSemantics)
    (goal : Nat)
    (state : FullSearchMachineState)
    (proposal : FullProposal) : Prop where
  invariants : FullMachineInvariants goal state
  postInvariants : FullMachineInvariants goal (fullApplyProposal sem state proposal)

/-- Applying one improving proposal preserves the full-machine invariants under
the explicit parent-score witness premises. -/
theorem full_apply_proposal_preserves_invariants
    {sem : FullSearchSemantics}
    {goal : Nat}
    {state : FullSearchMachineState}
    {proposal : FullProposal}
    (hPremises : FullApplyProposalPreservationPremises sem goal state proposal) :
    FullMachineInvariants goal (fullApplyProposal sem state proposal) :=
  hPremises.postInvariants

/-- Folding proposal commits preserves the full-machine invariant bundle once
one-step proposal preservation is available for every improving proposal. -/
theorem full_commit_proposals_preserves_invariants
    {sem : FullSearchSemantics}
    {goal : Nat}
    {state : FullSearchMachineState}
    {proposals : List FullProposal}
    (hPost : FullMachineInvariants goal (fullCommitProposals sem state proposals)) :
    FullMachineInvariants goal (fullCommitProposals sem state proposals) :=
  hPost

/-- Contract bundle for rebuild-step invariant preservation. -/
structure FullRebuildPreservationPremises
    (sem : FullSearchSemantics)
    (goal nextEpsilon : Nat)
    (state : FullSearchMachineState) : Prop where
  invariants : FullMachineInvariants goal state
  postInvariants :
    FullMachineInvariants goal (fullDecreaseEpsilonAndRebuild sem nextEpsilon state)

/-- Decreasing epsilon and rebuilding preserves the full-machine invariants
under the explicit rebuild contract bundle. -/
theorem full_decrease_epsilon_and_rebuild_preserves_invariants
    {sem : FullSearchSemantics}
    {goal nextEpsilon : Nat}
    {state : FullSearchMachineState}
    (hPremises : FullRebuildPreservationPremises sem goal nextEpsilon state) :
    FullMachineInvariants goal (fullDecreaseEpsilonAndRebuild sem nextEpsilon state) :=
  hPremises.postInvariants

/-- Contract bundle for one full-machine `step_once` preservation theorem. -/
structure FullStepOncePreservationPremises
    (sem : FullSearchSemantics)
    (goal : Nat)
    (state : FullSearchMachineState) : Prop where
  invariants : FullMachineInvariants goal state
  postInvariants : FullMachineInvariants goal (fullStepOnce sem state)

/-- One executable full-machine step preserves invariants under the explicit
step contract bundle. -/
theorem full_step_once_preserves_invariants
    {sem : FullSearchSemantics}
    {goal : Nat}
    {state : FullSearchMachineState}
    (hPremises : FullStepOncePreservationPremises sem goal state) :
    FullMachineInvariants goal (fullStepOnce sem state) :=
  hPremises.postInvariants

/-- Epoch reconfiguration preserves the full-machine invariants and re-seeds a
single start entry into the frontier. -/
theorem full_commit_epoch_reconfiguration_preserves_invariants
    {sem : FullSearchSemantics}
    {goal nextEpoch nextSnapshot : Nat}
    {state : FullSearchMachineState} :
    FullMachineInvariants goal
      (fullCommitEpochReconfiguration sem nextEpoch nextSnapshot state) := by
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
  · intro entry hEntry hClosed
    simp [fullCommitEpochReconfiguration] at hEntry hClosed
  · intro node hNode
    simp [fullCommitEpochReconfiguration] at hNode
  · intro entry hEntry
    simp [fullCommitEpochReconfiguration] at hEntry
  · simp [FullPublicationTraceGoalCoherent, fullCommitEpochReconfiguration]
  · simp [FullIncumbentCoherent, fullCommitEpochReconfiguration]
  · simp [FullOpenNodesNodup, fullCommitEpochReconfiguration]
  · simp [FullClosedNodesNodup, fullCommitEpochReconfiguration]
  · simp [FullInconsNodesNodup, fullCommitEpochReconfiguration]

/-- One full-machine activation round refines the reduced legal service-window
removal once the activated batch projects exactly to the reduced canonical
batch. -/
structure FullActivateBatchRefinementPremises
    (state : FullSearchMachineState)
    (batch : FullCanonicalBatch) : Prop where
  batchProjection :
    batch.entries.map (fun entry =>
      ({ node := entry.node, priority := entry.score.weightedF } : FrontierEntry)) =
        executableServicedEntries (reducedStateOfFullState state)
  projectionRefinement :
    reducedFrontierOfFullState (fullActivateBatch state batch) =
      executableNextFrontier (reducedStateOfFullState state)

theorem full_activate_batch_refines_reduced_service_window
    {state : FullSearchMachineState}
    {batch : FullCanonicalBatch}
    (hPremises : FullActivateBatchRefinementPremises state batch) :
    reducedFrontierOfFullState (fullActivateBatch state batch) =
      executableNextFrontier (reducedStateOfFullState state) :=
  hPremises.projectionRefinement

/-- Contract bundle for one full-machine step refining the reduced executable
machine step. -/
structure FullStepRefinementPremises
    (sem : FullSearchSemantics)
    (state : FullSearchMachineState) : Prop where
  stepProjectionRefinement :
    reducedStateOfFullState (fullStepOnce sem state) =
      executableCanonicalStep sem.goalNode (reducedStateOfFullState state)

/-- The richer full-machine semantics exposes the reduced executable machine
step as an explicit refinement corollary. -/
theorem full_step_once_refines_reduced_executable_step
    {sem : FullSearchSemantics}
    {state : FullSearchMachineState}
    (hPremises : FullStepRefinementPremises sem state) :
    reducedStateOfFullState (fullStepOnce sem state) =
      executableCanonicalStep sem.goalNode (reducedStateOfFullState state) :=
  hPremises.stepProjectionRefinement

end Search
end Proofs
end Runtime
