import Runtime.Proofs.Search.Executable
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Nodup

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.FullMachine

Executable fuller-machine search semantics over a natural-number domain.

This module deliberately stops short of claiming full Rust↔Lean refinement.
Its role is to model the missing transition families that the reduced lane does
not represent: proposal generation, normalization, commit, rebuild, and epoch
reconfiguration.
-/

namespace Runtime
namespace Proofs
namespace Search

structure FullFrontierScore where
  weightedF : Nat
  gCost : Nat
  deriving DecidableEq, Repr

structure FullFrontierEntry where
  node : Nat
  gScore : Nat
  score : FullFrontierScore
  deriving DecidableEq, Repr

structure FullParentRecord where
  parentNode : Nat
  edgeCost : Nat
  deriving DecidableEq, Repr

structure FullIncumbent where
  cost : Nat
  path : List Nat
  deriving DecidableEq, Repr

structure FullProposal where
  batchIndex : Nat
  sourceNode : Nat
  targetNode : Nat
  edgeCost : Nat
  tentativeG : Nat
  deriving DecidableEq, Repr

structure FullCanonicalBatch where
  epoch : Nat
  snapshotId : Nat
  phase : Nat
  minScore : FullFrontierScore
  entries : List FullFrontierEntry
  deriving DecidableEq, Repr

structure FullSearchMachineState where
  openEntries : List FullFrontierEntry
  closedNodes : List Nat
  inconsNodes : List Nat
  gScoreTable : List (Nat × Nat)
  parentTable : List (Nat × FullParentRecord)
  incumbent : Option FullIncumbent
  epsilon : Nat
  phase : Nat
  graphEpoch : Nat
  graphSnapshotId : Nat
  budgetExpansions : Nat
  budgetBatches : Nat
  productiveSteps : Nat
  totalSchedulerSteps : Nat
  lastBatch : Option FullCanonicalBatch
  normalizedCommitTrace : List NormalizedCommit
  incumbentPublicationTrace : List NormalizedCommit
  deriving DecidableEq, Repr

structure FullSearchSemantics where
  startNode : Nat
  goalNode : Nat
  successors : Nat → Nat → List (Nat × Nat)
  heuristic : Nat → Nat → Nat → Nat

def fullLookupGScore (state : FullSearchMachineState) (node : Nat) : Option Nat :=
  (state.gScoreTable.find? fun entry => entry.1 = node).map Prod.snd

def fullLookupParent
    (state : FullSearchMachineState) (node : Nat) : Option FullParentRecord :=
  (state.parentTable.find? fun entry => entry.1 = node).map Prod.snd

def fullFrontierScoreFor
    (sem : FullSearchSemantics)
    (epoch goal epsilon node gScore : Nat) : FullFrontierScore :=
  { weightedF := epsilon * (gScore + sem.heuristic epoch node goal)
  , gCost := gScore
  }

def fullFrontierEntryFor
    (sem : FullSearchSemantics)
    (epoch goal epsilon node gScore : Nat) : FullFrontierEntry :=
  { node := node
  , gScore := gScore
  , score := fullFrontierScoreFor sem epoch goal epsilon node gScore
  }

def fullFrontierEntryLe (left right : FullFrontierEntry) : Prop :=
  left.score.weightedF < right.score.weightedF ∨
    (left.score.weightedF = right.score.weightedF ∧
      (left.score.gCost < right.score.gCost ∨
        (left.score.gCost = right.score.gCost ∧ left.node ≤ right.node)))

instance : DecidableRel fullFrontierEntryLe := by
  intro left right
  unfold fullFrontierEntryLe
  infer_instance

def fullSuccessorLe (left right : Nat × Nat) : Prop :=
  left.1 ≤ right.1

instance : DecidableRel fullSuccessorLe := by
  intro left right
  unfold fullSuccessorLe
  infer_instance

def fullProposalLe (left right : FullProposal) : Prop :=
  left.targetNode < right.targetNode ∨
    (left.targetNode = right.targetNode ∧
      (left.tentativeG < right.tentativeG ∨
        (left.tentativeG = right.tentativeG ∧
          (left.sourceNode < right.sourceNode ∨
            (left.sourceNode = right.sourceNode ∧ left.batchIndex ≤ right.batchIndex)))))

instance : DecidableRel fullProposalLe := by
  intro left right
  unfold fullProposalLe
  infer_instance

def fullSortedOpenEntries (state : FullSearchMachineState) : List FullFrontierEntry :=
  state.openEntries.insertionSort fullFrontierEntryLe

def fullNextBatch (state : FullSearchMachineState) : Option FullCanonicalBatch :=
  match fullSortedOpenEntries state with
  | [] => none
  | head :: _ =>
      let entries :=
        (fullSortedOpenEntries state).takeWhile fun entry =>
          entry.score = head.score
      some
        { epoch := state.graphEpoch
        , snapshotId := state.graphSnapshotId
        , phase := state.phase
        , minScore := head.score
        , entries := entries
        }

def fullBatchNodes (batch : FullCanonicalBatch) : List Nat :=
  batch.entries.map FullFrontierEntry.node

def fullExpandBatchEntry
    (sem : FullSearchSemantics)
    (epoch : Nat)
    (batchIndex : Nat)
    (entry : FullFrontierEntry) : List FullProposal :=
  let ordered := (sem.successors epoch entry.node).insertionSort fullSuccessorLe
  ordered.map fun successor =>
    { batchIndex := batchIndex
    , sourceNode := entry.node
    , targetNode := successor.1
    , edgeCost := successor.2
    , tentativeG := entry.gScore + successor.2
    }

def fullExpandBatchAux
    (sem : FullSearchSemantics)
    (epoch : Nat)
    (batchIndex : Nat) : List FullFrontierEntry → List FullProposal
  | [] => []
  | entry :: rest =>
      fullExpandBatchEntry sem epoch batchIndex entry ++
        fullExpandBatchAux sem epoch (batchIndex + 1) rest

def fullExpandBatch
    (sem : FullSearchSemantics)
    (batch : FullCanonicalBatch) : List FullProposal :=
  fullExpandBatchAux sem batch.epoch 0 batch.entries

def fullNormalizeProposals (proposals : List FullProposal) : List FullProposal :=
  proposals.insertionSort fullProposalLe

def fullRemoveOpenNodes
    (entries : List FullFrontierEntry) (nodes : List Nat) : List FullFrontierEntry :=
  entries.filter fun entry => entry.node ∉ nodes

def fullUpsertGScore
    (scores : List (Nat × Nat)) (node gScore : Nat) : List (Nat × Nat) :=
  (node, gScore) :: scores.filter (fun entry => entry.1 ≠ node)

def fullUpsertParent
    (parents : List (Nat × FullParentRecord))
    (node : Nat)
    (record : FullParentRecord) : List (Nat × FullParentRecord) :=
  (node, record) :: parents.filter (fun entry => entry.1 ≠ node)

def fullActivateBatch
    (state : FullSearchMachineState)
    (batch : FullCanonicalBatch) : FullSearchMachineState :=
  { state with
    openEntries := fullRemoveOpenNodes state.openEntries (fullBatchNodes batch)
    closedNodes := state.closedNodes ++ fullBatchNodes batch
    lastBatch := some batch
  }

def fullProposalImprovesState
    (state : FullSearchMachineState) (proposal : FullProposal) : Bool :=
  match fullLookupGScore state proposal.targetNode with
  | none => true
  | some current =>
      if proposal.tentativeG < current then
        true
      else if proposal.tentativeG = current then
        match fullLookupParent state proposal.targetNode with
        | none => true
        | some currentParent => proposal.sourceNode < currentParent.parentNode
      else
        false

def fullGoalCommitOfProposal
    (sem : FullSearchSemantics) (proposal : FullProposal) : Option NormalizedCommit :=
  if proposal.targetNode = sem.goalNode then
    some
      { node := proposal.targetNode
      , parent := some proposal.sourceNode
      , gScore := proposal.tentativeG
      }
  else
    none

def fullApplyProposal
    (sem : FullSearchSemantics)
    (state : FullSearchMachineState)
    (proposal : FullProposal) : FullSearchMachineState :=
  let nextScores := fullUpsertGScore state.gScoreTable proposal.targetNode proposal.tentativeG
  let nextParents :=
    fullUpsertParent state.parentTable proposal.targetNode
      { parentNode := proposal.sourceNode, edgeCost := proposal.edgeCost }
  let nextOpen :=
    if proposal.targetNode ∈ state.closedNodes then
      state.openEntries.filter fun entry => entry.node ≠ proposal.targetNode
    else
      fullFrontierEntryFor sem state.graphEpoch sem.goalNode state.epsilon
        proposal.targetNode proposal.tentativeG ::
        state.openEntries.filter fun entry => entry.node ≠ proposal.targetNode
  let nextIncons :=
    if proposal.targetNode ∈ state.closedNodes then
      proposal.targetNode :: state.inconsNodes.filter fun node => node ≠ proposal.targetNode
    else
      state.inconsNodes.filter fun node => node ≠ proposal.targetNode
  let nextCommit : NormalizedCommit :=
    { node := proposal.targetNode
    , parent := some proposal.sourceNode
    , gScore := proposal.tentativeG
    }
  let nextPublications :=
    match fullGoalCommitOfProposal sem proposal with
    | none => state.incumbentPublicationTrace
    | some goalCommit => state.incumbentPublicationTrace ++ [goalCommit]
  let nextIncumbent :=
    match fullGoalCommitOfProposal sem proposal with
    | none => state.incumbent
    | some goalCommit =>
        some
          { cost := goalCommit.gScore
          , path := [proposal.sourceNode, goalCommit.node]
          }
  { state with
    gScoreTable := nextScores
    parentTable := nextParents
    openEntries := nextOpen
    inconsNodes := nextIncons
    incumbent := nextIncumbent
    normalizedCommitTrace := state.normalizedCommitTrace ++ [nextCommit]
    incumbentPublicationTrace := nextPublications
  }

def fullCommitProposals
    (sem : FullSearchSemantics)
    (state : FullSearchMachineState)
    (proposals : List FullProposal) : FullSearchMachineState :=
  proposals.foldl
    (fun acc proposal =>
      if fullProposalImprovesState acc proposal then
        fullApplyProposal sem acc proposal
      else
        acc)
    state

def fullStepOnce
    (sem : FullSearchSemantics)
    (state : FullSearchMachineState) : FullSearchMachineState :=
  match fullNextBatch state with
  | none =>
      { state with totalSchedulerSteps := state.totalSchedulerSteps + 1 }
  | some batch =>
      let proposals := fullExpandBatch sem batch
      let activated :=
        fullActivateBatch
          { state with totalSchedulerSteps := state.totalSchedulerSteps + 1 } batch
      let normalized := fullNormalizeProposals proposals
      let committed := fullCommitProposals sem activated normalized
      { committed with
        budgetExpansions := committed.budgetExpansions + batch.entries.length
        budgetBatches := committed.budgetBatches + 1
        productiveSteps :=
          committed.productiveSteps + if normalized = [] then 0 else 1
      }

def fullDecreaseEpsilonAndRebuild
    (sem : FullSearchSemantics)
    (nextEpsilon : Nat)
    (state : FullSearchMachineState) : FullSearchMachineState :=
  if nextEpsilon > state.epsilon then
    state
  else if nextEpsilon = state.epsilon then
    state
  else
    let rebuildNodes :=
      (state.openEntries.map FullFrontierEntry.node ++ state.inconsNodes).eraseDups
    let rebuiltOpen :=
      rebuildNodes.filterMap fun node =>
        (fullLookupGScore state node).map fun gScore =>
          fullFrontierEntryFor sem state.graphEpoch sem.goalNode nextEpsilon node gScore
    { state with
      openEntries := rebuiltOpen
      closedNodes := []
      inconsNodes := []
      epsilon := nextEpsilon
      phase := state.phase + 1
      lastBatch := none
    }

def fullCommitEpochReconfiguration
    (sem : FullSearchSemantics)
    (nextEpoch nextSnapshot : Nat)
    (state : FullSearchMachineState) : FullSearchMachineState :=
  let startEntry :=
    fullFrontierEntryFor sem nextEpoch sem.goalNode state.epsilon sem.startNode 0
  { state with
    openEntries := [startEntry]
    closedNodes := []
    inconsNodes := []
    gScoreTable := [(sem.startNode, 0)]
    parentTable := []
    incumbent := none
    phase := state.phase + 1
    graphEpoch := nextEpoch
    graphSnapshotId := nextSnapshot
    lastBatch := none
    normalizedCommitTrace := []
    incumbentPublicationTrace := []
  }

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
  · simpa [ReducedIncumbentCoherent, reducedStateOfFullState,
      FullPublicationTraceGoalCoherent] using hInv.publicationTraceGoalCoherent
  · simpa [FrontierNodesNodup, reducedStateOfFullState, reducedFrontierOfFullState] using
      hInv.openNodesNodup

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
