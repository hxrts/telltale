import Runtime.Proofs.Search.Executable
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Nodup

/-! # Runtime.Proofs.Search.FullMachineCorennFull search-machine state and step definitions underlying `Runtime.Proofs.Search.FullMachine`. -/

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.FullMachine

Executable fuller-machine search semantics over a natural-number domain.

This module deliberately stops short of claiming full Rust↔Lean refinement.
Its role is to model the missing transition families that the reduced lane does
not represent: proposal generation, normalization, commit, rebuild, and epoch
reconfiguration.

LONG_FILE_JUSTIFICATION: The full-machine semantics are intentionally kept in a
single executable document so the expanded state, invariant bundle, and reduced
refinement theorems stay visibly aligned.
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

end Search
end Proofs
end Runtime
