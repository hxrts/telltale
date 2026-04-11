import Runtime.Proofs.Search.Core
import Runtime.Proofs.Search.Fairness
import Mathlib.Data.List.Nodup

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.Executable

Executable reduced machine semantics for the search proof lane.

This module upgrades the earlier frontier-only view into a concrete reduced
machine step with explicit state projections back to the Rust-facing reduced
artifact vocabulary.
-/

namespace Runtime
namespace Proofs
namespace Search

/-- Reduced parent witness used by machine-facing invariants. -/
structure ReducedParentRecord where
  node : Nat
  parent : Nat
  edgeCost : Nat
  deriving DecidableEq, Repr

/-- Reduced machine state aligned with the proof-relevant Rust search state. -/
structure SearchMachineState where
  frontier : List FrontierEntry
  closedNodes : List Nat
  inconsNodes : List Nat
  gScores : List (Nat × Nat)
  parentRecords : List ReducedParentRecord
  incumbent : Option NormalizedCommit
  phase : Nat
  productiveSteps : Nat
  totalSchedulerSteps : Nat
  deriving DecidableEq, Repr

/-- No frontier node is already closed. -/
def OpenClosedDisjoint (state : SearchMachineState) : Prop :=
  ∀ ⦃entry : FrontierEntry⦄, entry ∈ state.frontier → entry.node ∉ state.closedNodes

/-- Every inconsistent node is already closed. -/
def InconsSubsetClosed (state : SearchMachineState) : Prop :=
  ∀ ⦃node : Nat⦄, node ∈ state.inconsNodes → node ∈ state.closedNodes

/-- Reduced parent-score coherence: parent and child scores exist and agree with
the recorded edge cost. -/
def ReducedParentScoreCoherent (state : SearchMachineState) : Prop :=
  ∀ ⦃record : ReducedParentRecord⦄,
    record ∈ state.parentRecords →
      ∃ parentScore childScore,
        (record.parent, parentScore) ∈ state.gScores ∧
        (record.node, childScore) ∈ state.gScores ∧
        childScore = parentScore + record.edgeCost

/-- Reduced incumbent coherence: the incumbent points at the distinguished goal
node and matches the recorded score table. -/
def ReducedIncumbentCoherent (goal : Nat) (state : SearchMachineState) : Prop :=
  match state.incumbent with
  | none => True
  | some commit =>
      commit.node = goal ∧ (goal, commit.gScore) ∈ state.gScores

/-- Frontier nodes are unique, mirroring the Rust `open : BTreeMap`. -/
def FrontierNodesNodup (state : SearchMachineState) : Prop :=
  (state.frontier.map FrontierEntry.node).Nodup

/-- Closed nodes are unique. -/
def ClosedNodesNodup (state : SearchMachineState) : Prop :=
  state.closedNodes.Nodup

/-- Reduced machine invariant bundle aligned with the Rust machine checks. -/
structure MachineInvariants (goal : Nat) (state : SearchMachineState) : Prop where
  openClosedDisjoint : OpenClosedDisjoint state
  inconsSubsetClosed : InconsSubsetClosed state
  parentScoreCoherent : ReducedParentScoreCoherent state
  incumbentCoherent : ReducedIncumbentCoherent goal state
  frontierNodup : FrontierNodesNodup state
  closedNodup : ClosedNodesNodup state

/-- Machine trace specialized to reduced machine states. -/
abbrev SearchMachineTrace := Nat → SearchMachineState

/-- Frontier projection from a machine trace. -/
def frontierTraceOfMachineTrace (trace : SearchMachineTrace) : FrontierTrace :=
  fun i => (trace i).frontier

/-- Executable current canonical batch. -/
def executableServicedEntries (state : SearchMachineState) : List FrontierEntry :=
  canonicalBatch state.frontier

/-- Executable serviced node list. -/
def executableServicedNodes (state : SearchMachineState) : List Nat :=
  (executableServicedEntries state).map FrontierEntry.node

/-- Executable normalized proposal commits for one reduced step. -/
def executableNormalizedCommits (state : SearchMachineState) : List NormalizedCommit :=
  canonicalNormalizedCommitTrace state.frontier

/-- Executable frontier removal for one reduced canonical step. -/
def executableNextFrontier (state : SearchMachineState) : List FrontierEntry :=
  frontierAfterCanonicalStep state.frontier

/-- Executable reduced parent updates. The reduced semantics preserves the
existing parent witness set because canonical-batch extraction alone does not
recover the parent-edge witness. -/
def executableParentUpdates (state : SearchMachineState) : List ReducedParentRecord :=
  state.parentRecords

/-- Executable reduced `g`-score updates extracted from normalized commits. -/
def executableGScoreUpdates (state : SearchMachineState) : List (Nat × Nat) :=
  (executableNormalizedCommits state).map fun commit => (commit.node, commit.gScore)

/-- Executable reduced closed-set movement. -/
def executableClosedNodes (state : SearchMachineState) : List Nat :=
  state.closedNodes ++ executableServicedNodes state

/-- Executable reduced `incons` movement. Serviced nodes are no longer tracked
as inconsistent after they are closed. -/
def executableInconsNodes (state : SearchMachineState) : List Nat :=
  state.inconsNodes.filter fun node => node ∉ executableServicedNodes state

/-- Candidate goal commits available for reduced incumbent refresh. -/
def executableGoalCommitCandidates
    (goal : Nat) (state : SearchMachineState) : List NormalizedCommit :=
  (executableNormalizedCommits state).filter fun commit => commit.node = goal

/-- Executable reduced incumbent refresh. If no incumbent is currently
published, a goal commit in the current normalized commit list becomes the new
reduced incumbent. -/
def executableRefreshedIncumbent
    (goal : Nat) (state : SearchMachineState) : Option NormalizedCommit :=
  match state.incumbent with
  | some incumbent => some incumbent
  | none => (executableGoalCommitCandidates goal state).head?

/-- Executable reduced canonical step. -/
def executableCanonicalStep
    (goal : Nat) (state : SearchMachineState) : SearchMachineState :=
  { frontier := executableNextFrontier state
  , closedNodes := executableClosedNodes state
  , inconsNodes := executableInconsNodes state
  , gScores := state.gScores ++ executableGScoreUpdates state
  , parentRecords := executableParentUpdates state
  , incumbent := executableRefreshedIncumbent goal state
  , phase := state.phase
  , productiveSteps := state.productiveSteps + if (executableNormalizedCommits state).isEmpty then 0 else 1
  , totalSchedulerSteps := state.totalSchedulerSteps + 1
  }

/-- Executable machine trace: every step is the reduced canonical machine
function. -/
abbrev ExecutableCanonicalMachineTrace (goal : Nat) (trace : SearchMachineTrace) : Prop :=
  ∀ i, trace (i + 1) = executableCanonicalStep goal (trace i)

/-- Reduced step artifact induced by the executable machine step. -/
def executableStepArtifact (goal : Nat) (state : SearchMachineState) : StepArtifact :=
  { batchNodes := executableServicedNodes state
  , normalizedCommits := executableNormalizedCommits state
  , nextFrontier := (executableCanonicalStep goal state).frontier
  }

/-- Reduced authoritative state-slice projection from one executable machine
state. This is the explicit Rust-facing reduced extraction boundary for the
machine semantics. -/
def stateSliceOfMachineState (state : SearchMachineState) : StateSlice :=
  { frontier := state.frontier
  , openNodes := state.frontier.map FrontierEntry.node
  , closedNodes := state.closedNodes
  , parentMap := state.parentRecords.map fun record => (record.node, some record.parent)
  , gScores := state.gScores
  , incumbent := state.incumbent
  , epoch := 0
  , phase := state.phase
  }

/-- Reduced observable-slice projection from one executable machine state. -/
def observationSliceOfMachineState (state : SearchMachineState) : ObservationSlice :=
  { incumbentCost := state.incumbent.map NormalizedCommit.gScore
  , incumbentNode := state.incumbent.map NormalizedCommit.node
  , normalizedCommits := executableNormalizedCommits state
  , productiveSteps := state.productiveSteps
  , totalSchedulerSteps := state.totalSchedulerSteps
  }

/-- Reduced exported runtime-state artifact induced by one executable machine
state. -/
def stateArtifactOfMachineState (state : SearchMachineState) : StateArtifactSchema :=
  stateArtifactOfStateSlice (stateSliceOfMachineState state)

/-- Helper: a `head? = some x` witness gives list membership. -/
theorem mem_of_head?_eq_some
    {α : Type} {xs : List α} {x : α}
    (hHead : xs.head? = some x) :
    x ∈ xs := by
  cases xs with
  | nil =>
      simp at hHead
  | cons hd tl =>
      simp at hHead
      simp [hHead]

/-- Helper: executable serviced entries are a frontier sublist. -/
theorem executableServicedEntries_sublist_frontier
    (state : SearchMachineState) :
    List.Sublist (executableServicedEntries state) state.frontier := by
  unfold executableServicedEntries canonicalBatch
  exact List.filter_sublist

/-- Helper: executable serviced nodes form a sublist of the frontier node list. -/
theorem executableServicedNodes_sublist_frontierNodes
    (state : SearchMachineState) :
    List.Sublist (executableServicedNodes state) (state.frontier.map FrontierEntry.node) := by
  simpa [executableServicedNodes] using
    (executableServicedEntries_sublist_frontier state).map FrontierEntry.node

/-- Executable next frontier remains a frontier sublist. -/
theorem executableNextFrontier_sublist_frontier
    (state : SearchMachineState) :
    List.Sublist (executableNextFrontier state) state.frontier := by
  unfold executableNextFrontier frontierAfterCanonicalStep
  exact List.filter_sublist

/-- Executable next-frontier nodes remain a sublist of frontier nodes. -/
theorem executableNextFrontierNodes_sublist_frontierNodes
    (state : SearchMachineState) :
    List.Sublist ((executableNextFrontier state).map FrontierEntry.node)
      (state.frontier.map FrontierEntry.node) := by
  simpa using (executableNextFrontier_sublist_frontier state).map FrontierEntry.node

/-- Executable serviced nodes remain nodup under the frontier nodup invariant. -/
theorem executableServicedNodes_nodup
    {goal : Nat} {state : SearchMachineState}
    (hInv : MachineInvariants goal state) :
    (executableServicedNodes state).Nodup := by
  exact hInv.frontierNodup.sublist (executableServicedNodes_sublist_frontierNodes state)

/-- Helper: normalized-commit membership yields the corresponding score update. -/
theorem mem_executableGScoreUpdates_of_mem_normalizedCommits
    {state : SearchMachineState}
    {commit : NormalizedCommit}
    (hCommit : commit ∈ executableNormalizedCommits state) :
    (commit.node, commit.gScore) ∈ executableGScoreUpdates state := by
  unfold executableGScoreUpdates
  exact List.mem_map.mpr ⟨commit, hCommit, by simp⟩

/-- Every nonempty frontier contains a min-priority entry. -/
theorem exists_minPriority_of_frontier_ne_nil
    {frontier : List FrontierEntry}
    (hFrontier : frontier ≠ []) :
    ∃ entry, IsMinPriority frontier entry := by
  induction frontier with
  | nil =>
      contradiction
  | cons head tail ih =>
      cases tail with
      | nil =>
          refine ⟨head, ?_⟩
          simp [IsMinPriority]
      | cons next rest =>
          have hTailNe : next :: rest ≠ [] := by simp
          rcases ih hTailNe with ⟨tailMin, hTailMin⟩
          rcases hTailMin with ⟨hTailPresent, hTailLeast⟩
          by_cases hHeadLeast : head.priority ≤ tailMin.priority
          · refine ⟨head, ?_⟩
            refine ⟨by simp, ?_⟩
            intro other hOther
            rcases List.mem_cons.mp hOther with rfl | hOtherTail
            · exact Nat.le_refl _
            · exact le_trans hHeadLeast (hTailLeast other hOtherTail)
          · refine ⟨tailMin, ?_⟩
            refine ⟨by simp [hTailPresent], ?_⟩
            intro other hOther
            rcases List.mem_cons.mp hOther with rfl | hOtherTail
            · exact Nat.le_of_lt (Nat.lt_of_not_ge hHeadLeast)
            · exact hTailLeast other hOtherTail

/-- The executable serviced batch is nonempty whenever the frontier is
nonempty. -/
theorem executableServicedEntries_nonempty_of_frontier_nonempty
    {state : SearchMachineState}
    (hFrontier : state.frontier ≠ []) :
    executableServicedEntries state ≠ [] := by
  rcases exists_minPriority_of_frontier_ne_nil hFrontier with ⟨entry, hMin⟩
  have hBatch : entry ∈ executableServicedEntries state := by
    exact min_priority_entry_serviced_next_step hMin
  exact List.ne_nil_of_mem hBatch

/-- The reduced step artifact induced by executable stepping agrees exactly
with the frontier-facing reduced step artifact vocabulary. -/
theorem executable_step_artifact_refines_canonical_step_artifact
    (goal : Nat) (state : SearchMachineState) :
    executableStepArtifact goal state = canonicalStepArtifact state.frontier := by
  rfl

/-- The executable state-artifact extraction is definitionally the runtime
state-artifact projection of the executable machine state. -/
theorem runtime_state_artifact_of_machine_state_is_projection
    (state : SearchMachineState) :
    stateArtifactOfMachineState state =
      stateArtifactOfStateSlice (stateSliceOfMachineState state) :=
  rfl

/-- Executable canonical stepping preserves the reduced machine invariants. -/
theorem executable_canonical_step_preserves_invariants
    {goal : Nat}
    {state : SearchMachineState}
    (hInv : MachineInvariants goal state) :
    MachineInvariants goal (executableCanonicalStep goal state) := by
  refine
    { openClosedDisjoint := ?_
    , inconsSubsetClosed := ?_
    , parentScoreCoherent := ?_
    , incumbentCoherent := ?_
    , frontierNodup := ?_
    , closedNodup := ?_
    }
  · intro entry hEntryNext hClosedNext
    have hEntryNext' : entry ∈ state.frontier ∧ entry ∉ canonicalBatch state.frontier := by
      simpa [executableCanonicalStep, executableNextFrontier, frontierAfterCanonicalStep] using
        (show entry ∈ executableNextFrontier state from hEntryNext)
    have hEntryCur : entry ∈ state.frontier := hEntryNext'.1
    have hNotServiced : entry ∉ executableServicedEntries state := by
      simpa [executableServicedEntries] using hEntryNext'.2
    have hClosedNext' : entry.node ∈ executableClosedNodes state := by
      simpa [executableCanonicalStep, executableClosedNodes] using hClosedNext
    rcases List.mem_append.mp hClosedNext' with hClosedOld | hClosedServiced
    · exact hInv.openClosedDisjoint hEntryCur hClosedOld
    · rcases List.mem_map.mp hClosedServiced with ⟨serviced, hServicedMem, hNodeEq⟩
      have hServicedFrontier : serviced ∈ state.frontier := by
        exact (List.mem_filter.mp hServicedMem).1
      have hInj :=
        List.inj_on_of_nodup_map hInv.frontierNodup hEntryCur hServicedFrontier hNodeEq.symm
      exact hNotServiced (hInj ▸ hServicedMem)
  · intro node hNodeIncons
    have hNodeCur : node ∈ state.inconsNodes := by
      exact (List.mem_filter.mp hNodeIncons).1
    have hNodeClosedCur : node ∈ state.closedNodes :=
      hInv.inconsSubsetClosed hNodeCur
    exact List.mem_append.mpr (Or.inl hNodeClosedCur)
  · intro record hRecord
    have hRecordCur : record ∈ state.parentRecords := by
      simpa [executableCanonicalStep, executableParentUpdates] using hRecord
    rcases hInv.parentScoreCoherent hRecordCur with
      ⟨parentScore, childScore, hParentScore, hChildScore, hEq⟩
    refine ⟨parentScore, childScore, ?_, ?_, hEq⟩
    · exact List.mem_append.mpr (Or.inl hParentScore)
    · exact List.mem_append.mpr (Or.inl hChildScore)
  · unfold ReducedIncumbentCoherent executableCanonicalStep executableRefreshedIncumbent
    cases hInc : state.incumbent with
    | some incumbent =>
        have hCoherent : incumbent.node = goal ∧ (goal, incumbent.gScore) ∈ state.gScores := by
          simpa [ReducedIncumbentCoherent, hInc] using hInv.incumbentCoherent
        rcases hCoherent with ⟨hNode, hScore⟩
        exact ⟨hNode, List.mem_append.mpr (Or.inl hScore)⟩
    | none =>
        dsimp
        cases hHead : (executableGoalCommitCandidates goal state).head? with
        | none =>
            trivial
        | some commit =>
            have hCommitMemGoalCandidates :
                commit ∈ executableGoalCommitCandidates goal state :=
              mem_of_head?_eq_some hHead
            have hCommitMemNormalized :
                commit ∈ executableNormalizedCommits state := by
              exact (List.mem_filter.mp hCommitMemGoalCandidates).1
            have hCommitGoal : commit.node = goal := by
              simpa using (List.mem_filter.mp hCommitMemGoalCandidates).2
            refine ⟨hCommitGoal, ?_⟩
            simpa [hCommitGoal] using
              (List.mem_append.mpr <|
                Or.inr (mem_executableGScoreUpdates_of_mem_normalizedCommits hCommitMemNormalized))
  · simpa [executableCanonicalStep, executableNextFrontier] using
      hInv.frontierNodup.sublist (executableNextFrontierNodes_sublist_frontierNodes state)
  · have hFresh :
        ∀ ⦃node : Nat⦄, node ∈ executableServicedNodes state → node ∉ state.closedNodes := by
        intro node hNode hClosed
        rcases List.mem_map.mp hNode with ⟨entry, hEntry, rfl⟩
        exact hInv.openClosedDisjoint (List.mem_filter.mp hEntry).1 hClosed
    have hDisjoint : List.Disjoint state.closedNodes (executableServicedNodes state) := by
      rw [List.disjoint_iff_ne]
      intro a hClosed b hServiced hEq
      subst hEq
      exact hFresh hServiced hClosed
    exact hInv.closedNodup.append (executableServicedNodes_nodup hInv) hDisjoint

end Search
end Proofs
end Runtime
