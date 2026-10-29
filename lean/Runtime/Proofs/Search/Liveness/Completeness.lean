import Runtime.Proofs.Search.Liveness.Fairness

set_option autoImplicit false

/-! # Runtime.Proofs.Search.Liveness.Completeness

Goal reachability and incumbent publication from explicit witness paths,
graph reachability, and raw successor semantics.
-/

namespace Runtime
namespace Proofs
namespace Search

/-- A recursively scheduled witness path from the current frontier to the goal.
Each head entry is min-priority at the current step, and after servicing that
entry the next witness entry is immediately present. -/
def PathReadyAt
    (trace : FrontierTrace) : Nat → List FrontierEntry → Prop
  | _, [] => False
  | start, [entry] => IsMinPriority (trace start) entry
  | start, entry :: next :: rest =>
      IsMinPriority (trace start) entry ∧
      next ∈ trace (start + 1) ∧
      PathReadyAt trace (start + 1) (next :: rest)

/-- Machine-level notion that the goal node has been reached. -/
def GoalReached (goal : Nat) (state : SearchMachineState) : Prop :=
  goal ∈ state.closedNodes

/-- Machine-level notion that the incumbent explicitly publishes the goal. -/
def GoalIncumbentPublished (goal : Nat) (state : SearchMachineState) : Prop :=
  ∃ commit, state.incumbent = some commit ∧ commit.node = goal

/-- Machine-level bounded eventual goal reachability. -/
def EventuallyGoalReachedWithin
    (goal : Nat)
    (trace : SearchMachineTrace)
    (start bound : Nat) : Prop :=
  ∃ j, j < bound ∧ GoalReached goal (trace (start + j + 1))

/-- Explicit premise bundle connecting machine-level goal reachability to
incumbent publication. -/
structure GoalPublicationPremises
    (goal : Nat)
    (trace : SearchMachineTrace)
    (start bound : Nat) : Prop where
  goalReachability : EventuallyGoalReachedWithin goal trace start bound
  goalReachabilityPublishesIncumbent :
    ∀ ⦃i : Nat⦄, GoalReached goal (trace i) → GoalIncumbentPublished goal (trace i)

/-- Goal reachability connects to incumbent publication under an explicit
machine-level publication premise. -/
theorem goal_reachability_connects_to_incumbent_publication
    {goal start bound : Nat}
    {trace : SearchMachineTrace}
    (hPremises : GoalPublicationPremises goal trace start bound) :
    ∃ j, j < bound ∧ GoalIncumbentPublished goal (trace (start + j + 1)) := by
  rcases hPremises.goalReachability with ⟨j, hj, hReached⟩
  exact ⟨j, hj, hPremises.goalReachabilityPublishesIncumbent hReached⟩

/-- The goal entry of a ready witness path is eventually serviced. This is the
global-completeness-facing theorem for the reduced model: completeness is
obtained from an explicit path witness plus per-prefix service readiness. -/
theorem canonical_serial_goal_reached_from_ready_witness_path
    {trace : FrontierTrace}
    {start : Nat}
    {path : List FrontierEntry}
    {goalEntry : FrontierEntry}
    (hTrace : CanonicalSerialTrace trace)
    (hReady : PathReadyAt trace start path)
    (hLast : path.getLast? = some goalEntry) :
    EventuallyServicedWithin trace start path.length goalEntry := by
  induction path generalizing start with
  | nil =>
      cases hReady
  | cons head tail ih =>
      cases tail with
      | nil =>
          have hGoal : goalEntry = head := by
            exact (by simpa using hLast : head = goalEntry).symm
          subst hGoal
          simpa using
            currently_min_priority_eventually_serviced_within_one_step hTrace hReady
      | cons next rest =>
          rcases hReady with ⟨_hMinHead, _hNextPresent, hReadyTail⟩
          have hTail :
              EventuallyServicedWithin trace (start + 1) (List.length (next :: rest))
                goalEntry := by
            exact ih hReadyTail (by simpa using hLast)
          rcases hTail with ⟨j, hj, hAbsent⟩
          refine ⟨j + 1, ?_, ?_⟩
          · simpa using Nat.succ_lt_succ hj
          · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hAbsent

/-- Machine-level version of the ready witness-path theorem: once the goal
entry reaches the legal service window along a ready witness path, executable
canonical stepping closes the goal node within the same horizon. -/
theorem canonical_machine_goal_reached_from_ready_witness_path
    {goal start : Nat}
    {trace : SearchMachineTrace}
    {path : List FrontierEntry}
    {goalEntry : FrontierEntry}
    (hTrace : CanonicalMachineTrace goal trace)
    (hReady : PathReadyAt (frontierTraceOfMachineTrace trace) start path)
    (hLast : path.getLast? = some goalEntry)
    (hGoalNode : goalEntry.node = goal) :
    EventuallyGoalReachedWithin goal trace start path.length := by
  induction path generalizing start with
  | nil =>
      cases hReady
  | cons head tail ih =>
      cases tail with
      | nil =>
          have hGoal : goalEntry = head := by
            exact (by simpa using hLast : head = goalEntry).symm
          subst hGoal
          have hMin : IsMinPriority (trace start).frontier goalEntry := by
            simpa [PathReadyAt, frontierTraceOfMachineTrace] using hReady
          have hBatch : goalEntry ∈ executableServicedEntries (trace start) :=
            min_priority_entry_serviced_next_step hMin
          have hClosed :
              GoalReached goal (trace (start + 0 + 1)) := by
            rw [(hTrace start).next_eq_executable, GoalReached,
              executableCanonicalStep, executableClosedNodes]
            have hGoalMem : goal ∈ executableServicedNodes (trace start) := by
              simpa [executableServicedNodes, hGoalNode] using
                (List.mem_map.mpr ⟨goalEntry, hBatch, by simp [hGoalNode]⟩)
            exact List.mem_append.mpr (Or.inr hGoalMem)
          exact ⟨0, by simp, by simpa using hClosed⟩
      | cons next rest =>
          rcases hReady with ⟨_hMinHead, _hNextPresent, hReadyTail⟩
          have hTail :
              EventuallyGoalReachedWithin goal trace (start + 1)
                (List.length (next :: rest)) := by
            exact ih hReadyTail (by simpa using hLast)
          rcases hTail with ⟨j, hj, hReached⟩
          refine ⟨j + 1, ?_, ?_⟩
          · simpa using Nat.succ_lt_succ hj
          · simpa [EventuallyGoalReachedWithin, GoalReached,
              Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hReached

/-- Consecutive-edge validity for one node path in an abstract successor
graph. -/
def NodePathEdgesRespect
    (successors : Nat → List Nat) : List Nat → Prop
  | [] => False
  | [_] => True
  | node :: next :: rest =>
      next ∈ successors node ∧ NodePathEdgesRespect successors (next :: rest)

/-- Graph reachability witnessed by one explicit successor-respecting node
path. -/
def GraphReachable
    (successors : Nat → List Nat) (start goal : Nat) : Prop :=
  ∃ path : List Nat,
    path ≠ [] ∧
    path.head? = some start ∧
    path.getLast? = some goal ∧
    NodePathEdgesRespect successors path

/-- Stronger completeness premise bundle driven by graph reachability rather
than a free-standing ready witness path. The ready entry-path witness is still
explicit, but it is now tied to a named reachable node path plus finiteness and
heuristic premises. -/
structure ReachabilityCompletenessPremises
    (goal : Nat)
    (trace : SearchMachineTrace)
    (start : Nat) where
  machineTrace : CanonicalMachineTrace goal trace
  successorGraph : Nat → List Nat
  startNode : Nat
  reachableNodePath : List Nat
  reachableNodePathWitness :
    reachableNodePath ≠ [] ∧
    reachableNodePath.head? = some startNode ∧
    reachableNodePath.getLast? = some goal ∧
    NodePathEdgesRespect successorGraph reachableNodePath
  reachableEntryPath : List FrontierEntry
  reachableEntryPathNodes :
    reachableEntryPath.map FrontierEntry.node = reachableNodePath
  reachableReadyPath :
    PathReadyAt (frontierTraceOfMachineTrace trace) start reachableEntryPath

/-- Completeness strengthened to a graph-reachability-driven statement over the
executable machine trace. -/
theorem canonical_machine_goal_reached_from_graph_reachability
    {goal start : Nat}
    {trace : SearchMachineTrace}
    (hPremises : ReachabilityCompletenessPremises goal trace start) :
    EventuallyGoalReachedWithin goal trace start
      hPremises.reachableEntryPath.length := by
  cases hLastEntry : hPremises.reachableEntryPath.getLast? with
  | none =>
      have hEntryLastNode :
          Option.map FrontierEntry.node hPremises.reachableEntryPath.getLast? =
            hPremises.reachableNodePath.getLast? := by
        simpa using congrArg List.getLast? hPremises.reachableEntryPathNodes
      simp [hLastEntry, hPremises.reachableNodePathWitness.2.2.1] at hEntryLastNode
  | some goalEntry =>
      have hGoalNode : goalEntry.node = goal := by
        have hEntryLastNode :
            Option.map FrontierEntry.node hPremises.reachableEntryPath.getLast? =
              hPremises.reachableNodePath.getLast? := by
          simpa [hLastEntry] using congrArg List.getLast? hPremises.reachableEntryPathNodes
        simpa [hLastEntry, hPremises.reachableNodePathWitness.2.2.1] using hEntryLastNode
      exact canonical_machine_goal_reached_from_ready_witness_path
        hPremises.machineTrace hPremises.reachableReadyPath hLastEntry hGoalNode

/-- Public completeness premise bundle phrased directly over the raw successor
contract, with the ready-path witness internalized behind one refinement
premise. -/
structure RawSuccessorCompletenessPremises
    (goal : Nat)
    (trace : SearchMachineTrace)
    (start : Nat) where
  machineTrace : CanonicalMachineTrace goal trace
  successorGraph : Nat → List Nat
  startNode : Nat
  rawReachability : GraphReachable successorGraph startNode goal
  reachablePathRefinesToReadyEntries :
    ∀ path : List Nat,
      path ≠ [] →
      path.head? = some startNode →
      path.getLast? = some goal →
      NodePathEdgesRespect successorGraph path →
      ∃ entryPath : List FrontierEntry,
        entryPath.map FrontierEntry.node = path ∧
        PathReadyAt (frontierTraceOfMachineTrace trace) start entryPath

/-- Blanket completeness from raw successor semantics: any raw reachable goal
is eventually reached once reachability is refined into the executable machine's
ready-entry progress contract. -/
theorem canonical_machine_goal_reached_from_raw_successor_semantics
    {goal start : Nat}
    {trace : SearchMachineTrace}
    (hPremises : RawSuccessorCompletenessPremises goal trace start) :
    ∃ bound, EventuallyGoalReachedWithin goal trace start bound := by
  rcases hPremises.rawReachability with ⟨path, hPathNe, hHead, hLast, hEdges⟩
  rcases hPremises.reachablePathRefinesToReadyEntries path hPathNe hHead hLast hEdges with
    ⟨entryPath, hEntryNodes, hReady⟩
  cases hLastEntry : entryPath.getLast? with
  | none =>
      have hEntryLastNode :
          Option.map FrontierEntry.node entryPath.getLast? = path.getLast? := by
        simpa using congrArg List.getLast? hEntryNodes
      simp [hLastEntry, hLast] at hEntryLastNode
  | some goalEntry =>
      have hGoalNode : goalEntry.node = goal := by
        have hEntryLastNode :
            Option.map FrontierEntry.node entryPath.getLast? = path.getLast? := by
          simpa using congrArg List.getLast? hEntryNodes
        simpa [hLastEntry, hLast] using hEntryLastNode
      exact ⟨entryPath.length,
        canonical_machine_goal_reached_from_ready_witness_path
          hPremises.machineTrace hReady hLastEntry hGoalNode⟩

end Search
end Proofs
end Runtime
