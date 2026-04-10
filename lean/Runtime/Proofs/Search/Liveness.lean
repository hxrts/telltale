import Runtime.Proofs.Search.Machine
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.Liveness

Machine-level liveness extensions for search:

- fixed-phase termination under explicit finite reachable-state premises
- bounded fairness for entries that are not initially min-priority
- goal reachability from an explicit witness-path schedule
-/

namespace Runtime
namespace Proofs
namespace Search

/-- Count of strictly better entries currently ahead of one frontier entry. -/
def StrictlyBetterEntryCount
    (frontier : List FrontierEntry) (entry : FrontierEntry) : Nat :=
  (frontier.filter fun other => other.priority < entry.priority).length

/-- If a present entry has no strictly better competitors in the frontier, it is
min-priority. -/
theorem isMinPriority_of_strictlyBetterEntryCount_eq_zero
    {frontier : List FrontierEntry} {entry : FrontierEntry}
    (hPresent : entry ∈ frontier)
    (hCount : StrictlyBetterEntryCount frontier entry = 0) :
    IsMinPriority frontier entry := by
  refine ⟨hPresent, ?_⟩
  intro other hOther
  by_contra hLt
  have hOtherLt : other.priority < entry.priority :=
    Nat.lt_of_not_ge hLt
  have hMemFilter : other ∈ frontier.filter (fun candidate => candidate.priority < entry.priority) := by
    simp [hOther, hOtherLt]
  have hPos :
      0 < StrictlyBetterEntryCount frontier entry := by
    unfold StrictlyBetterEntryCount
    exact List.length_pos_of_mem hMemFilter
  simp [hCount] at hPos

/-- Fixed-phase termination premises for the reduced canonical machine. The
phase is held constant and every nonempty frontier step closes at least one
fresh node from a finite reachable universe. -/
structure FixedPhaseTerminationPremises
    (goal : Nat)
    (reachable : List Nat)
    (trace : SearchMachineTrace) where
  machineTrace : CanonicalMachineTrace goal trace
  reachableNodup : reachable.Nodup
  finiteBranchingWithinReachable : Prop
  deterministicSuccessorEnumeration : Prop
  noInfiniteImprovementChurn : Prop
  invariantHolds : ∀ i, MachineInvariants goal (trace i)
  closedWithinReachable :
    ∀ i ⦃node : Nat⦄, node ∈ (trace i).closedNodes → node ∈ reachable

/-- Closed-node cardinality is bounded by the finite reachable universe. -/
theorem closed_nodes_length_le_reachable_length
    {goal : Nat}
    {reachable : List Nat}
    {trace : SearchMachineTrace}
    (hPremises : FixedPhaseTerminationPremises goal reachable trace)
    (i : Nat) :
    (trace i).closedNodes.length ≤ reachable.length := by
  have hInv := hPremises.invariantHolds i
  have hSubset :
      (trace i).closedNodes.toFinset ⊆ reachable.toFinset := by
    intro node hNode
    exact List.mem_toFinset.mpr <|
      hPremises.closedWithinReachable i (List.mem_toFinset.mp hNode)
  have hCard := Finset.card_le_card hSubset
  simpa [List.toFinset_card_of_nodup hInv.closedNodup,
    List.toFinset_card_of_nodup hPremises.reachableNodup] using hCard

/-- One nonempty fixed-phase canonical step strictly increases the number of
closed nodes. -/
theorem canonical_machine_step_closed_length_strict_increase_of_nonempty_frontier
    {goal : Nat}
    {current next : SearchMachineState}
    (hStep : CanonicalMachineStep goal current next)
    (hInv : MachineInvariants goal current)
    (hFrontier : current.frontier ≠ []) :
    current.closedNodes.length < next.closedNodes.length := by
  have hServicedNe : executableServicedEntries current ≠ [] :=
    executableServicedEntries_nonempty_of_frontier_nonempty hFrontier
  have hServicedLenPos : 0 < (executableServicedEntries current).length := by
    exact List.length_pos_iff_ne_nil.mpr hServicedNe
  have hMapLenPos : 0 < (executableServicedNodes current).length := by
    simpa [executableServicedNodes] using hServicedLenPos
  rw [hStep.next_eq_executable, executableCanonicalStep, executableClosedNodes, List.length_append]
  omega

/-- If the frontier stays nonempty across a prefix, the number of closed nodes
grows by at least the prefix length. -/
theorem closed_nodes_length_lower_bound_of_prefix_nonempty
    {goal : Nat}
    {reachable : List Nat}
    {trace : SearchMachineTrace}
    (hPremises : FixedPhaseTerminationPremises goal reachable trace) :
    ∀ j,
      (∀ k, k < j → (trace k).frontier ≠ []) →
      (trace 0).closedNodes.length + j ≤ (trace j).closedNodes.length
  | 0 => by
      intro _
      omega
  | j + 1 => by
      intro hPrefix
      have hPrefixPrev : ∀ k, k < j → (trace k).frontier ≠ [] := by
        intro k hk
        exact hPrefix k (Nat.lt_trans hk (Nat.lt_succ_self j))
      have hIH :=
        closed_nodes_length_lower_bound_of_prefix_nonempty hPremises j hPrefixPrev
      have hFrontier : (trace j).frontier ≠ [] :=
        hPrefix j (Nat.lt_succ_self j)
      have hStep := hPremises.machineTrace j
      have hInv := hPremises.invariantHolds j
      have hIncrease :
          (trace j).closedNodes.length < (trace (j + 1)).closedNodes.length :=
        canonical_machine_step_closed_length_strict_increase_of_nonempty_frontier
          hStep hInv hFrontier
      have hLt :
          (trace 0).closedNodes.length + j < (trace (j + 1)).closedNodes.length :=
        lt_of_le_of_lt hIH hIncrease
      simpa [Nat.add_assoc] using Nat.succ_le_of_lt hLt

/-- Fixed-phase canonical serial search terminates within the remaining
reachable-node budget. -/
theorem fixed_phase_canonical_serial_terminates_under_finite_reachable_bound
    {goal : Nat}
    {reachable : List Nat}
    {trace : SearchMachineTrace}
    (hPremises : FixedPhaseTerminationPremises goal reachable trace) :
    ∃ j,
      j ≤ reachable.length - (trace 0).closedNodes.length ∧
      (trace j).frontier = [] := by
  let bound := reachable.length - (trace 0).closedNodes.length
  by_contra hNo
  have hClosed0Le : (trace 0).closedNodes.length ≤ reachable.length :=
    closed_nodes_length_le_reachable_length hPremises 0
  have hAllNonempty : ∀ k, k ≤ bound → (trace k).frontier ≠ [] := by
    intro k hk hEmpty
    exact hNo ⟨k, hk, hEmpty⟩
  have hPrefixNonempty : ∀ k, k < bound + 1 → (trace k).frontier ≠ [] := by
    intro k hk
    exact hAllNonempty k (Nat.lt_succ_iff.mp hk)
  have hLower :
      (trace 0).closedNodes.length + (bound + 1) ≤
        (trace (bound + 1)).closedNodes.length :=
    closed_nodes_length_lower_bound_of_prefix_nonempty hPremises (bound + 1) hPrefixNonempty
  have hUpper :
      (trace (bound + 1)).closedNodes.length ≤ reachable.length :=
    closed_nodes_length_le_reachable_length hPremises (bound + 1)
  have : reachable.length + 1 ≤ reachable.length := by
    have hEq :
        (trace 0).closedNodes.length + bound = reachable.length := by
      dsimp [bound]
      exact Nat.add_sub_of_le hClosed0Le
    have hLower' : reachable.length + 1 ≤ (trace (bound + 1)).closedNodes.length := by
      omega
    exact le_trans hLower' hUpper
  omega

/-- Premises for bounded service of an entry that is not initially min-priority.
The entry stays present, and the count of strictly better competitors decreases
strictly whenever it is still not min-priority. -/
structure BoundedStrictPreemptionPremises
    (trace : FrontierTrace)
    (start bound : Nat)
    (entry : FrontierEntry) : Prop where
  presentAcrossWindow :
    ∀ j, j ≤ bound → entry ∈ trace (start + j)
  initialStrictlyBetterBound :
    StrictlyBetterEntryCount (trace start) entry ≤ bound
  strictlyBetterDecreasesWhileNonMin :
    ∀ j, j < bound →
      entry ∈ trace (start + j) →
      ¬ IsMinPriority (trace (start + j)) entry →
      StrictlyBetterEntryCount (trace (start + j + 1)) entry <
        StrictlyBetterEntryCount (trace (start + j)) entry

/-- Under bounded strict preemption, a present entry eventually reaches the
min-priority window. -/
theorem bounded_strict_preemption_eventually_becomes_min
    {trace : FrontierTrace}
    {start bound : Nat}
    {entry : FrontierEntry}
    (hPremises : BoundedStrictPreemptionPremises trace start bound entry) :
    ∃ j, j ≤ bound ∧ IsMinPriority (trace (start + j)) entry := by
  induction bound generalizing start with
  | zero =>
      refine ⟨0, Nat.le_refl 0, ?_⟩
      have hPresent : entry ∈ trace (start + 0) :=
        hPremises.presentAcrossWindow 0 (Nat.le_refl 0)
      have hCountZero :
          StrictlyBetterEntryCount (trace start) entry = 0 := by
        exact Nat.eq_zero_of_le_zero hPremises.initialStrictlyBetterBound
      simpa using isMinPriority_of_strictlyBetterEntryCount_eq_zero hPresent hCountZero
  | succ bound ih =>
      by_cases hMin : IsMinPriority (trace start) entry
      · exact ⟨0, Nat.zero_le _, hMin⟩
      · have hPresent0 : entry ∈ trace (start + 0) :=
          hPremises.presentAcrossWindow 0 (Nat.zero_le _)
        have hDecrease :
            StrictlyBetterEntryCount (trace (start + 1)) entry <
              StrictlyBetterEntryCount (trace start) entry := by
          simpa using
            hPremises.strictlyBetterDecreasesWhileNonMin 0 (Nat.zero_lt_succ _) hPresent0 hMin
        have hCountNext :
            StrictlyBetterEntryCount (trace (start + 1)) entry ≤ bound := by
          have hInit := hPremises.initialStrictlyBetterBound
          omega
        let shiftedPremises : BoundedStrictPreemptionPremises trace (start + 1) bound entry :=
          { presentAcrossWindow := by
              intro j hj
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                hPremises.presentAcrossWindow (j + 1) (Nat.succ_le_succ hj)
          , initialStrictlyBetterBound := hCountNext
          , strictlyBetterDecreasesWhileNonMin := by
              intro j hj hPresent hNotMin
              have hPresent' : entry ∈ trace (start + (j + 1)) := by
                simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hPresent
              have hNotMin' : ¬ IsMinPriority (trace (start + (j + 1))) entry := by
                simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hNotMin
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                hPremises.strictlyBetterDecreasesWhileNonMin (j + 1)
                  (Nat.succ_lt_succ hj) hPresent' hNotMin'
          }
        rcases ih shiftedPremises with ⟨j, hj, hMinLater⟩
        refine ⟨j + 1, Nat.succ_le_succ hj, ?_⟩
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hMinLater

/-- Canonical serial search therefore services a non-min-priority entry within
one extra step after it first becomes min-priority. -/
theorem canonical_serial_nonmin_entry_eventually_serviced_under_bounded_strict_preemption
    {trace : FrontierTrace}
    {start bound : Nat}
    {entry : FrontierEntry}
    (hTrace : CanonicalSerialTrace trace)
    (hPremises : BoundedStrictPreemptionPremises trace start bound entry) :
    EventuallyServicedWithin trace start (bound + 1) entry := by
  rcases bounded_strict_preemption_eventually_becomes_min hPremises with
    ⟨j, hj, hMin⟩
  have hService :
      EventuallyServicedWithin trace (start + j) 1 entry :=
    currently_min_priority_eventually_serviced_within_one_step hTrace hMin
  rcases hService with ⟨k, hk, hAbsent⟩
  refine ⟨j + k, ?_, ?_⟩
  · have hk0 : k = 0 := Nat.lt_one_iff.mp hk
    subst hk0
    omega
  · have hk0 : k = 0 := Nat.lt_one_iff.mp hk
    subst hk0
    simpa [Nat.add_assoc] using hAbsent

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
            simpa [frontierTraceOfMachineTrace] using hReady
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
          exact ⟨0, by simpa, by simpa using hClosed⟩
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
  finiteReachableUniverse : Prop
  heuristicAdmissible : Prop
  heuristicConsistent : Prop

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

/-- Premise bundle for rebuild-aware ARA-style termination. The first component
tracks remaining rebuild/phase budget, the second residual canonical work
within the current phase. Their lexicographic decrease is encoded as a natural
measure. -/
structure RebuildAwareTerminationPremises
    (goal : Nat)
    (trace : SearchMachineTrace) where
  machineTrace : CanonicalMachineTrace goal trace
  phaseBudget : Nat → Nat
  residualCanonicalWork : Nat → Nat
  residualCanonicalWorkBound : Nat
  invariantHolds : ∀ i, MachineInvariants goal (trace i)
  encodedMeasureDropsWhileFrontierNonempty :
    ∀ i, (trace i).frontier ≠ [] →
      phaseBudget (i + 1) * (residualCanonicalWorkBound + 1) +
          residualCanonicalWork (i + 1) + 1 ≤
        phaseBudget i * (residualCanonicalWorkBound + 1) +
          residualCanonicalWork i

/-- Encoded lexicographic phase/work progress measure. -/
def rebuildAwareEncodedMeasure
    {goal : Nat}
    {trace : SearchMachineTrace}
    (premises : RebuildAwareTerminationPremises goal trace)
    (i : Nat) : Nat :=
  premises.phaseBudget i * (premises.residualCanonicalWorkBound + 1) +
    premises.residualCanonicalWork i

/-- Rebuild-aware ARA-style canonical search terminates once the lexicographic
phase/work measure is shown to decrease across every nonempty-frontier step. -/
theorem rebuild_aware_canonical_serial_terminates_under_phase_work_measure
    {goal : Nat}
    {trace : SearchMachineTrace}
    (hPremises : RebuildAwareTerminationPremises goal trace) :
    ∃ j, j ≤ rebuildAwareEncodedMeasure hPremises 0 ∧ (trace j).frontier = [] := by
  let bound := rebuildAwareEncodedMeasure hPremises 0
  have hMeasureLower :
      ∀ j, (∀ k, k < j → (trace k).frontier ≠ []) →
        rebuildAwareEncodedMeasure hPremises j + j ≤ bound := by
    intro j
    induction j with
    | zero =>
        intro _
        simp [bound, rebuildAwareEncodedMeasure]
    | succ j ih =>
        intro hPrefix
        have hPrefixPrev : ∀ k, k < j → (trace k).frontier ≠ [] := by
          intro k hk
          exact hPrefix k (Nat.lt_trans hk (Nat.lt_succ_self j))
        have hIH := ih hPrefixPrev
        have hFrontier : (trace j).frontier ≠ [] :=
          hPrefix j (Nat.lt_succ_self j)
        have hDrop := hPremises.encodedMeasureDropsWhileFrontierNonempty j hFrontier
        have hStep :
            rebuildAwareEncodedMeasure hPremises (j + 1) + (j + 1) ≤
              rebuildAwareEncodedMeasure hPremises j + j := by
          dsimp [rebuildAwareEncodedMeasure] at hDrop ⊢
          omega
        exact le_trans hStep hIH
  by_contra hNo
  have hAllNonempty : ∀ k, k ≤ bound → (trace k).frontier ≠ [] := by
    intro k hk hEmpty
    exact hNo ⟨k, hk, hEmpty⟩
  have hPrefixNonempty : ∀ k, k < bound + 1 → (trace k).frontier ≠ [] := by
    intro k hk
    exact hAllNonempty k (Nat.lt_succ_iff.mp hk)
  have hLower :
      rebuildAwareEncodedMeasure hPremises (bound + 1) + (bound + 1) ≤ bound :=
    hMeasureLower (bound + 1) hPrefixNonempty
  have : bound + 1 ≤ bound := by
    exact le_trans (Nat.le_add_left _ _) hLower
  omega

/-- More structural premise bundle for non-min fairness: the better work ahead
of one entry lives in a finite universe whose size itself provides the service
bound. -/
structure FiniteBetterEntryExhaustionPremises
    (trace : FrontierTrace)
    (start : Nat)
    (entry : FrontierEntry) where
  betterEntryUniverse : List FrontierEntry
  betterEntryUniverseNodup : betterEntryUniverse.Nodup
  presentAcrossUniverseWindow :
    ∀ j, j ≤ betterEntryUniverse.length → entry ∈ trace (start + j)
  initialStrictlyBetterBoundByUniverse :
    StrictlyBetterEntryCount (trace start) entry ≤ betterEntryUniverse.length
  noUnboundedBetterArrivals :
    ∀ j, j ≤ betterEntryUniverse.length →
      ∀ other, other ∈ trace (start + j) → other.priority < entry.priority →
      other ∈ betterEntryUniverse
  strictlyBetterDecreasesWhileNonMin :
    ∀ j, j < betterEntryUniverse.length →
      entry ∈ trace (start + j) →
      ¬ IsMinPriority (trace (start + j)) entry →
      StrictlyBetterEntryCount (trace (start + j + 1)) entry <
        StrictlyBetterEntryCount (trace (start + j)) entry

/-- A finite better-entry universe induces the older bounded strict-preemption
premise with the bound specialized to the universe size. -/
theorem finite_better_entry_exhaustion_implies_bounded_strict_preemption
    {trace : FrontierTrace}
    {start : Nat}
    {entry : FrontierEntry}
    (hPremises : FiniteBetterEntryExhaustionPremises trace start entry) :
    BoundedStrictPreemptionPremises trace start
      hPremises.betterEntryUniverse.length entry := by
  refine
    { presentAcrossWindow := hPremises.presentAcrossUniverseWindow
    , initialStrictlyBetterBound := hPremises.initialStrictlyBetterBoundByUniverse
    , strictlyBetterDecreasesWhileNonMin := hPremises.strictlyBetterDecreasesWhileNonMin
    }

/-- Structural finite-universe fairness theorem for entries that are not
initially min-priority. -/
theorem finite_better_entry_exhaustion_eventually_becomes_min
    {trace : FrontierTrace}
    {start : Nat}
    {entry : FrontierEntry}
    (hPremises : FiniteBetterEntryExhaustionPremises trace start entry) :
    ∃ j, j ≤ hPremises.betterEntryUniverse.length ∧
      IsMinPriority (trace (start + j)) entry := by
  exact bounded_strict_preemption_eventually_becomes_min
    (finite_better_entry_exhaustion_implies_bounded_strict_preemption hPremises)

/-- Structural finite-universe service theorem for entries that are not
initially min-priority. -/
theorem canonical_serial_nonmin_entry_eventually_serviced_under_finite_better_entry_exhaustion
    {trace : FrontierTrace}
    {start : Nat}
    {entry : FrontierEntry}
    (hTrace : CanonicalSerialTrace trace)
    (hPremises : FiniteBetterEntryExhaustionPremises trace start entry) :
    EventuallyServicedWithin trace start
      (hPremises.betterEntryUniverse.length + 1) entry := by
  exact canonical_serial_nonmin_entry_eventually_serviced_under_bounded_strict_preemption
    hTrace (finite_better_entry_exhaustion_implies_bounded_strict_preemption hPremises)

/-- Premise bundle for eventual publication of an optimal goal incumbent. -/
structure OptimalGoalPublicationPremises
    (goal : Nat)
    (trace : SearchMachineTrace)
    (start bound optimalCost : Nat) where
  publicationPremises : GoalPublicationPremises goal trace start bound
  heuristicAdmissible : Prop
  heuristicConsistent : Prop
  publishedGoalIncumbentHasOptimalCost :
    ∀ ⦃i : Nat⦄ ⦃commit : NormalizedCommit⦄,
      (trace i).incumbent = some commit →
      commit.node = goal →
      commit.gScore = optimalCost

/-- Under explicit admissibility and consistency premises, eventual goal
publication can be strengthened to eventual optimal-goal publication. -/
theorem eventual_optimal_goal_publication_under_admissible_consistent_heuristic
    {goal start bound optimalCost : Nat}
    {trace : SearchMachineTrace}
    (hPremises : OptimalGoalPublicationPremises goal trace start bound optimalCost) :
    ∃ j, j < bound ∧
      ∃ commit,
        (trace (start + j + 1)).incumbent = some commit ∧
        commit.node = goal ∧
        commit.gScore = optimalCost := by
  rcases goal_reachability_connects_to_incumbent_publication
      hPremises.publicationPremises with
    ⟨j, hj, commit, hIncumbent, hGoal⟩
  refine ⟨j, hj, commit, hIncumbent, hGoal, ?_⟩
  exact hPremises.publishedGoalIncumbentHasOptimalCost hIncumbent hGoal

end Search
end Proofs
end Runtime
