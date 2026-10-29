import Runtime.Proofs.Search.Machine
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option autoImplicit false

/-! # Runtime.Proofs.Search.Liveness.Termination

Fixed-phase and rebuild-aware termination of canonical serial search under
explicit finite reachable-state / lexicographic measure premises.
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

end Search
end Proofs
end Runtime
