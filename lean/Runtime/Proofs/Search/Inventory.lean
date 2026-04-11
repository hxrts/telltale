import Runtime.Proofs.Search.Liveness
import Runtime.Proofs.Search.FullMachine
import Runtime.Proofs.Search.Envelope
import Runtime.Proofs.Search.Approximation

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.Inventory

Machine-readable inventory for the current search theorem surface.
-/

namespace Runtime
namespace Proofs
namespace Search

/-- Classification for one theorem in the release-facing search theorem pack. -/
inductive SearchTheoremSupportClass where
  | executableSemantics
  | refinementCorollary
  | premiseScoped
  deriving DecidableEq, Repr

/-- Whether one theorem is generic-machine or problem-class-specific. -/
inductive SearchTheoremProblemClass where
  | genericMachine
  | genericSelectedResult
  | pathProblemSpecific
  deriving DecidableEq, Repr

/-- One detailed theorem-inventory row. -/
structure SearchTheoremInventoryRow where
  name : String
  present : Bool
  supportClass : SearchTheoremSupportClass
  deriving Repr

/-- Detailed search theorem inventory with explicit support classification. -/
def fairnessTheoremInventoryRows : List SearchTheoremInventoryRow :=
  [ { name := "search_canonical_serial_exact_one_step_fairness"
    , present := true
    , supportClass := .executableSemantics
    }
  , { name := "search_full_state_artifact_of_full_state_is_runtime_projection"
    , present := true
    , supportClass := .executableSemantics
    }
  , { name := "search_reduced_state_of_full_state_preserves_machine_invariants"
    , present := true
    , supportClass := .refinementCorollary
    }
  , { name := "search_full_activate_batch_preserves_invariants"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_full_apply_proposal_preserves_invariants"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_full_commit_proposals_preserves_invariants"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_full_decrease_epsilon_and_rebuild_preserves_invariants"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_full_commit_epoch_reconfiguration_preserves_invariants"
    , present := true
    , supportClass := .executableSemantics
    }
  , { name := "search_full_step_once_preserves_invariants"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_full_activate_batch_refines_reduced_service_window"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_full_step_once_refines_reduced_executable_step"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_canonical_serial_dynamic_liveness_under_stability"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_executable_canonical_step_preserves_invariants"
    , present := true
    , supportClass := .executableSemantics
    }
  , { name := "search_executable_trace_refines_canonical_machine_trace"
    , present := true
    , supportClass := .refinementCorollary
    }
  , { name := "search_executable_step_artifact_refines_canonical_step_artifact"
    , present := true
    , supportClass := .refinementCorollary
    }
  , { name := "search_canonical_machine_step_preserves_invariants"
    , present := true
    , supportClass := .executableSemantics
    }
  , { name := "search_canonical_machine_trace_currently_min_priority_eventually_serviced"
    , present := true
    , supportClass := .executableSemantics
    }
  , { name := "search_canonical_machine_step_artifact_refines_runtime_boundary"
    , present := true
    , supportClass := .refinementCorollary
    }
  , { name := "search_canonical_machine_state_artifact_is_runtime_projection"
    , present := true
    , supportClass := .refinementCorollary
    }
  , { name := "search_fixed_phase_canonical_serial_terminates_under_finite_reachable_bound"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_rebuild_aware_canonical_serial_terminates_under_phase_work_measure"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_bounded_strict_preemption_eventually_becomes_min"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_canonical_serial_nonmin_entry_eventually_serviced_under_bounded_strict_preemption"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_finite_better_entry_exhaustion_eventually_becomes_min"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_canonical_serial_nonmin_entry_eventually_serviced_under_finite_better_entry_exhaustion"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_canonical_serial_nonmin_entry_eventually_serviced_under_scheduler_fairness"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_canonical_serial_goal_reached_from_ready_witness_path"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_canonical_machine_goal_reached_from_ready_witness_path"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_canonical_machine_goal_reached_from_graph_reachability"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_canonical_machine_goal_reached_from_raw_successor_semantics"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_goal_reachability_connects_to_incumbent_publication"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_eventual_optimal_goal_publication_under_admissible_consistent_heuristic"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_threaded_exact_single_lane_refines_canonical_one_step"
    , present := true
    , supportClass := .refinementCorollary
    }
  , { name := "search_threaded_exact_single_lane_commit_trace_refines_canonical"
    , present := true
    , supportClass := .refinementCorollary
    }
  , { name := "search_threaded_exact_single_lane_state_slice_refines_canonical"
    , present := true
    , supportClass := .refinementCorollary
    }
  , { name := "search_threaded_exact_single_lane_observation_slice_refines_canonical"
    , present := true
    , supportClass := .refinementCorollary
    }
  , { name := "search_threaded_exact_single_lane_observation_equivalent_to_canonical"
    , present := true
    , supportClass := .refinementCorollary
    }
  , { name := "search_threaded_exact_single_lane_multi_step_state_trace_refines_canonical"
    , present := true
    , supportClass := .refinementCorollary
    }
  , { name := "search_threaded_exact_single_lane_multi_step_observation_trace_refines_canonical"
    , present := true
    , supportClass := .refinementCorollary
    }
  , { name := "search_threaded_exact_single_lane_state_artifact_refines_canonical"
    , present := true
    , supportClass := .refinementCorollary
    }
  , { name := "search_threaded_exact_single_lane_multi_step_state_artifact_trace_refines_canonical"
    , present := true
    , supportClass := .refinementCorollary
    }
  , { name := "search_threaded_exact_single_lane_exact_one_step_fairness"
    , present := true
    , supportClass := .refinementCorollary
    }
  , { name := "search_canonical_serial_goal_window_service_has_exact_suffix_bound"
    , present := true
    , supportClass := .executableSemantics
    }
  , { name := "search_threaded_exact_single_lane_goal_window_service_has_exact_suffix_bound"
    , present := true
    , supportClass := .refinementCorollary
    }
  , { name := "search_batched_parallel_exact_certified_window_fairness"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_batched_parallel_exact_bounded_dynamic_starvation_freedom"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_batched_parallel_exact_certified_window_trace_valid"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_batched_parallel_envelope_claim_is_certified_window_bounded"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_batched_parallel_envelope_certified_window_fairness"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_batched_parallel_envelope_certified_window_trace_valid"
    , present := true
    , supportClass := .premiseScoped
    }
  , { name := "search_canonical_serial_has_exact_result_contract"
    , present := true
    , supportClass := .executableSemantics
    }
  , { name := "search_threaded_exact_single_lane_has_exact_result_contract"
    , present := true
    , supportClass := .executableSemantics
    }
  , { name := "search_batched_parallel_exact_has_certified_window_exact_contract"
    , present := true
    , supportClass := .executableSemantics
    }
  , { name := "search_batched_parallel_envelope_has_envelope_bounded_contract"
    , present := true
    , supportClass := .executableSemantics
    }
  , { name := "search_scheduler_step_budget_yields_budgeted_anytime_contract"
    , present := true
    , supportClass := .executableSemantics
    }
  , { name := "search_selected_result_observation_slice_refines_legacy_fields"
    , present := true
    , supportClass := .refinementCorollary
    }
  ]

/-- Compact theorem inventory used by existing gates. -/
def fairnessTheoremInventory : List (String × Bool) :=
  fairnessTheoremInventoryRows.map fun row => (row.name, row.present)

/-- Companion theorem-support classification surface. -/
def fairnessTheoremInventorySupportClasses : List (String × SearchTheoremSupportClass) :=
  fairnessTheoremInventoryRows.map fun row => (row.name, row.supportClass)

/-- Problem-class classification for one theorem inventory key. -/
def classifyTheoremProblemClass (name : String) : SearchTheoremProblemClass :=
  if name = "search_canonical_serial_has_exact_result_contract" ||
      name = "search_threaded_exact_single_lane_has_exact_result_contract" ||
      name = "search_batched_parallel_exact_has_certified_window_exact_contract" ||
      name = "search_batched_parallel_envelope_has_envelope_bounded_contract" ||
      name = "search_scheduler_step_budget_yields_budgeted_anytime_contract" ||
      name = "search_selected_result_observation_slice_refines_legacy_fields"
  then .genericSelectedResult
  else if name = "search_canonical_serial_goal_reached_from_ready_witness_path" ||
      name = "search_canonical_machine_goal_reached_from_ready_witness_path" ||
      name = "search_canonical_machine_goal_reached_from_graph_reachability" ||
      name = "search_canonical_machine_goal_reached_from_raw_successor_semantics" ||
      name = "search_goal_reachability_connects_to_incumbent_publication" ||
      name = "search_eventual_optimal_goal_publication_under_admissible_consistent_heuristic" ||
      name = "search_canonical_serial_goal_window_service_has_exact_suffix_bound" ||
      name = "search_threaded_exact_single_lane_goal_window_service_has_exact_suffix_bound"
  then .pathProblemSpecific
  else .genericMachine

/-- Generic-machine theorem rows from the current search inventory. -/
def genericMachineTheoremInventory : List (String × Bool) :=
  fairnessTheoremInventory.filter fun (name, _) =>
    classifyTheoremProblemClass name = .genericMachine

/-- Problem-class-specific theorem rows from the current search inventory. -/
def genericSelectedResultTheoremInventory : List (String × Bool) :=
  fairnessTheoremInventory.filter fun (name, _) =>
    classifyTheoremProblemClass name = .genericSelectedResult

/-- Path-problem-specific theorem rows from the current search inventory. -/
def problemSpecificTheoremInventory : List (String × Bool) :=
  fairnessTheoremInventory.filter fun (name, _) =>
    classifyTheoremProblemClass name = .pathProblemSpecific

end Search
end Proofs
end Runtime
