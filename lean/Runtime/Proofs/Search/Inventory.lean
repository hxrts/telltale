import Runtime.Proofs.Search.ProfileClaims

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.Inventory

Machine-readable inventory for the current search fairness theorem surface.
-/

namespace Runtime
namespace Proofs
namespace Search

/-- Current search fairness theorem inventory. -/
def fairnessTheoremInventory : List (String × Bool) :=
  [ ("search_canonical_serial_exact_one_step_fairness", true)
  , ("search_canonical_serial_dynamic_liveness_under_stability", true)
  , ("search_threaded_exact_single_lane_refines_canonical_one_step", true)
  , ("search_threaded_exact_single_lane_commit_trace_refines_canonical", true)
  , ("search_threaded_exact_single_lane_state_slice_refines_canonical", true)
  , ("search_threaded_exact_single_lane_observation_slice_refines_canonical", true)
  , ("search_threaded_exact_single_lane_observation_equivalent_to_canonical", true)
  , ("search_threaded_exact_single_lane_multi_step_state_trace_refines_canonical", true)
  , ("search_threaded_exact_single_lane_multi_step_observation_trace_refines_canonical", true)
  , ("search_threaded_exact_single_lane_state_artifact_refines_canonical", true)
  , ("search_threaded_exact_single_lane_multi_step_state_artifact_trace_refines_canonical", true)
  , ("search_threaded_exact_single_lane_exact_one_step_fairness", true)
  , ("search_canonical_serial_goal_window_service_has_exact_suffix_bound", true)
  , ("search_threaded_exact_single_lane_goal_window_service_has_exact_suffix_bound", true)
  , ("search_batched_parallel_exact_certified_window_fairness", true)
  , ("search_batched_parallel_exact_bounded_dynamic_starvation_freedom", true)
  , ("search_batched_parallel_exact_certified_window_trace_valid", true)
  , ("search_batched_parallel_envelope_unconditional_fairness", false)
  ]

end Search
end Proofs
end Runtime
