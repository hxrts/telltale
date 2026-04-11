import Runtime.Proofs.Search.Liveness
import Runtime.Proofs.Search.ProfileClaims
import Runtime.Proofs.Search.Problem

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.PathProblems

Path-search-specific completeness and publication theorems.

The generic search proof lane is problem-shaped, but the current strongest
completeness/publication theorems are still about the built-in path-search
specialization. This module re-exports those theorems explicitly as the
path-problem family instead of leaving them mixed into the generic machine
surface.
-/

namespace Runtime
namespace Proofs
namespace Search

theorem path_problem_goal_window_service_has_exact_suffix_bound
    {frontier : List FrontierEntry} {entry : FrontierEntry}
    (hMin : IsMinPriority frontier entry) :
    entry ∉ frontierAfterCanonicalStep frontier :=
  canonical_serial_goal_window_service_has_exact_suffix_bound hMin

theorem path_problem_threaded_goal_window_service_has_exact_suffix_bound
    {frontier : List FrontierEntry} {entry : FrontierEntry}
    (hMin : IsMinPriority frontier entry) :
    entry ∉ frontierAfterThreadedExactSingleLaneStep frontier :=
  threaded_exact_single_lane_goal_window_service_has_exact_suffix_bound hMin

theorem path_problem_goal_reachability_connects_to_publication
    {goal start bound : Nat}
    {trace : SearchMachineTrace}
    (hPremises : GoalPublicationPremises goal trace start bound) :
    ∃ j, j < bound ∧ GoalIncumbentPublished goal (trace (start + j + 1)) := by
  simpa using
    goal_reachability_connects_to_incumbent_publication hPremises

theorem path_problem_eventual_optimal_publication_under_admissible_consistent_heuristic
    {goal start bound optimalCost : Nat}
    {trace : SearchMachineTrace}
    (hPremises :
      OptimalGoalPublicationPremises goal trace start bound optimalCost) :
    ∃ j commit,
      j < bound ∧
        (trace (start + j + 1)).incumbent = some commit ∧
        commit.node = goal ∧
        commit.gScore = optimalCost := by
  simpa using
    eventual_optimal_goal_publication_under_admissible_consistent_heuristic hPremises

end Search
end Proofs
end Runtime
