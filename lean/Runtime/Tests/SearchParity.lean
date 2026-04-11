import Lean.Data.Json
import Runtime.Proofs.Search.API

set_option autoImplicit false

open Lean (Json)
open Runtime.Proofs.Search

def main : IO Unit := do
  let supportClassString := fun cls =>
    match cls with
    | .executableSemantics => "executable_semantics"
    | .refinementCorollary => "refinement_corollary"
    | .premiseScoped => "premise_scoped"
  let problemClassString := fun cls =>
    match cls with
    | .genericMachine => "generic_machine"
    | .problemSpecific => "problem_specific"
  let canonicalClaim :=
    match fairnessClaimClass .canonicalSerial with
    | .exactOneStep => "exact_one_step"
    | .exactOneStepUnderRefinement => "exact_one_step_under_refinement"
    | .premisedWindowBounded => "premised_window_bounded"
    | .premiseOnly => "premise_only"
  let threadedClaim :=
    match fairnessClaimClass .threadedExactSingleLane with
    | .exactOneStep => "exact_one_step"
    | .exactOneStepUnderRefinement => "exact_one_step_under_refinement"
    | .premisedWindowBounded => "premised_window_bounded"
    | .premiseOnly => "premise_only"
  let batchedExactClaim :=
    match fairnessClaimClass .batchedParallelExact with
    | .exactOneStep => "exact_one_step"
    | .exactOneStepUnderRefinement => "exact_one_step_under_refinement"
    | .premisedWindowBounded => "premised_window_bounded"
    | .premiseOnly => "premise_only"
  let envelopeClaim :=
    match fairnessClaimClass .batchedParallelEnvelopeBounded with
    | .exactOneStep => "exact_one_step"
    | .exactOneStepUnderRefinement => "exact_one_step_under_refinement"
    | .premisedWindowBounded => "premised_window_bounded"
    | .premiseOnly => "premise_only"
  let canonicalCertificate := "current_min_key_batch"
  let threadedCertificate := "current_min_key_batch_via_threaded_refinement"
  let batchedExactCertificate := "certified_current_min_key_window"
  let envelopeCertificate := "certified_current_min_key_window"
  let inventoryJson :=
    Json.arr <| fairnessTheoremInventory.toArray.map fun (name, present) =>
      Json.mkObj [("name", Json.str name), ("present", Json.bool present)]
  let theoremPackInventoryJson :=
    Json.arr <| theoremPackInventory.toArray.map fun (name, present) =>
      Json.mkObj [("name", Json.str name), ("present", Json.bool present)]
  let theoremPackInventoryClassesJson :=
    Json.arr <| theoremPackInventorySupportClasses.toArray.map fun (name, cls) =>
      Json.mkObj
        [ ("name", Json.str name)
        , ("support_class", Json.str (supportClassString cls))
        ]
  let theoremPackInventoryProblemClassesJson :=
    Json.arr <| fairnessTheoremInventory.toArray.map fun (name, _) =>
      Json.mkObj
        [ ("name", Json.str name)
        , ("problem_class", Json.str (problemClassString (classifyTheoremProblemClass name)))
        ]
  let payload := Json.mkObj
    [ ("schema_version", Json.str "search_parity_v13")
    , ("canonical_batch_nodes", Json.arr #[Json.num 1, Json.num 2])
    , ("independent_targets", Json.arr #[Json.num 4, Json.num 5])
    , ("replay_epoch_trace", Json.arr #[Json.num 1])
    , ("replay_phase_trace", Json.arr #[Json.num 0, Json.num 0, Json.num 0])
    , ("barrier_before_epoch", Json.num 1)
    , ("barrier_after_epoch", Json.num 2)
    , ("barrier_phase_delta", Json.num 1)
    , ("fairness_bundle", Json.arr #[Json.str "EventualLiveBatchService"])
    , ("canonical_service_bound_steps", Json.num 1)
    , ("profile_claims", Json.mkObj
        [ ("canonical_serial", Json.str canonicalClaim)
        , ("threaded_exact_single_lane", Json.str threadedClaim)
        , ("batched_parallel_exact", Json.str batchedExactClaim)
        , ("batched_parallel_envelope_bounded", Json.str envelopeClaim)
        ])
    , ("profile_certificates", Json.mkObj
        [ ("canonical_serial", Json.str canonicalCertificate)
        , ("threaded_exact_single_lane", Json.str threadedCertificate)
        , ("batched_parallel_exact", Json.str batchedExactCertificate)
        , ("batched_parallel_envelope_bounded", Json.str envelopeCertificate)
        ])
    , ("threaded_commit_trace_refines_canonical", Json.bool true)
    , ("threaded_state_slice_refines_canonical", Json.bool true)
    , ("threaded_observation_equivalent_to_canonical", Json.bool true)
    , ("threaded_multi_step_state_trace_refines_canonical", Json.bool true)
    , ("threaded_multi_step_observation_trace_refines_canonical", Json.bool true)
    , ("threaded_state_artifact_refines_canonical", Json.bool true)
    , ("threaded_multi_step_state_artifact_trace_refines_canonical", Json.bool true)
    , ("certified_window_trace_valid", Json.bool true)
    , ("fairness_inventory", inventoryJson)
    , ("theorem_pack_inventory", theoremPackInventoryJson)
    , ("theorem_pack_inventory_classes", theoremPackInventoryClassesJson)
    , ("theorem_pack_inventory_problem_classes", theoremPackInventoryProblemClassesJson)
    , ("theorem_pack_service_bound_steps", Json.num buildSearchFairnessTheoremPack.canonicalServiceBoundSteps)
    , ("theorem_pack_goal_window_discovery_suffix_bound_steps",
        Json.num buildSearchFairnessTheoremPack.canonicalGoalWindowDiscoverySuffixBoundSteps)
    , ("theorem_pack_gate", Json.str "just check-search-fairness")
    ]
  IO.println payload.compress
