import Lean.Data.Json

set_option autoImplicit false

open Lean (Json)

def main : IO Unit := do
  let payload := Json.mkObj
    [ ("schema_version", Json.str "search_parity_v1")
    , ("canonical_batch_nodes", Json.arr #[Json.num 1, Json.num 2])
    , ("independent_targets", Json.arr #[Json.num 4, Json.num 5])
    , ("replay_epoch_trace", Json.arr #[Json.num 1])
    , ("replay_phase_trace", Json.arr #[Json.num 0, Json.num 0, Json.num 0])
    , ("barrier_before_epoch", Json.num 1)
    , ("barrier_after_epoch", Json.num 2)
    , ("barrier_phase_delta", Json.num 1)
    , ("fairness_bundle", Json.arr #[Json.str "EventualLiveBatchService"])
    ]
  IO.println payload.compress
