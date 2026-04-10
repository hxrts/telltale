# Session Graph Search

`telltale-search` implements ARA*-style weighted graph search over Telltale
session graphs. It provides canonical search-machine semantics, deterministic
batch extraction, proposal normalization, and replay artifacts. The crate is
intentionally generic and free of simulator, viewer, browser, or
application-specific routing dependencies.

## Scope

The crate owns the search algorithm, its determinism contract, and the
capability vocabulary for scheduler profiles, fairness assumptions, and
observable classes. Downstream crates provide domain-specific node and edge
semantics, heuristic and cost policies, graph snapshots, and epoch updates.

`telltale-simulator` can project search runs through
`project_search_run(...)`. `telltale-viewer` can project search artifacts
through `project_search_artifacts(...)`. These integration layers are optional
and live above the crate boundary.

## Core Surface

`SearchDomain` defines the contract a downstream domain must implement:
successor generation, heuristic evaluation, and snapshot identity.
`SearchCost` and its concrete implementation `EpsilonMilli` define the cost
algebra. `EpsilonMilli` uses fixed-point milli-precision with a `u32` backing
store.

`SearchMachine` owns the frontier, parent map, incumbent, and budget state. It
exposes `step_once(...)` for single canonical steps and explicit invariant
checks for partition discipline, parent-score coherence, incumbent coherence,
and batch legality. `CanonicalBatch` and `Proposal` represent the min-key batch
window and its normalized expansion results. Path reconstruction is available
through the incumbent.

## Runtime Surface

`run_with_executor(...)` is the canonical host execution entry point.
`SearchRunConfig` provides typed runtime configuration for scheduler profile,
executor kind, fairness assumptions, batch width, and budget limits.
`validate_run_config(...)` enforces fail-closed checks for scheduler-profile,
executor-kind, fairness, and batch-width mismatches before execution begins.

`ProposalExecutor` is the trait for batch expansion strategies.
`SerialProposalExecutor` runs proposals sequentially.
`NativeParallelExecutor` uses `rayon` when the `multi-thread` feature is
enabled. Constructing `NativeParallelExecutor` without the feature fails
explicitly rather than silently degrading.

The runtime emits `SchedulerArtifact` for scheduler classification,
`SearchFairnessArtifact` for profile-scoped fairness evidence, and
`SearchRouteBoundArtifact` for route discovery and quality reporting.
`SearchStateArtifact` provides per-round state and certificate traces for
exact-profile correspondence checks.

## Admission and Capabilities

`SearchDUser` and `SearchCertifiedCapability` define the admission vocabulary.
`check_capability_containment(...)` verifies that a user's certified
capabilities satisfy the requirements of a given scheduler profile, fairness
assumption set, and observable class list. The check is fail-closed and returns
structured `AdmissionRejectionReason` values on mismatch.

The capability vocabulary covers four dimensions: `SearchSchedulerProfile`,
`SearchFairnessAssumption`, `SearchDeterminismMode`, and
`SearchObservableClass`. These are first-class observable artifacts and
comparison inputs throughout the runtime and replay surfaces.

## Replay and Epoch Reconfiguration

Replay semantics are fail-closed. `SearchReplayArtifact` captures the canonical
round commits, epoch schedule, snapshot schedule, phase schedule, and batch
schedule from a prior run. `replay_observation(...)` re-derives the final
observation from canonical round commits and rejects drift against the stored
artifact.

`EpochReconfigurationRequest` and `commit_epoch_reconfiguration(...)` handle
graph-epoch transitions. Reconfiguration resets the canonical frontier, parent
map, and incumbent state, then re-seeds from the start node. Runtime failures
during proposal generation do not consume the canonical batch.

## Observation and Comparison

`SearchObservationArtifact` captures the observable surface of a completed
search run. `compare_observations(...)` compares two artifacts against a
determinism mode and observable class list. Under `ModuloCommutativity` mode,
normalized commit traces are compared as multisets rather than sequences.

Observable classes include `IncumbentCost`, `CanonicalPathIdentity`,
`NormalizedCommitTrace`, `GraphEpochTrace`, `SchedulerProfileTrace`, and
`ProgressAccounting`.

## Lean Proof Support

The Lean formalization lives in `Runtime.Proofs.Search` and is structured in
six modules: `Core`, `Fairness`, `Refinement`, `ProfileClaims`, `Inventory`,
and `TheoremPack`, re-exported through `API`.

### Proof Vocabulary (Core)

`Runtime.Proofs.Search.Core` establishes the foundational vocabulary:

- `FrontierEntry` — a `(node : Nat, priority : Nat)` pair; the unit of
  frontier membership.
- `IsMinPriority frontier entry` — `entry` is present in `frontier` and no
  other entry has strictly lower priority.
- `canonicalBatch frontier` — the list of all entries satisfying
  `IsMinPriority`; these are exactly the entries that will be serviced in the
  next step.
- `frontierAfterCanonicalStep frontier` — the frontier with the canonical batch
  removed.
- `OneStepFair frontier` — every `IsMinPriority` entry is absent from
  `frontierAfterCanonicalStep frontier`.
- `CanonicalSerialTrace` — a dynamic frontier trace whose successive states are
  related by `frontierAfterCanonicalStep`.
- `EventuallyServicedWithin trace start bound entry` — `entry` is removed from
  `trace start` within `bound` steps.
- `ContinuouslyEligible`, `NoStrictlyBetterEntryAppears` — predicates used in
  the dynamic liveness theorem to constrain how the frontier evolves.

The reduced artifact structures — `StepArtifact`, `StateSlice`,
`ObservationSlice`, and `StateArtifactSchema` — define the boundary at which
Lean and Rust search states are compared. `BatchedExactWindowCertificate` is
a proof-carrying record whose fields provide evidence that a batched window
covers the current canonical batch and produces a commit for each covered
entry; downstream fairness theorems are conditioned on holding one of these
certificates.

### Fairness Proofs (Fairness)

`Runtime.Proofs.Search.Fairness` proves:

- **`mem_canonicalBatch_iff_isMinPriority`** — membership in the canonical
  batch is equivalent to satisfying `IsMinPriority`. This connects the
  computational filter to the logical predicate.
- **`canonical_batch_entries_removed_after_step`** — every entry in the
  canonical batch is absent after the step. This is the core removal fact.
- **`canonical_serial_one_step_fair_for_min_priority_entries`** — if `entry`
  satisfies `IsMinPriority`, it is absent after one canonical step. This is
  the main one-step fairness result.
- **`canonical_serial_batch_is_one_step_fair`** — the full frontier is
  `OneStepFair`.
- **`currently_min_priority_eventually_serviced_within_one_step`** — in any
  `CanonicalSerialTrace`, a current `IsMinPriority` entry satisfies
  `EventuallyServicedWithin ... 1`. The service bound is exactly one step.
- **`continuously_eligible_without_strictly_better_entries_eventually_serviced`**
  — the dynamic liveness result: if an entry remains eligible and no strictly
  better entry arrives across a horizon, it is serviced within one step.

These proofs establish unconditional one-step fairness for `canonicalSerial`.
No fairness is claimed for entries outside the current min-key batch.

### Refinement Proofs (Refinement)

`Runtime.Proofs.Search.Refinement` proves that the threaded exact single-lane
executor is identical to canonical serial at every reduced artifact boundary:

- **`threaded_exact_single_lane_step_artifact_refines_canonical`** — the full
  `StepArtifact` is equal.
- **`threaded_exact_single_lane_commit_trace_refines_canonical`** and
  **`threaded_exact_single_lane_batch_nodes_refine_canonical`** — the
  `normalizedCommits` and `batchNodes` fields match individually.
- **`threaded_exact_single_lane_state_slice_refines_canonical`** and
  **`threaded_exact_single_lane_observation_slice_refines_canonical`** — the
  reduced `StateSlice` and `ObservationSlice` projections are equal.
- **`threaded_exact_single_lane_multi_step_state_trace_refines_canonical`**,
  **`..._observation_trace_..._canonical`**, and
  **`..._state_artifact_trace_..._canonical`** — all three multi-step trace
  functions agree across arbitrary `FrontierTrace` inputs.

These are equalities, not simulations: parallelisation of successor enumeration
within a batch produces no observable difference in batch nodes, normalized
commits, state, or observations.

### Profile Claims (ProfileClaims)

`Runtime.Proofs.Search.ProfileClaims` packages the fairness story per
`SearchSchedulerProfile` using a `FairnessClaimClass` type:

| Profile | `FairnessClaimClass` | Proof status |
|---|---|---|
| `canonicalSerial` | `exactOneStep` | proved unconditionally |
| `threadedExactSingleLane` | `exactOneStepUnderRefinement` | proved via refinement |
| `batchedParallelExact` | `premisedWindowBounded` | proved under `BatchedExactWindowCertificate` |
| `batchedParallelEnvelopeBounded` | `premiseOnly` | no unconditional theorem |

Key theorems exposed by this module:

- **`canonical_serial_profile_has_exact_one_step_fairness`** and
  **`canonical_serial_goal_window_service_has_exact_suffix_bound`** — restate
  the `Fairness` results at profile granularity.
- **`threaded_exact_single_lane_has_exact_one_step_fairness`** — derives
  one-step fairness for the threaded profile by composing the `Refinement`
  equalities.
- **`threaded_exact_single_lane_has_exact_observation_equivalence`** —
  observation slices match canonical serial exactly.
- **`certified_batched_exact_window_is_fair`** — given a
  `BatchedExactWindowCertificate`, every `IsMinPriority` entry is removed
  within the certified window.
- **`certified_batched_exact_window_eventually_services_min_priority_entries`**
  — restates the above as an `EventuallyServicedWithin` bound of 1.
- **`certified_batched_exact_window_bounded_dynamic_starvation_freedom`** —
  the strongest premise-scoped result: given certificates for each step in a
  horizon, a `ContinuouslyEligible` entry under `BoundedPreemptionWindow` is
  serviced within `bound` steps.
- **`certified_window_trace_is_valid_for_exact_batch_service`** — validates
  that a certificate sequence matches the canonical batch at every step with
  a service bound of 1.
- **`batched_parallel_envelope_claim_is_premise_only`** — states formally that
  the envelope-bounded profile has no proof-backed fairness guarantee.

### Theorem Inventory (Inventory and TheoremPack)

`Runtime.Proofs.Search.Inventory` records every theorem by name together with
a `Bool` indicating whether it is proved. The current inventory has
**17 proved** theorems and **1 unproved**: the unconditional fairness theorem
for `batchedParallelEnvelopeBounded` is intentionally left as `false` because
no unconditional proof exists for that profile.

`Runtime.Proofs.Search.TheoremPack` wraps the inventory and two numeric
bounds into a `SearchFairnessTheoremPack` structure:

```
canonicalServiceBoundSteps                 := 1
canonicalGoalWindowDiscoverySuffixBoundSteps := 1
```

Both bounds are exactly one step, matching the `EventuallyServicedWithin ...
1` statements in `Fairness` and `ProfileClaims`.

The dedicated local verification gate is `just check-search-fairness`. The
theorem-pack is also exported through the runtime API and written to
`target/search-theorem-pack/search-theorem-pack.json` for release and
provenance checks.

### What the Proofs Do Not Cover

- **Termination**: no proof that the frontier ever empties.
- **Global completeness**: no proof that the goal node is eventually reached.
- **Fairness for non-min-priority entries**: an entry not in the current
  canonical batch has no service bound.
- **Unconditional fairness for `batchedParallelEnvelopeBounded`**: this
  profile carries premise-only classification with no supporting theorem.

## Artifact Vectors

Stable source-controlled search artifact vectors are exported through
`cargo run -p telltale-search --example export_vectors` and checked by the
`search_vectors` conformance test. This covers theorem-pack, final-state,
fairness, and replay artifact drift.

A separate recovery vector surface is exported through
`cargo run -p telltale-search --example export_recovery_vectors` and checked by
`search_recovery_vectors`. This covers epoch-transition recovery bounds and
route summaries.

The release and provenance lane records both the theorem-pack JSON and the
generated canonical vector artifact at
`target/search-artifacts/search-vectors-v1.json`, plus the recovery vector
artifact at `target/search-artifacts/search-recovery-vectors-v1.json`.

## Target Support

The core serial machine is target-agnostic. WASM builds use the same canonical
serial and replay surface without `rayon`. The optional `multi-thread` feature
enables the native parallel executor for native targets.

## Lean/Rust Parity

Reduced Lean/Rust parity currently covers canonical batch-window extraction,
proposal independence over declared authority surfaces, replay epoch and phase
contracts, and epoch-barrier semantics with fairness-bundle fixtures. See
[Rust-Lean Bridge and Parity](802_rust_lean_parity.md) for the deviation registry and
parity policy.
