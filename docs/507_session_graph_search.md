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
ten modules: `Core`, `Fairness`, `Executable`, `Machine`, `Liveness`,
`Refinement`, `ProfileClaims`, `Envelope`, `Inventory`, and `TheoremPack`,
re-exported through `API`.

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

### Executable Semantics (Executable)

`Runtime.Proofs.Search.Executable` is now the semantic center of the search
proof lane:

- `SearchMachineState` — reduced proof-relevant machine state carrying
  frontier, closed nodes, inconsistent nodes, score table, parent witnesses,
  incumbent, phase, and progress accounting.
- `MachineInvariants` — reduced machine invariant bundle covering
  open/closed disjointness, `incons ⊆ closed`, parent-score coherence,
  incumbent coherence, and nodup conditions.
- `executableCanonicalStep` — concrete reduced step function implementing
  canonical batch extraction, batch removal, normalized commit production,
  `open/closed/incons` movement, score updates, and reduced incumbent refresh.
- `stateSliceOfMachineState`, `observationSliceOfMachineState`, and
  `stateArtifactOfMachineState` — explicit Rust-facing reduced extraction
  boundary from executable machine states back into the reduced artifact
  vocabulary used by parity tests and theorem-pack exports.

Key theorems exposed by this module:

- **`executable_canonical_step_preserves_invariants`** — executable reduced
  stepping preserves the reduced machine invariant bundle.
- **`executable_step_artifact_refines_canonical_step_artifact`** — the
  executable step refines exactly to the existing reduced step-artifact
  vocabulary.
- **`runtime_state_artifact_of_machine_state_is_projection`** — the reduced
  runtime-state artifact is an explicit projection of executable machine state.

### Machine Vocabulary (Machine)

`Runtime.Proofs.Search.Machine` now packages the executable semantics into the
machine-facing theorem surface:

- `CanonicalMachineStep` — packaged executable reduced step plus current-state
  invariant bundle.
- `CanonicalMachineTrace` — machine trace version of canonical serial search.

Key theorems exposed by this module:

- **`canonical_machine_step_services_current_min_priority_entries`** — the
  machine-level step relation preserves the same one-step service fact for the
  current min-key batch as the frontier-only fairness layer.
- **`canonical_machine_step_preserves_invariants`** — machine invariants are
  preserved by the executable reduced step.
- **`canonical_machine_trace_currently_min_priority_eventually_serviced`** —
  machine traces inherit the frontier-facing one-step eventual-service theorem
  through frontier projection.
- **`executable_trace_refines_canonical_machine_trace`** — executable machine
  traces refine directly into the packaged machine-step theorem surface.
- **`canonical_machine_step_artifact_refines_runtime_boundary`** and
  **`canonical_machine_state_artifact_is_runtime_projection`** — the
  machine-level theorem surface now includes explicit refinement back into the
  Rust-facing reduced artifact vocabulary.

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

### Liveness Proofs (Liveness)

`Runtime.Proofs.Search.Liveness` extends the search lane beyond the current
min-key batch:

- **`closed_nodes_length_le_reachable_length`** — under the fixed-phase premise
  bundle, closed-node cardinality stays bounded by a finite reachable-node
  universe.
- **`fixed_phase_canonical_serial_terminates_under_finite_reachable_bound`** —
  fixed-phase canonical serial search terminates under an explicit finite
  reachable-node premise bundle.
- **`rebuild_aware_canonical_serial_terminates_under_phase_work_measure`** —
  rebuild-aware ARA-style termination theorem under an explicit lexicographic
  phase/work progress measure encoded into a natural descent argument.
- **`bounded_strict_preemption_eventually_becomes_min`** — a continuously
  present non-min-priority entry eventually reaches the min-key window when the
  count of strictly better entries is bounded and decreases strictly while it
  remains non-min.
- **`canonical_serial_nonmin_entry_eventually_serviced_under_bounded_strict_preemption`**
  — composes the previous theorem with one-step fairness to obtain a service
  bound for an entry that is not initially in the current canonical batch.
- **`finite_better_entry_exhaustion_eventually_becomes_min`** and
  **`canonical_serial_nonmin_entry_eventually_serviced_under_finite_better_entry_exhaustion`**
  — stronger structural non-min fairness theorems using a finite better-entry
  universe rather than only an ad hoc numeric preemption bound.
- **`canonical_serial_goal_reached_from_ready_witness_path`** — global
  goal-reachability theorem for the reduced model: from an explicit ready
  witness path whose successive frontier entries become service-ready in order,
  the goal entry is eventually serviced.
- **`canonical_machine_goal_reached_from_ready_witness_path`** — machine-level
  version of the same theorem: executable canonical stepping closes the goal
  node within the witness-path horizon.
- **`canonical_machine_goal_reached_from_graph_reachability`** — stronger
  completeness theorem driven by an explicit graph-reachability premise bundle
  that names reachable-node path, finiteness, and heuristic assumptions.
- **`goal_reachability_connects_to_incumbent_publication`** — machine-level
  bridge from bounded goal reachability to incumbent publication under an
  explicit publication premise bundle.
- **`eventual_optimal_goal_publication_under_admissible_consistent_heuristic`**
  — premise-scoped optimality theorem: under explicit admissibility and
  consistency premises, eventual goal publication strengthens to eventual
  optimal-goal publication.

These liveness theorems are premise-scoped. Termination is proved only for the
named premise bundles exposed in the theorem statements. Completeness is now
stated over a graph-reachability bundle rather than a free-standing ready-path
statement, but it still depends on explicit ready-path and heuristic premises
instead of deriving from unconstrained Rust successor semantics alone.

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

### Envelope Boundary (Envelope)

`Runtime.Proofs.Search.Envelope` makes the remaining envelope-bounded gap
explicit:

- **`EnvelopeFairnessDesignBoundary`** — checked-in design boundary listing the
  missing ingredients for an unconditional envelope fairness theorem.
- **`batched_parallel_envelope_design_boundary_is_explicit`** — proves that the
  envelope-bounded profile remains premise-only by explicit design review, not
  by omission. The current recorded reasons are lack of a certified frontier
  window, lack of canonical commit refinement, and lack of an
  observation-equivalence theorem.

### Theorem Inventory (Inventory and TheoremPack)

`Runtime.Proofs.Search.Inventory` records every theorem by name together with
a `Bool` indicating whether it is proved. `Runtime.Proofs.Search.TheoremPack`
now also exports a support classification for every row:
`executableSemantics`, `refinementCorollary`, or `premiseScoped`.

The current inventory has **36 proved** theorems and **1 unproved**: the
unconditional fairness theorem for `batchedParallelEnvelopeBounded` is still
intentionally left as `false`, but the lack of that theorem is now paired with
an explicit design-boundary theorem in `Envelope` and a premise-scoped support
classification in the theorem pack.

`Runtime.Proofs.Search.TheoremPack` wraps the inventory, support classes, and
two numeric bounds into a `SearchFairnessTheoremPack` structure:

```
inventorySupportClasses
canonicalServiceBoundSteps                 := 1
canonicalGoalWindowDiscoverySuffixBoundSteps := 1
```

Both bounds are exactly one step, matching the `EventuallyServicedWithin ...
1` statements in `Fairness` and `ProfileClaims`.

The dedicated local verification gate is `just check-search-fairness`. The
theorem-pack is also exported through the runtime API and written to
`target/search-theorem-pack/search-theorem-pack.json` for release and
provenance checks.

### What the Proofs Still Do Not Cover

- **Executable refinement to the full Rust machine**: the Lean lane now has an
  executable reduced machine semantics, but it is still a reduced model. There
  is not yet a full executable refinement proof from every Rust search-machine
  transition, rebuild path, and epoch transition into that Lean machine.
- **Unconstrained global completeness from raw successor semantics**: the new
  completeness theorem names graph reachability, finiteness, and heuristic
  premises explicitly, but it still depends on an explicit reachable ready-path
  witness bundle. There is still no blanket theorem that every reachable goal
  in an arbitrary Rust search domain is eventually discovered from `start`
  without those progress premises.
- **Fairness under unbounded better-work arrival**: non-min-priority entries now
  have proved service theorems under bounded strict preemption and under a
  finite better-entry exhaustion bundle. There is still no fairness theorem for
  traces that can admit an unbounded stream of strictly better entries.
- **Unconditional fairness for `batchedParallelEnvelopeBounded`**: the profile
  still carries no unconditional fairness theorem. What changed is that the
  absence is now explicit and documented through the `Envelope` design-boundary
  theorem, empty theorem-backed observable set, and premise-scoped theorem-pack
  classification rather than left as an undocumented proof gap.

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
contracts, theorem-pack support-class parity, and epoch-barrier semantics with
fairness-bundle fixtures. See
[Rust-Lean Bridge and Parity](802_rust_lean_parity.md) for the deviation registry and
parity policy.
