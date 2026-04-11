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

Execution policy is explicit and separate from downstream search-problem
semantics. Downstream control policy may choose scheduler profile, batch
width, caching mode, and effort regime, but that execution-side choice does
not redefine the search objective or candidate meaning.

`telltale-simulator` can project search runs through
`project_search_run(...)`. `telltale-viewer` can project search artifacts
through `project_search_artifacts(...)`. These integration layers are optional
and live above the crate boundary.

Allowed downstream variation includes:

- node and edge meaning
- heuristic and cost policy
- success/selection criterion
- reconstruction witness
- execution profile

Non-goal:
the crate does not define downstream domain truth, candidate eligibility, or
objective semantics.

## Core Surface

`SearchDomain` defines the contract a downstream domain must implement:
successor generation, heuristic evaluation, snapshot identity, and optionally
custom authority-surface derivation through the blanket
`SearchAuthorityPolicy` hook.
`SearchCost` and its concrete implementation `EpsilonMilli` define the cost
algebra. `EpsilonMilli` uses fixed-point milli-precision with a `u32` backing
store.

`SearchQuery` generalizes the built-in problem surface:

- `SingleGoal` for classic one-goal path search
- `MultiGoal` for any-of-N terminal search
- `CandidateSet` for selector-style best-candidate search

`SearchMachine` owns the frontier, parent map, selected solution, and budget
state. The historical incumbent vocabulary is still present for compatibility,
but the crate also exports selected-result aliases and accessors.
`SearchMachine` exposes `step_once(...)` for single canonical steps and
explicit invariant checks for partition discipline, parent-score coherence,
selected-result coherence, and batch legality. `CanonicalBatch` and `Proposal`
represent the min-key batch window and its normalized expansion results. The
built-in path-search adapters still reconstruct canonical paths.

## Runtime Surface

`run_with_executor(...)` is the canonical host execution entry point.
`SearchExecutionPolicy` is the explicit execution-side runtime policy surface:
it carries scheduler profile, batch width, caching profile, and effort
profile. `SearchRunConfig` packages that execution policy together with the
declared fairness assumptions. `validate_run_config(...)` enforces fail-closed
checks for unsupported execution-policy variants, executor-kind mismatches,
fairness mismatches, and batch-width mismatches before execution begins. The
executor strategy is supplied separately via the `ProposalExecutor`
implementation and does not define search-problem semantics.

`ProposalExecutor` is the trait for batch expansion strategies.
`SerialProposalExecutor` runs proposals sequentially.
`NativeParallelExecutor` uses `rayon` when the `multi-thread` feature is
enabled. Constructing `NativeParallelExecutor` without the feature fails
explicitly rather than silently degrading.

The runtime emits `SchedulerArtifact` for scheduler classification and the
declared execution policy,
`SearchFairnessArtifact` for profile-scoped fairness evidence,
`SearchResultBoundArtifact` for generic selected-result discovery and quality
reporting, with `SearchRouteBoundArtifact` retained as the path-search
compatibility alias, and
packages them together with state traces and progress summary in
`SearchExecutionReport`. `SearchStateArtifact` provides per-round state and
certificate traces for exact-profile correspondence checks. `SearchFullStateArtifact`
is the Rust-facing extraction boundary for the full-machine refinement lane:
it includes `OPEN`, `CLOSED`, `INCONS`, `g_score`, parent, incumbent,
epsilon, epoch/snapshot, last-batch nodes, and full commit/publication traces.
`SearchFairnessArtifact` is the proof-claim carrier: it records the profile
claim class, theorem-side certificate, and whether exact
commit-trace/state-slice/observation equivalence to canonical serial is part
of the claimed surface for that profile.

`SearchResultSummary` is the generic selected-result summary exported in result
bounds. Path-search-specific summary data now lives under its optional
`path_summary` helper, with `SearchRouteSummary` retained as the compatibility
alias for that path-specific wrapper rather than the primary generic summary.

The theorem-pack surface is also classified conceptually into:

- generic machine/refinement/fairness theorems
- problem-class-specific completeness/discovery theorems

Rust currently exposes helper classification for this split through
`classify_theorem_problem_class(...)` and
`theorem_inventory_problem_classes()`. The theorem-pack artifact now exports
that split directly in `inventory_problem_classes` alongside
`inventory_support_classes`. Lean mirrors the same distinction in the search
theorem inventory docs.

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
graph-epoch transitions. Reconfiguration now carries an explicit
`SearchReseedingPolicy`:

- `StartOnly` resets the frontier and reseeds only from the canonical start
- `PreserveOpenAndIncons` preserves the live frontier plus the retained parent
  closure needed for witness reconstruction

Replay and state artifacts record the applied reseeding policy on runs that
cross epoch barriers. Runtime failures during proposal generation do not
consume the canonical batch.

## Observation and Comparison

`SearchObservationArtifact` captures the observable surface of a completed
search run. `compare_observations(...)` compares two artifacts against a
determinism mode and observable class list. Under `ModuloCommutativity` mode,
normalized commit traces are compared as multisets rather than sequences.

Observable classes still use the historical incumbent/path terms for backward
compatibility on deserialization, but the primary exported names are now the
generic selected-result terms. Observable classes include
`SelectedResultCost`, `SelectedResultWitnessIdentity`,
`SelectedResultPublicationTrace`, `NormalizedCommitTrace`,
`GraphEpochTrace`, `SchedulerProfileTrace`, and `ProgressAccounting`.

## Profiling Surface

The repo now includes an explicit profiling matrix for the generalized search
surface:

- end-to-end Criterion workloads in `rust/search/benches/search_profiles.rs`
- phase microbenchmarks in `rust/search/benches/search_machine_phases.rs`
- runtime-overhead microbenchmarks in
  `rust/search/benches/search_runtime_overheads.rs`
- structural counters in `rust/search/benches/support.rs`
- saved-profile helpers in `scripts/ops/profile-search-bench.sh`
- convenience entry points:
  - `just profile-search-chain`
  - `just profile-search-rebuild`
  - `just profile-search-threaded`
  - `just profile-search-machine-only`
  - `just profile-search-artifact`
  - `just profile-search-invariants`

The benchmark harness reports frontier growth, batch count, proposal churn,
duplicate elimination, commit count, rebuild count, and publication count so
performance work can separate generic machine cost from executor and artifact
overhead. The profiling surface should be used before making search-structure
optimizations; hotspot assumptions should not be treated as stable until after
the generalized query/result/authority surfaces are in place.

The profiling split is intentionally layered:

- algorithm/search work:
  `search_profiles` and the machine-only runtime-overhead bench
- executor/scheduler overhead:
  compare `runtime_machine_only_chain_256` against
  `runtime_executor_serial_chain_256`
- theorem/replay/artifact work:
  `runtime_observation_export_chain_256` and
  `runtime_full_state_export_chain_256`
- invariant-checking cost:
  `runtime_invariant_check_frontier_512`

Current review findings:

- replacing `next_batch(...)` full-frontier sorting with a naive two-pass
  min-score scan regressed both `phase_next_batch_frontier_512` and the
  end-to-end `serial_chain_256` workload, so that change was rejected
- duplicate-heavy and rebuild-heavy workloads still show normalization churn
  and rebuild work as stronger optimization candidates than batch extraction
- `normalize_proposals(...)` was then changed from full sort-plus-dedup to
  per-target best-selection after the duplicate-pressure phase bench isolated
  that stage as the stronger hotspot
- on `phase_normalize_proposals_duplicate_pressure_64x32`, that change reduced
  the measured phase time from roughly `120.75-132.44 µs` to
  `44.59-56.46 µs`
- the improved workload class is generic machine normalization cost on
  duplicate-heavy frontiers; it did not require theorem or artifact-schema
  changes
- any further optimization should be justified against those measured workload
  classes, not assumed from the frontier implementation alone

The `check-search-bench-tooling` just target is the regression guard for this
surface. It syntax-checks the saved-profile script and compiles the search
bench targets in both default and `multi-thread` configurations without
running them. `just check-search-tooling` now calls it, so the benchmark and
saved-profile surface is part of the normal search verification lane rather
than an optional local-only check.

## Lean Proof Support

The Lean formalization lives in `Runtime.Proofs.Search`. The public proof
surface is now split explicitly into a curated generic-machine barrel
(`Generic`) and the path-problem-specific completeness/publication family
(`PathProblems`), both re-exported through `API`. The supporting modules build
from frontier vocabulary through one-step fairness and artifact refinement into
full-machine semantics, liveness, completeness, and approximation-contract
inventory rows.

The per-profile fairness claim taxonomy determines what the runtime can assert
on behalf of each scheduler profile:

| Profile | `FairnessClaimClass` | Proof basis |
|---|---|---|
| `canonicalSerial` | `exactOneStep` | proved unconditionally |
| `threadedExactSingleLane` | `exactOneStepUnderRefinement` | proved via artifact equality |
| `batchedParallelExact` | `premisedWindowBounded` | proved under `BatchedExactWindowCertificate` |
| `batchedParallelEnvelopeBounded` | `premisedWindowBounded` | proved under `BatchedEnvelopeWindowCertificate` |

The batched profiles carry certified-window fairness, not end-to-end replay
equivalence. What each profile claims is exactly what Lean justifies.

### Proof Vocabulary (Core)

`Runtime.Proofs.Search.Core` establishes the foundational vocabulary:

- `FrontierEntry` - a `(node : Nat, priority : Nat)` pair, the unit of
  frontier membership.
- `IsMinPriority frontier entry` - `entry` is present in `frontier` and no
  other entry has strictly lower priority.
- `canonicalBatch frontier` - the list of all entries satisfying
  `IsMinPriority`. These are exactly the entries serviced in the next step.
- `frontierAfterCanonicalStep frontier` - the frontier with the canonical batch
  removed.
- `OneStepFair frontier` - every `IsMinPriority` entry is absent from
  `frontierAfterCanonicalStep frontier`.
- `CanonicalSerialTrace` - a dynamic frontier trace whose successive states are
  related by `frontierAfterCanonicalStep`.
- `EventuallyServicedWithin trace start bound entry` - `entry` is removed from
  `trace start` within `bound` steps.
- `ContinuouslyEligible`, `NoStrictlyBetterEntryAppears` - predicates used in
  the dynamic liveness theorem to constrain how the frontier evolves.

The reduced artifact structures `StepArtifact`, `StateSlice`, `ObservationSlice`,
and `StateArtifactSchema` define the boundary at which Lean and Rust search
states are compared. `BatchedExactWindowCertificate` is a proof-carrying record
whose fields provide evidence that a batched window covers the current canonical
batch and produces a commit for each covered entry. Downstream fairness theorems
are conditioned on holding one of these certificates.

### Fairness Proofs (Fairness)

`Runtime.Proofs.Search.Fairness` proves unconditional one-step fairness for
`canonicalSerial`. No fairness is claimed for entries outside the current
min-key batch.

- `mem_canonicalBatch_iff_isMinPriority` - membership in the canonical batch is
  equivalent to satisfying `IsMinPriority`. This connects the computational
  filter to the logical predicate.
- `canonical_batch_entries_removed_after_step` - every entry in the canonical
  batch is absent after the step. This is the core removal fact.
- `canonical_serial_one_step_fair_for_min_priority_entries` - if `entry`
  satisfies `IsMinPriority`, it is absent after one canonical step. This is the
  main one-step fairness result.
- `canonical_serial_batch_is_one_step_fair` - the full frontier is `OneStepFair`.
- `currently_min_priority_eventually_serviced_within_one_step` - in any
  `CanonicalSerialTrace`, a current `IsMinPriority` entry satisfies
  `EventuallyServicedWithin ... 1`. The service bound is exactly one step.
- `continuously_eligible_without_strictly_better_entries_eventually_serviced` -
  the dynamic liveness result: if an entry remains eligible and no strictly
  better entry arrives across a horizon, it is serviced within one step.

### Refinement Proofs (Refinement)

`Runtime.Proofs.Search.Refinement` proves that `threadedExactSingleLane` is
identical to canonical serial at every reduced artifact boundary. These are
equalities, not simulations: parallelisation of successor enumeration within a
batch produces no observable difference in batch nodes, normalized commits,
state, or observations.

- `threaded_exact_single_lane_step_artifact_refines_canonical` - the full
  `StepArtifact` is equal.
- `threaded_exact_single_lane_commit_trace_refines_canonical` and
  `threaded_exact_single_lane_batch_nodes_refine_canonical` - the
  `normalizedCommits` and `batchNodes` fields match individually.
- `threaded_exact_single_lane_state_slice_refines_canonical` and
  `threaded_exact_single_lane_observation_slice_refines_canonical` - the
  reduced `StateSlice` and `ObservationSlice` projections are equal.
- `threaded_exact_single_lane_multi_step_state_trace_refines_canonical`,
  `..._observation_trace_..._canonical`, and
  `..._state_artifact_trace_..._canonical` - all three multi-step trace
  functions agree across arbitrary `FrontierTrace` inputs.

### Executable Semantics (Executable)

`Runtime.Proofs.Search.Executable` is the semantic center of the search proof
lane: an executable reduced machine whose transitions and artifact projections
are all explicitly proved.

- `SearchMachineState` - reduced proof-relevant machine state carrying
  frontier, closed nodes, inconsistent nodes, score table, parent witnesses,
  incumbent, phase, and progress accounting.
- `MachineInvariants` - reduced machine invariant bundle covering
  open/closed disjointness, `incons ⊆ closed`, parent-score coherence,
  incumbent coherence, and nodup conditions.
- `executableCanonicalStep` - concrete reduced step function implementing
  canonical batch extraction, batch removal, normalized commit production,
  `open/closed/incons` movement, score updates, and reduced incumbent refresh.
- `stateSliceOfMachineState`, `observationSliceOfMachineState`, and
  `stateArtifactOfMachineState` - explicit Rust-facing reduced extraction
  functions from executable machine states into the reduced artifact vocabulary.

Key theorems:

- `executable_canonical_step_preserves_invariants` - executable reduced
  stepping preserves the reduced machine invariant bundle.
- `executable_step_artifact_refines_canonical_step_artifact` - the executable
  step refines exactly to the existing reduced step-artifact vocabulary.
- `runtime_state_artifact_of_machine_state_is_projection` - the reduced
  runtime-state artifact is an explicit projection of executable machine state.

### Machine Vocabulary (Machine)

`Runtime.Proofs.Search.Machine` packages the executable semantics into the
machine-facing theorem surface.

- `CanonicalMachineStep` - packaged executable reduced step plus current-state
  invariant bundle.
- `CanonicalMachineTrace` - machine trace version of canonical serial search.

Key theorems:

- `canonical_machine_step_services_current_min_priority_entries` - the
  machine-level step relation preserves the same one-step service fact as the
  frontier-only fairness layer.
- `canonical_machine_step_preserves_invariants` - machine invariants are
  preserved by the executable reduced step.
- `canonical_machine_trace_currently_min_priority_eventually_serviced` -
  machine traces inherit the frontier-facing one-step eventual-service theorem
  through frontier projection.
- `executable_trace_refines_canonical_machine_trace` - executable machine
  traces refine directly into the packaged machine-step theorem surface.
- `canonical_machine_step_artifact_refines_runtime_boundary` and
  `canonical_machine_state_artifact_is_runtime_projection` - explicit
  refinement back into the Rust-facing reduced artifact vocabulary.

### Full-Machine Semantics (FullMachine)

`Runtime.Proofs.Search.FullMachine` lifts the search lane above the reduced
frontier model into an executable proof-side machine that mirrors the
proof-relevant Rust state more closely.

- `FullSearchMachineState` - executable full-machine state carrying `OPEN`,
  `CLOSED`, `INCONS`, `g_score`, parent table, incumbent, epsilon, phase,
  epoch, snapshot, last batch, and commit/publication traces.
- `fullStepOnce`, `fullDecreaseEpsilonAndRebuild`, and
  `fullCommitEpochReconfiguration` - executable full-machine transitions for
  canonical stepping, rebuild, and epoch changes.
- `FullMachineInvariants` - full-machine invariant bundle covering
  open/closed discipline, `incons ⊆ closed`, parent-score coherence,
  publication coherence, incumbent coherence, and nodup conditions.
- `FullStateArtifactSchema` and `fullStateArtifactOfFullState` - explicit
  full-state artifact projection aligned with the Rust-side
  `SearchFullStateArtifact` export.

Key theorems:

- `full_state_artifact_of_full_state_is_runtime_projection` - the exported
  full-state artifact is exactly the projection of the Lean full-machine state.
- `reduced_state_of_full_state_preserves_machine_invariants` - the richer
  full-machine invariant bundle implies the existing reduced machine invariants.
- `full_activate_batch_preserves_invariants`,
  `full_apply_proposal_preserves_invariants`,
  `full_commit_proposals_preserves_invariants`,
  `full_decrease_epsilon_and_rebuild_preserves_invariants`,
  `full_commit_epoch_reconfiguration_preserves_invariants`, and
  `full_step_once_preserves_invariants` - the full-machine transition families
  have explicit invariant-preservation theorems.
- `full_activate_batch_refines_reduced_service_window` and
  `full_step_once_refines_reduced_executable_step` - the richer machine
  semantics refine back into the reduced executable step surface.

### Liveness Proofs (Liveness)

`Runtime.Proofs.Search.Liveness` extends the search lane beyond the current
min-key batch. All results are premise-scoped: termination is proved only for
the named premise bundles in the theorem statements, and completeness
assumptions are made explicit in the theorem premises rather than left as
documentation-only caveats.

Termination:

- `closed_nodes_length_le_reachable_length` - under the fixed-phase premise
  bundle, closed-node cardinality stays bounded by a finite reachable-node
  universe.
- `fixed_phase_canonical_serial_terminates_under_finite_reachable_bound` -
  fixed-phase canonical serial search terminates under an explicit finite
  reachable-node premise bundle.
- `rebuild_aware_canonical_serial_terminates_under_phase_work_measure` -
  rebuild-aware ARA-style termination under a lexicographic phase/work
  progress measure encoded into a natural descent argument.

Non-min fairness:

- `bounded_strict_preemption_eventually_becomes_min` - a continuously
  present non-min-priority entry eventually reaches the min-key window when the
  count of strictly better entries is bounded and decreases strictly while it
  remains non-min.
- `canonical_serial_nonmin_entry_eventually_serviced_under_bounded_strict_preemption`
  - composes the previous theorem with one-step fairness to obtain a service
  bound for non-min entries.
- `finite_better_entry_exhaustion_eventually_becomes_min` and
  `canonical_serial_nonmin_entry_eventually_serviced_under_finite_better_entry_exhaustion`
  - stronger variants using a finite better-entry universe rather than a
  numeric preemption bound.
- `canonical_serial_nonmin_entry_eventually_serviced_under_scheduler_fairness` -
  public scheduler-facing non-min fairness theorem with no internal preemption
  terminology exposed.

Completeness:

- `canonical_serial_goal_reached_from_ready_witness_path` - from an explicit
  ready witness path whose successive frontier entries become service-ready in
  order, the goal entry is eventually serviced.
- `canonical_machine_goal_reached_from_ready_witness_path` - machine-level
  version: executable canonical stepping closes the goal node within the
  witness-path horizon.
- `canonical_machine_goal_reached_from_graph_reachability` - completeness
  driven by an explicit graph-reachability premise bundle naming reachable-node
  path, finiteness, and heuristic assumptions.
- `canonical_machine_goal_reached_from_raw_successor_semantics` - public
  completeness theorem phrased over the raw successor contract, with
  ready-entry progress internalized behind an explicit refinement premise.
- `goal_reachability_connects_to_incumbent_publication` - machine-level bridge
  from bounded goal reachability to incumbent publication under an explicit
  publication premise bundle.
- `eventual_optimal_goal_publication_under_admissible_consistent_heuristic` -
  under explicit admissibility and consistency premises, eventual goal
  publication strengthens to eventual optimal-goal publication.

### Envelope Surface (Envelope)

`Runtime.Proofs.Search.Envelope` carries the certified-window theorem surface
for `batchedParallelEnvelopeBounded`. It provides the same certificate
structure as `batchedParallelExact` but scoped to the envelope-bounded service
window.

- `BatchedEnvelopeWindowCertificate` - theorem-side certificate object for one
  legal envelope-bounded service window.
- `certified_batched_envelope_window_is_fair` - every current `IsMinPriority`
  entry is removed within the certified envelope window.
- `certified_batched_envelope_window_eventually_services_min_priority_entries`
  - restates the one-window fairness theorem as `EventuallyServicedWithin ... 1`.
- `certified_envelope_window_trace_is_valid` - validates exported envelope
  certificate traces against the legal current min-key batch.

### Profile Claims (ProfileClaims)

`Runtime.Proofs.Search.ProfileClaims` derives the per-profile theorem surface
from the upstream proof modules, indexing each result by `SearchSchedulerProfile`
and `FairnessClaimClass`. The claim table at the top of this section shows what
each profile carries.

- `canonical_serial_profile_has_exact_one_step_fairness` and
  `canonical_serial_goal_window_service_has_exact_suffix_bound` - restate the
  `Fairness` results at profile granularity.
- `threaded_exact_single_lane_has_exact_one_step_fairness` - derives one-step
  fairness for the threaded profile by composing the `Refinement` equalities.
- `threaded_exact_single_lane_has_exact_observation_equivalence` -
  observation slices match canonical serial exactly.
- `certified_batched_exact_window_is_fair` - given a
  `BatchedExactWindowCertificate`, every `IsMinPriority` entry is removed
  within the certified window.
- `certified_batched_exact_window_eventually_services_min_priority_entries` -
  restates the above as an `EventuallyServicedWithin` bound of 1.
- `certified_batched_exact_window_bounded_dynamic_starvation_freedom` - given
  certificates for each step in a horizon, a `ContinuouslyEligible` entry
  under `BoundedPreemptionWindow` is serviced within `bound` steps.
- `certified_window_trace_is_valid_for_exact_batch_service` - validates that a
  certificate sequence matches the canonical batch at every step with a service
  bound of 1.
- `batched_parallel_envelope_claim_is_premised` - states formally that
  `batchedParallelEnvelopeBounded` carries the theorem-backed certified-window
  claim class.

### Theorem Inventory (Inventory and TheoremPack)

`Runtime.Proofs.Search.Inventory` records every theorem by name together with
a `Bool` indicating whether it is proved. `Runtime.Proofs.Search.TheoremPack`
exports a support classification for every row: `executableSemantics`,
`refinementCorollary`, or `premiseScoped`.

The inventory has 50 proved theorems and 0 unproved. Coverage includes
the full-machine artifact and projection surface, full-step refinement contracts
back into the reduced executable lane, a raw-successor completeness theorem
surface, scheduler-fair non-min service, and the certified-window envelope
profile theorems.

`Runtime.Proofs.Search.TheoremPack` wraps the inventory, support classes, and
two numeric bounds into a `SearchFairnessTheoremPack` structure. The mirrored
Rust `SearchTheoremPackArtifact` carries those same rows plus the release-gate
name:

```
inventorySupportClasses
canonicalServiceBoundSteps                 := 1
canonicalGoalWindowDiscoverySuffixBoundSteps := 1
```

Both bounds are exactly one step, matching the `EventuallyServicedWithin ... 1`
statements in `Fairness` and `ProfileClaims`. The dedicated local verification
gate is `just check-search-fairness`. The theorem-pack is exported through the
runtime API and written to `target/search-theorem-pack/search-theorem-pack.json`
for release and provenance checks. On the Rust side this appears in
`SearchTheoremPackArtifact` as both `inventory` and
`inventory_support_classes`, so downstream checks can distinguish executable
semantics theorems from refinement corollaries and premise-scoped theorems.

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

Reduced Lean/Rust parity covers canonical batch-window extraction,
proposal independence over declared authority surfaces, theorem-pack
support-class parity, the richer Rust full-state artifact boundary, and
epoch-barrier semantics with fairness-bundle fixtures. See
[Rust-Lean Bridge and Parity](802_rust_lean_parity.md) for the deviation registry and
parity policy.
