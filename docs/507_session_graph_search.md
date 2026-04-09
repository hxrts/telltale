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

The Lean formalization provides scoped fairness and refinement results for the
canonical serial scheduler. `Runtime.Proofs.Search.API` defines a
search-specific fairness vocabulary over dynamic frontier entries.
`Runtime.Proofs.Search.Fairness` proves that every entry in the current legal
min-key batch is serviced by the next canonical serial step, restated as an
eventual-service theorem with bound 1.

`Runtime.Proofs.Search.Refinement` proves reduced exact single-lane threaded
refinement down to batch-node, normalized-commit-trace, reduced state-slice,
and reduced observation-slice equality with canonical serial search. The same
module exposes multi-step exact threaded refinement theorems for reduced
state-slice and observation-slice traces.

`Runtime.Proofs.Search.ProfileClaims` separates the public fairness story by
runtime profile. Canonical serial provides exact one-step fairness. Threaded
exact single-lane proves exact one-step fairness through a reduced refinement
theorem to canonical serial search. Batched exact provides premise-scoped
bounded-window fairness via a certified current-window theorem and a bounded
dynamic starvation-freedom theorem under an explicit bounded-preemption premise.
Envelope-bounded batched provides premise-only classification without an
unconditional fairness theorem.

`Runtime.Proofs.Search.TheoremPack` packages the theorem inventory as a
first-class Lean artifact. The dedicated local gate is
`just check-search-fairness`. The search theorem-pack artifact is also exported
through the runtime API and through the generated JSON at
`target/search-theorem-pack/search-theorem-pack.json` for release and
provenance checks.

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
