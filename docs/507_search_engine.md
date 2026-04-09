# Search Engine

`telltale-search` is the generic weighted-graph search substrate for the
Telltale workspace.

The crate is intended to own:

- canonical search-machine semantics
- deterministic serial min-key batch extraction
- canonical proposal normalization and commit
- determinism, scheduler, and fairness capability vocabulary
- replay and comparison artifacts
- explicit graph-epoch and snapshot boundaries

The crate is intentionally generic and downstream-oriented.

Downstream crates should provide:

- domain-specific node and edge semantics
- heuristic and cost policies
- application-specific graph snapshots and epoch updates
- product-specific reports or overlays

Simulator and viewer integration are optional layers above the core crate.
`telltale-search` itself should remain free of simulator, viewer, browser, and
application-specific routing dependencies.

The current serial-core surface includes:

- `SearchCost` and `EpsilonMilli`
- `SearchDomain`
- `SearchMachine`
- `CanonicalBatch`, `Proposal`, and canonical path reconstruction
- explicit invariant checks for partition discipline, parent-score coherence,
  incumbent coherence, and batch legality
- determinism, scheduler, fairness, and observable capability vocabulary
- `SearchObservationArtifact` and `compare_observations(...)` for profile-aware
  artifact comparison, including canonical parent identity and incumbent
  publication traces

The current runtime surface adds:

- `ProposalExecutor`, `SerialProposalExecutor`, and `NativeParallelExecutor`
- `SearchRunConfig` for typed runtime configuration instead of positional
  scheduler/fairness arguments
- fail-closed `validate_run_config(...)` / `SearchRunConfigError` checks for
  scheduler-profile, executor-kind, fairness, and batch-width mismatches
- full legal min-key batch execution, with `batch_width` controlling worker
  chunking rather than canonical batch membership
- authority read/write summaries for speculative proposals
- `run_with_executor(...)` for canonical host execution over speculative work
- `SchedulerArtifact`, `SchedulerArtifactClass`, and `ProgressSummary`
- `SearchFairnessArtifact`, `SearchFairnessCertificate`, and
  `SearchFairnessClaimClass` for public profile-scoped fairness classification,
  representative certified-window evidence, theorem-backed observable sets,
  normalization mode, certified epoch/phase identity, and exact refinement
  flags for the reduced state and observable slices
- `SearchRouteBoundArtifact`, `SearchRouteDiscoveryBoundClass`, and
  `SearchRouteQualityClass` for selected-route discovery and quality reporting,
  including the observed scheduler-step bound to the first candidate route,
  the observed bound to first goal-window entry,
  the theorem-backed one-step service bound once the goal is in the legal
  service window, a structured `SearchRouteDiscoveryCertificate`, recovery
  after the latest epoch transition, exact-optimal quality for exact profiles,
  weaker premise-scoped quality classes for the non-exact profiles, and a
  compact `SearchRouteSummary` with stable generic metric entries
- `theorem_backed_observables(...)` and `search_theorem_pack_artifact()` for
  exporting the current theorem-backed comparison surface and release-facing
  search theorem-pack artifact
- `SearchStateArtifact` plus per-round state/certificate traces in replay-ready
  runtime artifacts for exact-profile and certified-window correspondence
- `SearchReplayArtifact`, `ReplayExpectation`, and `replay_observation(...)`
- `EpochReconfigurationRequest` and `commit_epoch_reconfiguration(...)`

Replay and reconfiguration semantics are fail-closed:

- runtime failures during proposal generation do not consume the canonical batch
- replay derives the final observation from canonical round commits and rejects
  drift against the stored artifact, epoch schedule, snapshot schedule, phase
  schedule, and batch schedule
- epoch reconfiguration resets canonical frontier, parent, and incumbent state,
  then re-seeds the new epoch from the start node
- fairness assumptions are first-class observable artifacts and comparison
  inputs

Lean proof support now includes a scoped fairness result for the canonical
serial scheduler:

- `Runtime.Proofs.Search.API` provides a search-specific fairness vocabulary
  over dynamic frontier entries rather than fixed scheduler roles
- `Runtime.Proofs.Search.Fairness` proves that every entry in the current legal
  min-key batch is serviced by the next canonical serial step, and restates that
  as an eventual-service theorem with bound `1`
- the same module now also exposes a dynamic liveness theorem under an explicit
  stability premise: continuously eligible entries with no strictly better
  competing entry are eventually serviced
- `Runtime.Proofs.Search.Refinement` proves reduced exact single-lane threaded
  refinement down to batch-node, normalized-commit-trace, reduced state-slice,
  and reduced observation-slice equality with canonical serial search
- `Runtime.Proofs.Search.TheoremPack` packages the current search fairness
  theorem inventory as a first-class Lean artifact, and the dedicated local
  gate is `just check-search-fairness`
- `Runtime.Proofs.Search.Refinement` now also exposes multi-step exact threaded
  refinement theorems for reduced state-slice and observation-slice traces
- `Runtime.Proofs.Search.ProfileClaims` separates the public fairness story by
  runtime profile:
  - canonical serial: exact one-step fairness
  - threaded exact single-lane: exact one-step fairness proved through a
    reduced one-step, commit-trace, full reduced state-slice, and reduced
    observation-slice refinement theorem to canonical serial search
  - batched exact: premise-scoped bounded-window fairness via a certified
    current-window theorem plus a bounded dynamic starvation-freedom theorem
    under an explicit bounded-preemption premise
  - envelope-bounded batched: premise-only, not an unconditional fairness theorem
- the Rust runtime now emits the same profile-scoped fairness classification in
  `SearchFairnessArtifact` and `SearchFairnessCertificate`, including a
  representative certified-window payload, theorem-backed observable classes,
  normalization mode, and exact state/observation refinement flags for exact
  profiles, and replay preserves that artifact verbatim
- exact runtime reports now also export `SearchStateArtifact`, per-round
  fairness certificate traces, and per-round state artifacts so multi-step
  exact correspondence can be checked against the public Rust surface directly
- exact runtime reports and replay artifacts now also export
  `SearchRouteBoundArtifact`, which currently provides an observed
  run-scoped bound to first candidate discovery, an observed recovery bound
  after the latest epoch transition, an observed bound to first goal-window
  entry, and a theorem-backed one-step goal-window service bound derived from
  the fairness certificate surface. The structured
  `SearchRouteDiscoveryCertificate` now records both the theorem class and the
  exact observed steps to which the certificate is attached, so downstream
  consumers can distinguish the observed prefix from the proved final suffix.
  The route summary carries both scalar convenience fields and a stable generic
  metric list for downstream reporting. This is intentionally narrower than a full theorem-backed
  end-to-end discovery-time guarantee
- the search theorem-pack artifact is exported through the runtime API and
  through the generated JSON at `target/search-theorem-pack/search-theorem-pack.json`
  for release/provenance checks
- stable source-controlled search artifact vectors are exported through
  `cargo run -p telltale-search --example export_vectors` and checked by the
  `search_vectors` conformance test so theorem-pack, final-state, fairness,
  and replay artifact drift is caught explicitly
- a separate recovery vector surface is exported through
  `cargo run -p telltale-search --example export_recovery_vectors` and checked
  by `search_recovery_vectors` so epoch-transition recovery bounds and route
  summaries remain pinned to source-controlled artifacts
- the release/provenance lane now records both the theorem-pack JSON and the
  generated canonical vector artifact at
  `target/search-artifacts/search-vectors-v1.json`, plus the generated recovery
  vector artifact at
  `target/search-artifacts/search-recovery-vectors-v1.json`, so search
  conformance leaves a first-class audit trail alongside the package tarballs
- this is intentionally narrower than a global fairness claim for arbitrary
  future frontier growth or for all parallel modes without additional premises

Target support:

- the core serial machine is target-agnostic
- the optional `multi-thread` feature enables the native parallel executor;
  constructing `NativeParallelExecutor` without it fails explicitly rather than
  silently degrading to serial execution
- WASM builds use the same canonical serial and replay surface without `rayon`

Optional integration layers now exist above the crate boundary:

- `telltale-simulator` can project search runs through `project_search_run(...)`
- `telltale-viewer` can project search artifacts through `project_search_artifacts(...)`

Reduced Lean/Rust parity currently covers:

- canonical batch-window extraction
- proposal independence over declared authority surfaces
- replay epoch and phase contracts
- epoch-barrier semantics and fairness-bundle fixtures
