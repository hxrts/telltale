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
- `SearchMachine` and `SearchState`
- `CanonicalBatch`, `Proposal`, and canonical path reconstruction
- explicit invariant checks for partition discipline, parent-score coherence,
  incumbent coherence, and batch legality
- determinism, scheduler, fairness, and observable capability vocabulary
- `SearchObservationArtifact` and `compare_observations(...)` for profile-aware
  artifact comparison

The current runtime surface adds:

- `ProposalExecutor`, `SerialProposalExecutor`, and `NativeParallelExecutor`
- authority read/write summaries for speculative proposals
- `run_with_executor(...)` for canonical host execution over speculative work
- `SchedulerArtifact`, `SchedulerArtifactClass`, and `ProgressSummary`
- `SearchReplayArtifact`, `ReplayExpectation`, and `replay_observation(...)`
- `EpochReconfigurationRequest` and `commit_epoch_reconfiguration(...)`

Target support:

- the core serial machine is target-agnostic
- the optional `multi-thread` feature enables the native parallel executor
- WASM builds use the same canonical serial and replay surface without `rayon`

Optional integration layers now exist above the crate boundary:

- `telltale-simulator` can project search runs through `project_search_run(...)`
- `telltale-viewer` can project search artifacts through `project_search_artifacts(...)`

Reduced Lean/Rust parity currently covers:

- canonical batch-window extraction
- proposal independence over declared authority surfaces
- replay epoch and phase contracts
- epoch-barrier semantics and fairness-bundle fixtures
