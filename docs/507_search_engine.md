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
