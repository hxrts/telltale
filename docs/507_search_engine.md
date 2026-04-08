# Search Engine

`telltale-search` is the planned generic weighted-graph search substrate for the
Telltale workspace.

The crate is intended to own:

- canonical search-machine semantics
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
