# Simulation Viewer Model

This page describes the Phase 1 model and service boundary for the simulator
webapp work.
It is intentionally about typed artifacts and application-service contracts,
not about Dioxus rendering.

## Scope

The simulator web stack is split into three layers:

- `telltale-viewer`: pure artifact loading, schema/version handling, branch
  patch types, query/command models, and the application-service boundary
- `telltale-ui`: the portable Dioxus UI core that consumes the `telltale-viewer`
  model layer
- `telltale-web`: the thin WASM/browser shell around `telltale-ui`

Only `telltale-viewer` exists at this phase.
Its job is to keep browser APIs and renderer-local state out of the
authoritative artifact boundary.

## Artifact Families

The viewer model is built around the simulator artifacts that already exist in
`telltale-simulator`.
The initial typed envelope supports these families:

- scenario bundles
- decision reports
- environment traces
- reconfiguration traces
- sweep manifests
- sweep diff reports
- scheduler comparisons
- observability comparisons
- approximation manifests
- contract-check reports

Each saved artifact uses one stable format marker and one explicit schema
version so later UI layers can reject unsupported files cleanly.

## Query and Command Split

The model layer uses an explicit command/query split.

Queries:

- load artifact inventories
- load one artifact
- load scenario summaries
- load branch-lineage projections
- request graph projections
- search loaded artifacts
- select one historical inspection position

Commands:

- import one artifact
- create a branch
- update a branch
- delete a branch
- request a rerun for a branch

This is deliberate.
The UI should inspect authoritative artifacts through typed queries and emit
typed branch/scenario patch commands rather than mutate run state directly.

## Branch Patches

Branch editing is patch-based.
The model layer defines `ScenarioBranchPatch` and `ScenarioPatchOperation`
instead of exposing direct mutable scenario state to the UI.

The current patch surface includes:

- scenario metadata updates such as name, seed, and steps
- execution policy updates
- theorem-profile replacement
- extension updates
- reconfiguration replacement
- full scenario replacement when the caller already owns a canonical scenario

Later phases can extend the patch language, but the UI should continue to emit
typed deltas rather than mutate simulator state in place.

## Application Service

`ViewerApplicationService` is the stable boundary between the pure model layer
and the future UI/web layers.
The first implementation is `InMemoryViewerService`.

Even though the initial service is in-process, the boundary is already shaped
like a real application service:

- queries return typed model projections
- commands mutate branch/workspace state explicitly
- the browser shell does not become the semantic owner of simulation state

## Related Docs

- [Simulation Overview](501_simulation_overview.md)
- [Code Organization](105_code_organization.md)
