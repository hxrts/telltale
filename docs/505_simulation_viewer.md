# Simulation Viewer

This page describes the typed model and service boundary for the simulator
webapp work.
It is intentionally about artifacts and application-service contracts first,
with only the minimum crate-split notes needed to explain how `telltale-ui`
and `telltale-web` consume it.

## Scope

The simulator web stack is split into three layers:

- `telltale-viewer`: pure artifact loading, schema/version handling, branch
  patch types, query/command models, and the application-service boundary
- `telltale-ui`: the portable Dioxus UI core that consumes the `telltale-viewer`
  model layer
- `telltale-web`: the thin WASM/browser shell around `telltale-ui`

`telltale-viewer` keeps browser APIs and renderer-local state out of the
authoritative artifact boundary.
`telltale-ui` and `telltale-web` are now present, but they are intentionally
downstream of this crate split rather than new semantic authorities.

The viewer layer now also owns the typed command builders used by the
graph/time-travel workspace.
That keeps branch patch construction in `telltale-viewer` and lets
`telltale-ui` stay an `Observed` command-emission shell instead of directly
authoring patch details.

## Artifact Families

The viewer is built around the simulator artifacts that already exist in
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

`ViewerReport` is the first canonical report model built from that query
surface.
It lets the UI render artifact inventories and scenario summaries without
opening downstream-specific assumptions in the Dioxus layer.

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

## Ownership and Portability Notes

The shared viewer stack borrows Aura's split and ownership discipline:

- `telltale-viewer` remains pure and renderer-free
- `telltale-ui` is an `Observed` surface over authoritative artifacts
- `telltale-web` is the thin browser shell and owns `Dioxus.toml`,
  `index.html`, Tailwind packaging, and future browser-only APIs

The first shared ownership-marker set comes from `telltale-macros`:

- `#[observed_only]`
- `#[actor_owned("...")]`
- `#[authoritative_source("...")]`
- `#[strong_reference("...")]`
- `#[weak_identifier("...")]`

These markers are intentionally lightweight.
They validate the declared boundary shape and are backed by compile-fail tests
and repo-level boundary checks.

## Related Docs

- [Simulation Overview](501_simulation_overview.md)
- [Simulation Viewer Webapp](506_simulation_viewer_webapp.md)
- [Code Organization](105_code_organization.md)
