# Simulation Viewer Webapp

This page describes the current shared Dioxus webapp surface for simulator
inspection.
It covers the crate split, global layout, graph and run-insight workspaces,
ownership discipline, testing split, and local development workflow.

## Crate Split

The viewer web stack is intentionally split into three crates:

- `telltale-viewer`: pure artifact envelopes, report/query/command models,
  branch patching, and the application-service boundary
- `telltale-ui`: portable Dioxus UI core with the shared shell, reusable
  components, graph rendering, route/view state, and task-owner helpers
- `telltale-web`: thin browser shell with `Dioxus.toml`, `index.html`,
  Tailwind packaging, and future browser-only integration

Only `telltale-web` may own browser APIs.
`telltale-ui` and `telltale-viewer` must stay portable.

## App Ownership Model

The viewer is an `Observed` surface over authoritative simulator artifacts.
It may shape presentation, selection, and browser-local layout state, but it
must not become the semantic owner of simulation truth.

The current ownership markers used by the shared viewer stack are:

- `#[observed_only]` for render/projection helpers
- `#[actor_owned("...")]` for long-lived task/runtime helpers
- `#[authoritative_source("...")]` for the narrow surfaces that publish
  authoritative demo or derived outputs
- `#[strong_reference("...")]` and `#[weak_identifier("...")]` for typed
  reference/identifier boundaries

These are intentionally structural.
The real semantic authority still lives in simulator artifacts and the
application-service boundary.

## Graph Workspace and Time Travel

The shared webapp now includes a graph workspace for deterministic structure
and replay browsing.
The graph page can switch between these projection families from the same
authoritative artifact set:

- choreography structure
- instantiated protocol structure
- execution timeline
- branch lineage

Time travel is explicit.
Users can:

- step forward and backward through deterministic execution history
- jump directly to a historical step
- switch projections without losing typed selection state
- search nodes, branches, and labels through the pure `telltale-viewer` index

Branch management is command-driven rather than mutation-driven.
The graph workspace emits typed viewer commands for:

- branch creation from the active historical step
- branch update through a typed patch
- branch deletion

Those commands are minted in `telltale-viewer`, while `telltale-ui` remains an
`Observed` shell over the resulting command stream and graph projections.

## Run Insight Workspace

The insight page is the companion debugging surface for one active run or
branch.
It currently renders:

- execution regime and theorem scheduler profile
- watch expressions over sampled semantic facts
- branch provenance and narrative annotations
- a run-diff summary for the active branch
- causality/explanation rows derived from the execution timeline projection
- bookmarks for historical steps and branches
- archive reload status for exact artifact-set re-entry

This gives the viewer a first serious run-analysis lane instead of only a
graph browser.

The archive controls are intentionally part of the insight workspace rather
than a separate browser-owned workflow.
Reloading an archived artifact set preserves the deterministic viewer state,
and any subsequent branch fork still goes back through the typed command path
instead of mutating the archived run in place.

## Downstream Handoff

Aura is unblocked to start integrating once it consumes these shared surfaces:

- `telltale_viewer::ViewerArtifactFile` and `telltale_viewer::ViewerArtifact`
  as the stable artifact envelope
- `telltale_viewer::ViewerReport`, `ViewerQuery`, `ViewerCommand`, and
  `ViewerApplicationService` as the query/command boundary
- `telltale_viewer::GraphProjection` and `GraphProjectionKind` as the graph
  projection contract
- `telltale_ui::TelltaleUiRoot`, `ViewerFrame`, `ViewerPage`, and
  `ViewerWorkspace` as the portable Dioxus shell and shared workspace model

The intended downstream extension points are:

- artifact and insight overlays layered on top of the shared pages
- graph annotations and domain-specific badges that do not replace the
  authoritative projection contract
- downstream application-service implementations that feed the same
  query/command surface

Downstreams should not fork the core shell just to add overlays.
The shared Telltale crates now provide the minimum handoff surface Aura needs.

## Testing Split

The viewer work uses an explicit three-way testing split:

- pure model tests in `telltale-viewer`
- ownership/compile-fail/boundary checks in `telltale-macros` and
  `scripts/check/viewer-tooling-boundaries.sh`
- Dioxus shell integration tests in `telltale-ui`

The canonical local/CI recipe is `just check-viewer-tooling`.
That recipe runs the pure model tests, the UI shell tests, the thin web-shell
compile, and the boundary check script.

## Local Development

For the current shared web shell:

```text
cd rust/web
npm install
npm run tailwind:watch
dx serve --platform web
```

The Dioxus watcher is configured to watch:

- `rust/web/src`
- `rust/ui/src`
- `rust/web/styles`
- `rust/web/public`

The browser shell currently loads the demo workspace through the typed
application-service path so the shared shell, graph, and insight surfaces are
all exercised from one entrypoint.

## Simulator CLI Note

Textual replay output remains available for compatibility and quick terminal
checks, but it is now explicitly a compatibility summary path.
The shared viewer is the preferred human-facing inspection surface for graph
navigation, time travel, branch management, and run insights.

## Related Docs

- [Simulation Overview](501_simulation_overview.md)
- [Simulation Viewer](505_simulation_viewer.md)
