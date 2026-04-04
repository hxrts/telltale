# Simulation Viewer Webapp

This page describes the current shared Dioxus webapp surface for simulator
inspection.
It covers the crate split, global layout, ownership discipline, testing split,
and local development workflow.

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
checks, but the shared viewer is now the preferred human-facing inspection
surface for artifact summaries, graph browsing, and run insights.

## Related Docs

- [Simulation Overview](501_simulation_overview.md)
- [Simulation Viewer Model](505_simulation_viewer_model.md)
