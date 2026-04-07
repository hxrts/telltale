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
- semantic comparison results
- theorem-aware counterexamples
- deterministic sweep reports
- experiment-suite reports
- effect-trace artifacts
- minimization results

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
- compare two artifacts semantically
- find the first meaningful divergence between two artifacts
- load theorem-aware counterexamples
- load sweep explorer and experiment-suite reports
- load typed effect traces
- load deterministic minimization results
- load downstream extension manifests

Commands:

- import one artifact
- create a branch
- update a branch
- delete a branch
- request a rerun for a branch
- execute a deterministic archived-artifact sweep
- execute a baseline-vs-candidate experiment suite
- request a mocked rerun with typed effect overrides
- request deterministic minimization for a branch
- register downstream extension manifests

This is deliberate.
The UI should inspect authoritative artifacts through typed queries and emit
typed branch/scenario patch commands rather than mutate run state directly.

`ViewerReport` is the first canonical report model built from that query
surface.
It lets the UI render artifact inventories and scenario summaries without
opening downstream-specific assumptions in the Dioxus layer.

The newer reusable tooling surfaces build on that same boundary:

- `SemanticComparisonResult` for exact, normalization-equivalent, and
  safety-visible divergence classification
- `TheoremAwareCounterexample` for reusable theorem and divergence witnesses
- `DeterministicSweepReport` and `ExperimentSuiteReport` for archived sweep and
  baseline/candidate execution families
- `EffectTraceArtifact` and `EffectOverrideSpec` for effect inspection and
  mocked reruns
- `MinimizationRequest` and `MinimizationResult` for deterministic witness
  reduction
- `ViewerExtensionManifest` for downstream overlays, graph annotations, and
  time-travel extension panels

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

## Comparison and Counterexamples

Semantic comparison is now a first-class viewer concern.
The pure model layer exposes `SemanticComparisonRequest`,
`SemanticComparisonResult`, and `SemanticDivergencePoint`.
Those types deliberately sit above raw mismatch blobs:

- exact raw match stays distinct from normalization-equivalent match
- classification-only changes remain visible without being misreported as raw
  divergence
- the first semantically meaningful divergence is queryable directly

`TheoremAwareCounterexample` composes with that comparison surface.
It can be derived either from theorem-eligibility failure on one artifact or
from a comparison that leaves the expected semantic regime.
The viewer crate marks the helper constructors for these artifacts as
authoritative sources so the browser shell does not mint them locally.

## Sweeps, Effects, and Minimization

The pure model layer now also owns:

- deterministic archived-artifact sweep execution through `ExecuteSweep`
- baseline-vs-candidate experiment suites through `ExecuteExperimentSuite`
- typed effect inspection via `EffectTraceArtifact`
- typed mocked rerun requests via `EffectOverrideSpec`
- deterministic branch minimization via `MinimizationRequest`

These are still command/query surfaces, not browser-owned mutation.
The browser shell issues requests, and the application service owns the resulting
artifacts and summaries.

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

## Downstream Integration

Downstream projects should consume the shared viewer stack by importing the
stable artifact and extension contracts instead of forking the shell.
The supported downstream integration surface is now:

- viewer artifacts and query/command types from `telltale-viewer`
- extension manifests through `ViewerExtensionManifest`
- extension slots for overview panels, graph annotations, time-travel panels,
  and insight panels
- the existing ownership markers where they define public viewer/webapp
  boundaries, while narrower repo-local lint scripts remain internal

## Related Docs

- [Simulation Overview](501_simulation_overview.md)
- [Simulation Viewer Webapp](506_simulation_viewer_webapp.md)
- [Code Organization](105_code_organization.md)
