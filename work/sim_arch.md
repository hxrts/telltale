# Simulator Architecture Remediation

This document tracks the simulator architectural cleanup needed to make the crate internally coherent, generic at the integration boundary, and explicit about what it guarantees.
When a phase replaces an old surface, remove the old surface in that same phase.
Do not keep backwards-compatibility aliases, wrappers, dual schemas, or legacy code paths unless a task explicitly says otherwise.

## Success Criteria

- The simulator has one shared scenario execution engine used by both normal runs and replay.
- Fault and network middleware compose through one transport path. A message delayed by one middleware layer must still pass through the remaining active transport policies.
- The generic harness path does not require built-in material parameters. Built-in material configuration is only required by material-driven adapters and CLIs that opt into it.
- The simulator schema does not expose dead or misleading fields. Every public configuration field must be consumed by a canonical execution path.
- Generated-effect helper APIs remain available only as helper surfaces, not as top-level simulator entrypoints.
- Trace sampling is driven by explicit simulator round semantics rather than inferred from `ObsEvent::Invoked` counts.
- Property parsing has one canonical implementation. Scenario property loading should lower into the same property model without a parallel parser layer.
- Targeted tests cover middleware composition, generic harness execution without materials, shared replay/run semantics, and updated public API expectations.
- Simulator docs describe the new execution model and public surfaces accurately.
- The simulator exposes backend choice, scheduler concurrency, and worker-thread count as separate concepts instead of overloading one `concurrency` field.
- Default single-scenario execution resolves to the authoritative serialized canonical regime rather than a host-parallel auto lane.
- The simulator provides a deterministic batch-run surface for speeding up many independent runs while preserving input-order results.
- The simulator can run one scenario on a threaded protocol-machine backend when the threaded machine feature is enabled.
- Canonical and threaded simulator runs agree on authoritative outputs for the same scenario, seed, and resolved scheduler configuration.
- Docs explain which execution settings change semantics, which only change performance, and which mode is authoritative for replay/debugging.
- Simulator profiles are theorem-indexed. A run can report not only transport/fault settings, but also which Telltale assumption bundle, scheduler profile, envelope profile, and proof-side eligibility status applied.
- Simulator outputs can classify runs using Telltale-native quantities such as weighted progress measure, productive-step budget, scheduler-lift bounds, and critical-capacity phase.
- Topology change, delegation, handoff, and mode transition are representable as first-class reconfiguration operations rather than only as ad hoc link toggles.
- The simulator can distinguish raw trace differences from semantically normalized differences through envelope-aware observability and exchange/spatial normalization surfaces.
- Failure results can include theorem-native witnesses or counterexamples for decision procedures, capacity violations, envelope-admission failures, and distributed-assumption failures.
- Fault injection supports explicit adversarial/failure budgets and reports which budget or assumption clause failed instead of only surfacing low-level packet effects.
- Scheduler comparisons can be stated in Telltale-native terms: productive exactness, conservative total-step lift, fairness requirements, and envelope adherence.
- The simulator can compare exact protocol-machine execution to approximation layers such as batched stochastic, fluid, or mean-field regimes with explicit theorem-side scope.
- Batch and sweep outputs are proof-carrying experiment artifacts: resolved settings, assumption bundles, theorem eligibility, certificates, witnesses, and authoritative results are recorded in one reproducible manifest.
- Domain-specific simulators can extend Telltale through generic environment/model hooks without adding protocol- or domain-branded fields to the core simulator schema.
- Core simulator abstractions cover topology, medium effects, mobility, node capabilities, and admission/capacity constraints in domain-neutral terms.
- The simulator’s current material-model surface is replaced by a field/environment-dynamics surface suitable for interference fields, occupancy fields, and other shared environment state, and the legacy material API surface is removed rather than retained as compatibility shims.
- External projects can provide their own environment models, capability profiles, and artifact interpreters through public traits/interfaces rather than by patching Telltale internals.
- Core docs and tests explicitly guard against Bluetooth-specific or other vertical-specific logic leaking into `telltale-simulator`.

## Phase 1: Shared Execution Core

- [x] Add a shared scenario execution engine that owns middleware ticking, delivery, paused-role propagation, property checks, and checkpointing.
- [x] Refactor `run_with_scenario(...)` to use the shared engine.
- [x] Refactor `rust/simulator/src/bin/replay.rs` to use the same shared engine instead of duplicating the loop.
- [x] Fix middleware composition so fault-delayed messages re-enter through the network policy stage when network middleware is active.
- [x] Add targeted tests covering fault+network composition and replay/run loop equivalence.
- [x] Run targeted simulator tests for the shared execution core.
- [x] Make a git commit for Phase 1.

## Phase 2: Generic Integration Boundary

- [x] Make built-in scenario materials optional at the schema level.
- [x] Restrict built-in material requirements to material-driven surfaces such as `MaterialAdapter` and the simulator CLI.
- [x] Keep generic harness execution working when the caller supplies handler-owned initial state without built-in material params.
- [x] Remove `Scenario.output` and the related dead output types from the simulator schema and presets.
- [x] Demote generated-effect helper types out of the crate-root re-export surface and update generated-code imports to use the helper module directly.
- [x] Add targeted tests covering generic harness execution without scenario materials and updated public API paths.
- [x] Run targeted simulator and language tests for the generic integration boundary.
- [x] Make a git commit for Phase 2.

## Phase 3: Sampling and Verification Cleanup

- [x] Replace invoke-count-based trace sampling with explicit round-based sampling in the simulator runner.
- [x] Remove the duplicate scenario invariant parser module and move canonical property parsing into the property layer.
- [x] Keep post-run contracts and offline analysis as distinct phases, but make the property-loading path clearly lower into one `Property` model.
- [x] Add targeted tests covering round-based sampling and scenario property parsing.
- [x] Run targeted simulator tests for sampling and verification behavior.
- [x] Make a git commit for Phase 3.

## Phase 4: Documentation

- [x] Update simulator docs to describe the shared execution core, middleware ordering, generic/material boundaries, and round-based sampling.
- [x] Update API and getting-started docs for the simulator public-surface changes.
- [x] Re-read the touched docs for consistency with the implemented code paths.
- [x] Make a git commit for Phase 4.

## Phase 5: Execution Policy and Backend Surface

- [x] Replace the top-level scenario `concurrency` field with an `execution` block that separates backend choice, scheduler concurrency, and worker-thread count.
- [x] Add the initial auto-resolution policy and execution-resolution surface that Phase 8A later tightens to an authoritative single-run default.
- [x] Record resolved execution settings in simulator stats/output so environment-dependent defaults remain observable.
- [x] Keep run and replay paths using the same resolved execution contract.
- [x] Update scenario presets, parser tests, and runner tests to the new execution schema.
- [x] Run targeted simulator tests for execution config parsing and resolved-default behavior.
- [x] Make a git commit for Phase 5.

## Phase 6: Deterministic Batch Parallelism

- [x] Add a batch harness surface for running many independent harness specs concurrently.
- [x] Preserve deterministic result ordering by input index regardless of worker scheduling.
- [x] Default batch parallelism to host parallelism outside CI and to one worker in CI.
- [x] Add targeted tests for deterministic ordering and CI/default worker resolution.
- [x] Run targeted simulator tests for batch execution.
- [x] Make a git commit for Phase 6.

## Phase 7: Threaded Scenario Backend

- [x] Add simulator backend abstraction so the shared execution loop can run on either the canonical or threaded protocol machine.
- [x] Extend the threaded protocol machine with the public state/snapshot hooks the simulator needs for initial-state injection, trace sampling, property checks, and paused-role propagation.
- [x] Add feature-gated threaded simulator execution using `telltale-machine/multi-thread`.
- [x] Keep canonical replay as the authoritative replay lane, while allowing threaded runs to emit compatible replay artifacts.
- [x] Add targeted parity tests comparing canonical and threaded simulator outputs for the same scenario and seed.
- [x] Run targeted simulator and machine tests for threaded execution and parity.
- [x] Make a git commit for Phase 7.

## Phase 8: Determinism Contract and Documentation

- [x] Update simulator docs to explain backend selection, scheduler concurrency, worker threads, auto defaults, CI behavior, and canonical replay authority.
- [x] Update API docs and examples to show batch execution and explicit execution configuration for reproducibility.
- [x] Re-read the touched docs for consistency with the implemented execution behavior.
- [x] Make a git commit for Phase 8.

## Phase 8A: Authoritative Concurrency Contract

- [x] Change single-scenario auto execution defaults to an authoritative serialized regime rather than a host-parallel regime.
- [x] Keep batch parallelism and other throughput-oriented surfaces separate from authoritative single-run execution defaults.
- [x] Pin threaded simulator execution explicitly to the proof-aligned canonical one-step threaded round semantics instead of inheriting that choice implicitly from machine defaults.
- [x] Add an explicit execution-regime classification to simulator stats/artifacts that distinguishes exact canonical runs, exact threaded `n = 1` runs, and envelope-bounded threaded `n > 1` runs.
- [x] Add targeted tests for authoritative auto resolution, execution-regime reporting, and worker-thread invariance for fixed threaded scheduler concurrency.
- [x] Rename the canonical-only multi-session runner helper so it does not imply that it honors scenario-level threaded execution settings.
- [x] Update simulator docs to explain the new authoritative default and the execution-regime classification.
- [x] Remove any superseded host-parallel auto-default code paths, stale stats fields, and compatibility branches instead of retaining both regimes behind legacy shims.
- [x] Make a git commit for Phase 8A.

## Phase 8B: Hierarchical VM-Native Simulation Foundation

- [x] Promote nested/distributed simulation into explicit outer/inner execution vocabulary rather than leaving it as an implicit builder-only detail.
- [x] Add a public outer/inner execution contract type for nested simulation that records outer scheduler concurrency and inner rounds-per-step.
- [x] Expose the nested execution contract through the distributed simulation public API so downstream integrations can inspect the authoritative outer/inner VM structure directly.
- [x] Keep nested VM semantics distinct from worker-thread/performance parallelism in public types and docs.
- [x] Add targeted tests that nested execution contracts are observable and stable through the public distributed-simulation surface.
- [x] Update simulator docs to explain the hierarchical VM-native execution model and its distinction from performance parallelism.
- [x] Remove any builder-only or implicit nested-execution legacy surface that becomes redundant once the public execution contract exists. Do not keep parallel old/new nested APIs.
- [x] Make a git commit for Phase 8B.

## Phase 9: Theorem-Indexed Simulation Profiles

- [x] Add a first-class theorem/profile layer for simulator runs that records scheduler profile, envelope profile, transport/fault assumption bundle, and eligibility for theorem-backed outputs.
- [x] Separate raw execution settings from theorem assumptions so the simulator can say both "what ran" and "what proof-side contract, if any, applies".
- [x] Emit resolved theorem/profile information in run statistics, replay artifacts, and batch manifests.
- [x] Add targeted tests showing that the same execution can be classified differently under different declared theorem profiles without changing raw runtime behavior.
- [x] Update simulator docs to explain theorem-indexed profiles and assumption-bundle reporting.
- [x] Remove any older ad hoc profile/status reporting once theorem-indexed profiles exist. Do not keep duplicate reporting surfaces for the same concept.
- [x] Make a git commit for Phase 9.

## Phase 10: Capacity, Stability, and Phase Classification

- [x] Add weighted-measure accounting to simulator runs so each scenario can report protocol-level progress potential, productive-step count, and remaining budget.
- [x] Expose scheduler-lifted total-step bounds when the selected scheduler profile provides them, and report when only productive exactness is available.
- [x] Add critical-capacity and phase-classification reporting for supported scenarios, including below/at/above threshold classification.
- [x] Keep theorem-native classifications distinct from raw transport counters such as queue length or message count.
- [x] Add targeted tests for weighted-measure descent reporting, productive-step accounting, and phase-boundary classification.
- [x] Update simulator docs and examples to explain theorem-native run summaries.
- [x] Remove any superseded approximate or transport-counter-only summary code that overlaps with the new theorem-native reporting surface. No compatibility summaries.
- [x] Make a git commit for Phase 10.

## Phase 11: Reconfiguration-Native Topology and Handoff

- [x] Introduce first-class simulator reconfiguration operations for link, delegation, handoff, federation, and mode transition instead of modeling all topology changes as low-level transport events.
- [x] Reuse one canonical representation for reconfiguration traces across normal runs, replay, and analysis tooling.
- [x] Add explicit footprint/well-formedness validation for topology-changing operations before they enter the execution core.
- [x] Distinguish pure reconfiguration from budget-consuming transition choreography so conservation and descent are reported separately.
- [x] Add targeted tests for delegation safety, footprint-local updates, handoff replay, and reconfiguration/run equivalence.
- [x] Update docs to explain when a scenario should use transport faults versus semantic reconfiguration operations.
- [x] Remove legacy topology-change encodings that become redundant once first-class reconfiguration operations exist. Do not keep old ad hoc encodings as compatibility paths.
- [x] Make a git commit for Phase 11.

## Phase 12: Envelope-Aware Observability and Normalization

- [x] Add a normalized observability layer that groups traces modulo exchange normalization and spatial refinement rather than only exposing raw event order.
- [x] Extend simulator outputs so users can inspect both raw traces and envelope-normalized behavior classes.
- [x] Report whether two runs differ only by admissible exchange/spatial normalization or by safety-visible semantic divergence.
- [x] Keep replay/debugging anchored to canonical authoritative traces while allowing normalized comparison views for analysis.
- [x] Add targeted tests for normalization-aware equivalence and non-equivalence reporting.
- [x] Update simulator docs to explain raw trace vs normalized envelope trace semantics.
- [x] Remove any older comparison/reporting surface that duplicates the new normalized observability contract. Do not retain parallel legacy diff modes.
- [x] Make a git commit for Phase 12.

## Phase 13: Decision Procedures and Counterexample Surfaces

- [x] Add simulator-facing decision/checker APIs for regular-fragment properties such as branching feasibility, async-subtyping-facing checks, capacity predicates, and crash/distributed assumption eligibility where the theorem program supports them.
- [x] When a theorem-side predicate fails, return a structured witness or counterexample object rather than only a boolean or log line.
- [x] Preserve separation between runtime execution and offline decision procedures, but allow both to emit a shared witness/certificate format.
- [x] Add targeted tests for witness emission, counterexample minimization, and decision/execution result alignment.
- [x] Update docs to explain which checks are theorem-decision procedures and which are empirical simulator analyses.
- [x] Remove boolean-only or string-only legacy checker outputs where the new witness/certificate surface replaces them. No duplicate old/new result APIs.
- [x] Make a git commit for Phase 13.

## Phase 14: Budgeted Fault and Adversary Models

- [x] Refactor fault injection to support explicit budget declarations for crash, Byzantine-style interference, corruption, withholding, and timing disturbance models.
- [x] Keep low-level packet events, but classify failures at the assumption-bundle level: quorum/intersection failure, authentication/evidence failure, fairness failure, budget exhaustion, or unsupported regime.
- [x] Add support for correlated and windowed fault budgets in addition to per-message independent probabilities.
- [x] Ensure replay artifacts record the resolved budget schedule and budget-consumption history.
- [x] Add targeted tests for budget accounting, failure classification, and assumption-bundle diagnostics.
- [x] Update docs to describe budgeted adversary surfaces and their theorem-side meaning.
- [x] Remove any superseded low-level-only fault reporting paths once budget/accounting-aware surfaces exist, except where raw packet events remain intentionally foundational.
- [x] Make a git commit for Phase 14.

## Phase 15: Scheduler Semantics as a First-Class Surface

- [x] Extend execution configuration so scheduler policy is described in theorem-native terms in addition to implementation terms.
- [x] Report productive exactness, total-step conservative bounds, fairness requirements, and envelope/adherence status for each scheduler profile.
- [x] Add comparison tools for canonical, threaded, and alternative scheduler policies that distinguish semantic differences from performance-only differences.
- [x] Keep canonical replay as the authoritative lane while making scheduler-specific performance runs comparable through normalized metrics and theorem eligibility.
- [x] Add targeted tests for scheduler-profile reporting and cross-scheduler classification stability.
- [x] Update docs and examples to frame scheduler choice as both an execution policy and a theorem-profile choice.
- [x] Remove stale scheduler reporting/config surfaces that become redundant once first-class scheduler profiles exist. Do not keep old and new policy vocabularies in parallel.
- [x] Make a git commit for Phase 15.

## Phase 16: Approximation and Limit-Regime Ladders

- [x] Add an explicit approximation surface for comparing exact protocol-machine execution with batched stochastic, fluid, mean-field, or continuum-style regimes where Telltale has theorem support.
- [x] Make approximation runs declare their theorem-side scope and non-goals rather than presenting them as interchangeable with exact execution.
- [x] Add comparison reports that relate exact and approximate runs through shared observables, admissibility checks, and approximation metadata.
- [x] Keep approximation artifacts separate from authoritative replay artifacts while allowing them to cite the same scenario and profile manifest.
- [x] Add targeted tests for approximation-run determinism, manifest generation, and exact-vs-approximate comparison reporting.
- [x] Update docs to explain which approximation families are empirical only and which are tied to existing classical/mean-field theorem surfaces.
- [x] Remove or rename any legacy “simulation mode” surface that blurs exact execution and approximation once the explicit ladder exists. No backwards-compatibility aliases.
- [ ] Make a git commit for Phase 16.

## Phase 17: Proof-Carrying Batch and Sweep Artifacts

- [ ] Extend batch execution to support parameter sweeps over seeds, capacities, scheduler profiles, reconfiguration programs, and fault/adversary budgets.
- [ ] Emit one reproducible manifest per sweep containing resolved execution settings, theorem profiles, assumption bundles, witnesses/certificates, and authoritative result ordering.
- [ ] Preserve deterministic input-order results and deterministic artifact layout regardless of worker scheduling.
- [ ] Add diff/report tooling for comparing experiment families by theorem-native outcomes as well as raw metrics.
- [ ] Add targeted tests for manifest reproducibility, witness retention, and deterministic sweep ordering.
- [ ] Update docs and examples to present batch/sweep outputs as experiment artifacts rather than ad hoc logs.
- [ ] Remove any older ad hoc sweep-output or batch-report format that the new manifest supersedes. Do not keep parallel legacy artifact layouts.
- [ ] Make a git commit for Phase 17.

## Phase 18: External Domain-Model Integration Boundary

- [ ] Rename the simulator’s conceptual and public “material” layer to a broader field/environment-dynamics layer in architecture docs and public APIs.
- [ ] Remove the legacy `MaterialModel`/`MaterialParams` naming and API surface instead of retaining compatibility aliases or wrappers.
- [ ] Define the intended role of the field/environment-dynamics layer precisely: evolving shared fields, latent environment state, and node-local physical state, not owning the full medium/admission/topology decision stack by itself.
- [ ] Add a generic `TopologyModel` boundary that can answer potential communication reachability as a function of simulator time and environment state.
- [ ] Add a generic `MediumModel` boundary that can resolve delivery, delay, corruption, collision, and contention outcomes from concurrent transmissions and environment state.
- [ ] Add a generic `MobilityModel` boundary for deterministic position/orientation updates over simulator time.
- [ ] Add a generic `NodeCapabilityModel` boundary for per-node limits such as connection/admission slots, queue budgets, duty-cycle budgets, memory ceilings, or energy/state constraints.
- [ ] Add a generic `LinkAdmissionModel` boundary for deciding whether new or continuing communication relationships are admissible under topology and capability constraints.
- [ ] Define one canonical `EnvironmentSnapshot` surface that the simulator passes to these models each round so external integrations can compose them without private simulator coupling.
- [ ] Define one canonical `EnvironmentArtifact` or `EnvironmentTrace` surface for medium events, collisions, attenuation decisions, admission rejections, and capacity-limit diagnostics.
- [ ] Ensure the shared execution core can consume these boundaries without assuming any domain-specific naming, timing constants, protocol roles, or transport semantics.
- [ ] Keep the core scenario schema domain-neutral: do not add Bluetooth-, QUIC-, or any other vertical-specific fields to the base simulator config.
- [ ] Add extension-friendly config hooks so external projects can inject domain-owned environment models without patching `telltale-simulator` internals.
- [ ] Update simulator tests, docs, examples, and downstream-facing imports to the new field/environment-dynamics names in one breaking change.
- [ ] Document the breaking rename explicitly and state that downstream projects must migrate to the field/environment-dynamics surface.
- [ ] Decide whether generic geometry/radio helpers belong in a separate optional crate and keep that crate domain-neutral if added.
- [ ] Add targeted tests using a fake external environment model to prove that topology, medium, mobility, and node-capability hooks work without built-in domain knowledge.
- [ ] Add architecture checks or lint-style guidance that reject domain-branded simulator schema fields in core crates.
- [ ] Update simulator docs to describe the external-domain boundary, the field/environment-dynamics terminology shift, and explicitly state that vertical-specific logic belongs in downstream crates/projects.
- [ ] Remove the legacy material surface completely in this phase. Do not keep compatibility aliases, deprecated wrappers, dual terminology, or old config fields after the rename.
- [ ] Make a git commit for Phase 18.
