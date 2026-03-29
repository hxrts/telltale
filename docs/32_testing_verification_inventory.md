# Verification Inventory

This page is the authoritative inventory for verification counts.
Only counts that are stable enough to check automatically are tracked here.

The goal is to track coverage of key system properties and regression gates,
not raw unit-test volume.

When one of these values changes legitimately:

1. update the underlying source of truth,
2. refresh this page,
3. rerun `just check-verification-inventory`.

The numeric rows in this section are source-derived and checked by
`scripts/check/verification-inventory.sh`.

| Metric | Value | Source |
|---|---:|---|
| Lean core-library files | 651 | `lean/CODE_MAP.md` total row |
| Lean core-library lines | 132,553 | `lean/CODE_MAP.md` total row |
| Ownership contract gate commands | 6 | `just check-ownership-contracts` |
| Aura-derived boundary checks | 6 | `just check-aura-borrowed-lints` |
| Explicit failure/timeout observable event kinds | 5 | `rust/machine/src/engine/protocol_machine_config.rs` (`ObsEvent`) |
| Macro UI pass fixtures | 9 | `rust/macros/tests/macro_ui.rs` |
| Macro UI compile-fail fixtures | 10 | `rust/macros/tests/macro_ui.rs` |
| Property buckets with executable assurance suites | 22 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Property buckets currently lacking executable assurance suites | 0 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Authority and ownership semantic assurance suites | 2 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Lean-backed correspondence strict suites | 6 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Identity and replay semantic assurance suites | 5 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Commitment and progress semantic assurance suites | 4 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Cross-mode semantic parity suites | 4 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Fail-closed lowering and admission gate suites | 5 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Structural locality and reconfiguration executable assurance suites | 5 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Semantic lifecycle invariant suites | 1 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Deterministic adversarial lifecycle scenarios | 10 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| End-to-end DSL runtime semantic conformance suites | 1 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Simulator semantic contract categories enforced automatically | 6 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Theorem-pack and admission executable assurance suites | 4 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Distributed and topology semantic harness suites | 3 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Agreement and composition runtime semantic suites | 4 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Extension and middleware semantic hardening suites | 2 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Generated topology and transport public-path suites | 1 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Runtime substrate boundary assurance suites | 2 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Handler contract boundary assurance suites | 1 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Long-horizon recovery differential harness suites | 1 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Artifact and release assurance suites | 3 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Mutation fail-closed assurance suites | 2 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Concrete protocol-machine refinement suites | 3 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Compiler and serialization pipeline suites | 5 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Deadlock automation fragment assurance suites | 3 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Docs-as-contract assurance suites | 3 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Deterministic scale and budget assurance suites | 1 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Explicit unsupported or fail-closed property notes | 0 | Curated unsupported-surface note list in `scripts/check/verification-inventory.sh` |

## Current Formal Verification Claim

Telltale does not currently make the blanket public claim that "Telltale is
formally verified" end to end.

The current public claim is:

> Telltale has formally verified Lean models and theorems for its session-type,
> projection, protocol-machine, and conservation-property semantics; strict
> deterministic Rust↔Lean correspondence for the declared supported corpora; and
> operational verification for the shipped first-party Rust artifacts and
> release surface.

That claim is intentionally narrower than "the shipped Rust implementation is
mechanically proved correct end to end." The remaining gap is tracked in
`work/verification.md`.

## Claimed Surface

The current proved or proof-backed claimed surface is:

- the Lean `SessionTypes`, `SessionCoTypes`, `Choreography`, `Protocol`, and
  `Runtime` models and theorem libraries
- the supported DSL subset explicitly described in the property coverage table
  for parser -> projection -> theory-conversion -> protocol-machine lowering
- the strict Rust↔Lean correspondence corpora and comparison contracts tracked
  in the Lean correspondence rows below
- the packaged first-party crates and binaries only at the level of
  operationally checked artifact/release assurance, not full mechanized proof

## Out of Scope / Assumption Boundaries

The current public claim does not include:

- user-supplied handlers, transports, plugins, or deployment adapters
- third-party infrastructure or deployment environments
- Cargo, crates.io, git hosting, OS, compiler, and toolchain correctness beyond
  the documented operational checks
- cryptographic hardness assumptions beyond standard SHA-256-style assumptions
- a blanket claim that every shipped Rust code path is mechanically proved

## Public TCB Ledger

The current trusted computing base for the public claim is:

| Component | Why it remains trusted | Current enforcement |
|---|---|---|
| Lean kernel and imported proof libraries | theorem checker and proof environment | Lean build + code map + proof targets |
| Lean model definitions | theorems are only as correct as the modeled semantics | Lean proof suites and docs inventory |
| Rust/Lean bridge normalization and interchange | comparison/equality surface between Rust and Lean | `just check-bridge-normalization`, strict correspondence suites |
| Rust runtime implementation | shipped executable semantics are still comparison-checked, not fully proved | strict correspondence, semantic assurance, refinement slice |
| First-party handlers/transports | external impurity boundary for the runtime | handler-contract and runtime-boundary suites |
| Release/package scripts and generated resources | artifact identity path from workspace to published crates | package-artifact, release-recovery, and docs-as-contract gates |
| Cargo / crates.io / git / toolchains | external delivery/build platform | operational checks only |

If that TCB shrinks or the claim broadens, this section must be updated before a
broader public wording is used.

## Refinement Coverage Map

This map names the current protocol-machine state surfaces that matter to the
claimed runtime story and shows whether they are already inside the exact
Rust↔Lean refinement slice.

| Runtime state component | Rust surface | Lean surface | Current refinement status | Note |
|---|---|---|---|---|
| Coroutine identity, program counter, status, owned-endpoint count, progress-token count | `rust/machine/src/refinement.rs` (`CoroutineRefinementSlice`) | `lean/Runtime/Proofs/ProtocolMachine/ConcreteRefinement.lean` (`ConcreteCoroutineSlice`) | exact slice | Compared exactly across cooperative, Lean, and threaded executions today |
| Session id, role count, local-type entry count, buffered-message count, epoch | `rust/machine/src/refinement.rs` (`SessionRefinementSlice`) | `lean/Runtime/Proofs/ProtocolMachine/ConcreteRefinement.lean` (`ConcreteSessionSlice`) | exact slice | This is the current session-level refinement surface |
| Scheduler ready queue, blocked-set tags, step count | `rust/machine/src/refinement.rs` (`SchedulerRefinementSlice`) | `lean/Runtime/Proofs/ProtocolMachine/ConcreteRefinement.lean` (`ConcreteSchedulerSlice`) | exact slice | The canonical scheduler slice is compared exactly today |
| Per-step event stream, `session_type_counts`, `ready_queue`, and `blocked` snapshots | `rust/bridge/src/protocol_machine_runner.rs` (`ProtocolMachineStepState`) | `lean/Runtime/Tests/ProtocolMachineRunner.lean` step-state JSON export | strict correspondence, not yet part of the proved refinement slice | Deterministic parity exists, but this surface is still compared through the bridge runner rather than covered by the current Lean refinement theorem |
| Effect exchanges and output-condition trace | `rust/bridge/src/protocol_machine_runner.rs` (`effect_exchanges`, `output_condition_trace`) | Lean runner JSON export and strict bridge suites | strict correspondence, not yet part of the proved refinement slice | Compared in strict lanes, not yet in the concrete refinement theorem |
| Semantic-object families (handoffs, progress contracts, publications, agreement state, transformation obligations) | `rust/machine/src/engine/runtime_exec/introspection.rs`, `rust/machine/src/threaded/runtime_introspection.rs` | `lean/Runtime/Proofs/ProtocolMachine/SemanticObjects/*` | theorem-backed separately, not yet folded into one full refinement slice | Conservation theorems and strict comparison exist, but Phase 20 is the work to unify them into a single end-to-end runtime refinement claim |

## Gate Ownership

The verification surface is organized around three canonical just-entry lanes.
`just ci-dry-run`, `check.yml`, and `verify.yml` should call these names rather
than duplicating their inner gate lists by hand.

| Gate | Canonical entry point | Primary owning files | Local run surface | GitHub run surface |
|---|---|---|---|---|
| Fast structural verification | `just check-fast-structure` | `justfile`, `scripts/check/ci-assurance-lanes.sh`, `scripts/check/formal-claim-scope.sh`, `scripts/check/verification-inventory.sh`, `scripts/check/bridge-normalization-ledger.sh`, `scripts/check/fail-closed-mutations.sh`, `scripts/check/source-doc-snippets.sh`, `scripts/check/tooling-convergence.sh`, Lean bootstrap scripts | `just check-pr-critical`, `just ci-dry-run`, direct local recipe use | `check.yml`, `verify.yml` |
| Focused assurance | `just check-focused-assurance` | `justfile`, strict Lean bridge suites, compiler pipeline suites, metatheory/refinement/runtime boundary suites | `just check-pr-critical`, `just ci-dry-run`, direct local recipe use | `check.yml`, `verify.yml` |
| Packaged artifact assurance | `just check-package-artifacts` | `justfile`, `scripts/check/package-artifacts.sh`, `scripts/check/package-resource-audit.sh`, `scripts/check/release-recovery.sh` | `just check-pr-critical`, `just ci-dry-run`, direct local recipe use | `check.yml`, `verify.yml` |
| PR-critical assurance | `just check-pr-critical` | `justfile`, `.github/workflows/check.yml`, `.github/workflows/verify.yml` | `just ci-dry-run`, direct local recipe use | `check.yml`, `verify.yml` |
| Scheduled deep assurance | `just check-deep-assurance` | `justfile`, `.github/workflows/verify.yml`, scale-budget and larger-corpus verification lanes | `just ci-dry-run full`, direct local recipe use | `verify.yml` |

## Property Coverage Baseline

This baseline records whether each conserved-property bucket has at least one
high-signal executable assurance suite today.
It is intentionally curated.
The aim is to make gaps explicit rather than to produce vanity totals.

| Property bucket | Executable status | High-signal suites | Current note |
|---|---|---|---|
| Evidence | Spot checks | `rust/machine/tests/ownership_contracts.rs`, `rust/machine/tests/conformance_lean.rs` | Evidence-bearing paths are exercised directly in runtime and Lean-backed spot checks; the current theorem-focused authority slice starts from authoritative reads plus canonical publication/materialization rather than the whole authority lifecycle family |
| Authority | Cross-path checks | `rust/machine/tests/ownership_contracts.rs`, `rust/simulator/tests/ownership_faults.rs` | The supported authority theorem slice is now explicit: evidence-bearing reads and canonical publication/materialization are justified at the semantic-object layer, while broader lifecycle surfaces still rely on the wider protocol-machine conservation theorems |
| Lean correspondence | Strict executable validation checks | `rust/bridge/tests/lean_trace_validation.rs`, `rust/bridge/tests/property_tests.rs`, `rust/bridge/tests/protocol_bundle_admission_contracts.rs`, `rust/bridge/tests/protocol_machine_correspondence_tests.rs`, `rust/bridge/tests/protocol_machine_differential_steps.rs`, `rust/simulator/tests/lean_reference_parity.rs` | `validateTrace`, `validateSimulationTrace`, `runSimulation`, `verifyProtocolBundle`, deterministic reconfiguration-transition validation, epoch-aware multi-step reconfiguration phase validation, exact normalized simulator-trace parity, full protocol-machine event-stream parity, session-status parity, and step-indexed scheduler-state parity now execute in strict deterministic lanes for the supported corpus |
| Identity | Cross-path checks | `rust/machine/tests/serialization_replay.rs`, `rust/machine/tests/replay_persistence_identity.rs`, `rust/bridge/tests/semantic_object_roundtrip.rs`, `rust/bridge/tests/protocol_machine_cross_target_tests.rs`, `rust/bridge/tests/reconfiguration_recovery_harness.rs` | Replay, snapshot/restore, canonical fragment roundtrip, semantic-object identity, ownership-transfer replay artifacts, and bridge-exported reconfiguration snapshot identity are now checked as one differential family across multiple surfaces |
| Commitment | Spot + path checks | `rust/machine/tests/unit/protocol_machine/tests_semantic_state.rs`, `rust/machine/tests/conformance_lean.rs`, `rust/machine/tests/threaded_equivalence.rs`, `rust/machine/src/runtime_contracts.rs` | Progress and terminalization are covered across runtime contracts, lifecycle harnesses, and cross-driver parity |
| Commitment | Deterministic lifecycle harness | `rust/machine/src/engine/runtime_exec/semantic_state.rs` | Seeded lifecycle and adversarial corpus now exercise terminalization, invalidation, proof-gaps, and progress escalation as one semantic state machine |
| Structure | Deterministic runtime structure suite | `rust/machine/src/engine/runtime_exec/semantic_state.rs`, `rust/machine/tests/ownership_contracts.rs`, `rust/machine/src/composition.rs`, `rust/bridge/tests/protocol_bundle_admission_contracts.rs`, `rust/runtime/tests/generated_topology_public_path.rs` | Structural handoff locality, transformation obligations, pre-transfer witness invalidation, generated topology validation, executable region inheritance/conflict checks, bridge-to-runtime reconfiguration admission, atomic multi-step plan execution, canonical placement/transport-boundary phase artifacts, deterministic reconfiguration history, snapshot/restore state, and Lean-validated transition artifacts are now exercised on executable runtime paths |
| Premise | Fail-closed + admission checks | `rust/machine/src/runtime_contracts.rs`, `rust/machine/src/composition.rs`, `rust/language/src/compiler/parser/mod.rs`, `rust/runtime/tests/authority_compile_fail.rs`, `rust/runtime/tests/authority_control_flow_corpus.rs` | Assumption-heavy paths are rejected or gated, and the authority/control-flow boundary is now exercised with deterministic accepted/rejected `.tell` and `tell!` fixtures |
| Premise | End-to-end supported/fail-closed lowering | `rust/tests/dsl_runtime_semantics_tests.rs` | The theory-backed supported subset is explicit and executable: `choice`, `call`, counted `loop`, and recursion remain parser -> projection -> theory-conversion -> protocol-machine clean. `par`, `case/of`, and `timeout` stay outside that theory-convertible subset and are covered through the executable/runtime and boundary suites above |
| Admission | Theorem-pack and bundle assurance | `rust/bridge/tests/protocol_bundle_admission_contracts.rs`, `rust/bridge/tests/invariant_verification.rs`, `rust/machine/src/runtime_contracts.rs`, `rust/tests/dsl_runtime_semantics_tests.rs` | Proof-bundle declarations, capability drops, admission-gated runtime requests, and the explicit transported-theorem boundary ledger are now exercised end to end with stable diagnostics; runtime-critical instantiated premises are separated from Lean-only assumption boundaries and black-box/background theorem inventory |
| Distributed topology | Deterministic harness | `rust/simulator/tests/distributed.rs`, `rust/machine/tests/topology_effect_ingress.rs`, `rust/runtime/tests/generated_topology_public_path.rs` | Distributed replay, ordered topology ingress, generated helpers, and invalid placement rejection now run through executable runtime paths without ambient network dependency |
| Agreement | Runtime commitment semantics | `rust/machine/src/effect/core_types.rs`, `rust/machine/src/semantic_objects.rs`, `rust/machine/tests/threaded_equivalence.rs`, `rust/tests/dsl_runtime_semantics_tests.rs` | Agreement profiles and child-effect rollups are checked as runtime semantics across scenario tables, lowering, and cross-driver parity |
| Extension boundary | Deterministic parse-to-runtime dispatch + middleware stacks | `rust/runtime/tests/extension_integration.rs`, `rust/runtime/tests/middleware_semantic_hardening.rs` | Registered statement rules now parse into `Protocol::Extension`, lower into runtime extension effects, execute through deterministic extensible handlers, fail with stable diagnostics when handlers are missing or payloads are malformed, and remain middleware-safe under retry, metrics, trace, and seeded fault injection |
| Generated deployment path | Public helper end-to-end execution | `rust/runtime/tests/generated_topology_public_path.rs` | `handler(...)`, `with_topology(...)`, and named inline topology helpers are exercised as public surfaces with real loopback remote transport, negative validation coverage, executable region semantics, preservation of inline role-family constraints, and a transport-agnostic runtime topology API |
| Runtime substrate | Target-aware wrapper contracts | `rust/runtime/tests/runtime_substrate_contracts.rs`, `rust/runtime/tests/wasm_compat.rs` | Native and WASM wrapper seams now have direct regression coverage for `spawn`, `spawn_local`, and deterministic clock/RNG discipline, and deterministic assurance suites are guarded against accidental `SystemClock` / `SystemRng` drift |
| Handler contract boundary | Machine-checkable contract profiles for core handlers and fail-closed extension dispatch | `rust/runtime/tests/handler_contracts.rs` | `ChoreoHandler` now has an explicit machine-checkable contract ledger that separates protocol-semantic obligations from transport policy choices, validates production and harness handler profiles mechanically, and proves deterministic registered-only extension dispatch plus fail-closed unregistered behavior through runtime tests |
| Recovery | Long-horizon differential harness | `rust/bridge/tests/reconfiguration_recovery_harness.rs` | Ownership-transfer replay artifacts, bridge export/import, topology-derived placement artifacts, atomic multi-step reconfiguration plans, snapshot/restore recovery, and deterministic suffix replay now execute as one end-to-end recovery family with explicit divergence detection |
| Artifact / release | Packaged-crate and resume verification | `scripts/check/package-artifacts.sh`, `scripts/check/package-resource-audit.sh`, `scripts/check/release-recovery.sh` | Every publishable crate now goes through the `cargo publish --dry-run --locked --no-verify` packaging path, package-manifest resource paths are checked before packaging, the full packaged crate set is compiled from extracted tarballs, external consumer canaries for `telltale`, `telltale-runtime`, and `telltale-bridge` run outside the workspace layout with exact last-line stdout assertions, package-root resource escapes are fail-closed, the packaged WASM and embedded-grammar surfaces are verified explicitly, and release resume behavior is exercised under a deterministic fake cargo/git harness |
| Mutation pressure | Direct fail-closed perturbation suites | `rust/machine/src/runtime_contracts.rs`, `scripts/check/fail-closed-mutations.sh` | Representative bridge payload, theorem-boundary, source-derived docs-row, package-registry, package-manifest, package-resource, and inventory mutations are injected directly against the narrow owning gates so drift is rejected before broader integration lanes run |
| Concrete refinement | Exact cooperative/Lean/threaded state-slice parity plus Lean proof-connected slice | `rust/bridge/tests/protocol_machine_differential_steps.rs`, `rust/machine/tests/lean_protocol_machine_equivalence.rs`, `rust/machine/tests/threaded_equivalence.rs` | The first concrete protocol-machine refinement slice now compares coroutine/session/scheduler state exactly across Rust, Lean, and canonical threaded execution, exports bounded `u64` bridge fields fail-closed, and is connected to dedicated Lean refinement theorems over the same slice |
| Compiler / serialization pipeline | Strict DSL-to-theory lowering, exact-shape JSON bridge, and Lean-backed projection acceptance | `rust/bridge/tests/compiler_pipeline_conformance.rs`, `rust/bridge/tests/projection_equivalence.rs`, `rust/bridge/tests/proptest_json_roundtrip.rs`, `rust/bridge/tests/lean_integration_tests.rs`, `rust/bridge/tests/merge_semantics_tests.rs` | The supported DSL subset now runs through parser -> `protocol_to_global()` / `local_to_local_r()` -> exact-shape import/export -> Lean projection export and validator acceptance in deterministic strict lanes; bridge import rejects unknown fields fail-closed so schema drift cannot hide behind permissive parsing |
| Deadlock automation | Lean-sound regular-fragment checker mirrored into Rust diagnostics | `rust/types/src/local.rs`, `rust/bridge/tests/regular_practical_fragment_checks.rs`, `rust/tests/dsl_runtime_semantics_tests.rs` | The automatic deadlock-discharge fragment is now mechanically characterized as closed + contractive projected locals whose full unfold exposes send/recv, checked first in Lean on `SessionTypes.LocalTypeR`, mirrored in Rust only for macro/proof-status diagnostics, and exercised end to end through bridge parity and generated `proof_status` surfaces |
| Public docs as contract | Source-derived capability/admission, authority-support, and trust-surface tables | `rust/tests/docs_contract_tests.rs`, `scripts/check/verification-inventory.sh`, `scripts/check/bridge-normalization-ledger.sh` | The highest-value public verification/capability docs now separate source-derived tables from explanatory prose, and those rows are checked mechanically against runtime-contract, DSL-tier, and bridge-ledger facts |
| Deterministic scale budgets | Larger supported corpora with structural size envelopes | `rust/bridge/tests/scale_budget_contracts.rs` | Larger lowering/projection corpora, longer record/replay histories, larger reconfiguration snapshots, and larger Lean bridge payloads now run as deterministic structural-budget gates with exact replay/snapshot equality and explicit serialized-size envelopes rather than ambient wall-clock benchmarks |

## Bridge Normalization Trust Surface

The Lean bridge still contains a small amount of trusted normalization logic.
That logic is intentionally narrow and is audited explicitly in CI by
`just check-bridge-normalization`.
The rows in this table are source-derived and checked by
`telltale_bridge::bridge_normalization_ledger()` via
`scripts/check/bridge-normalization-ledger.sh`.

| Surface | Normalization rule | Classification | Why permitted | Enforcing artifacts |
|---|---|---|---|---|
| semantic-audit tick normalization | Normalize only `tick`, and only per extracted session id | irreducible trusted comparison logic | Absolute cross-session scheduling order is not semantic protocol truth; per-session observable order is | `rust/bridge/src/protocol_machine_trace.rs`, `rust/bridge/tests/protocol_machine_correspondence_tests.rs`, `rust/bridge/tests/protocol_machine_differential_steps.rs` |
| runner JSON schema backfill | Inject missing `schema_version` fields only at the root, nested trace/session/step-event nodes, and semantic-object export | compatibility-only, removable by schema tightening | Older runner payloads may omit nested schema tags; the bridge must not synthesize semantic fields | `rust/bridge/src/protocol_machine_runner_json_parsing.rs`, `scripts/check/bridge-normalization-ledger.sh` |

Session-status ordering is no longer part of the trusted comparison surface.
Both the Lean runner and Rust-side correspondence harness now emit session rows
in canonical `sid` order, so comparison is exact rather than normalized.

## Explicit Unsupported / Fail-Closed Notes

No explicit unsupported or fail-closed implementation-gap notes remain in the
tracked inventory. New notes should be added here only for intentional,
documented non-goals or for temporary regressions that are not yet executable.

The inventory deliberately does not track raw unit-test totals, assertion
counts, or line counts for tests.
