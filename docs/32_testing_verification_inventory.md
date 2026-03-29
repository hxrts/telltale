# Verification Inventory

This page is the authoritative inventory for verification counts.
Only counts that are stable enough to check automatically are tracked here.

The goal is to track coverage of key system properties and regression gates,
not raw unit-test volume.

When one of these values changes legitimately:

1. update the underlying source of truth,
2. refresh this page,
3. rerun `just check-verification-inventory`.

| Metric | Value | Source |
|---|---:|---|
| Lean core-library files | 650 | `lean/CODE_MAP.md` total row |
| Lean core-library lines | 132,260 | `lean/CODE_MAP.md` total row |
| Ownership contract gate commands | 6 | `just check-ownership-contracts` |
| Aura-derived boundary checks | 6 | `just check-aura-borrowed-lints` |
| Explicit failure/timeout observable event kinds | 5 | `rust/machine/src/engine/protocol_machine_config.rs` (`ObsEvent`) |
| Macro UI pass fixtures | 9 | `rust/macros/tests/macro_ui.rs` |
| Macro UI compile-fail fixtures | 10 | `rust/macros/tests/macro_ui.rs` |
| Property buckets with executable assurance suites | 19 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
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
| Theorem-pack and admission executable assurance suites | 3 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Distributed and topology semantic harness suites | 3 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Agreement and composition runtime semantic suites | 4 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Extension and middleware semantic hardening suites | 2 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Generated topology and transport public-path suites | 1 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Runtime substrate boundary assurance suites | 2 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Handler contract boundary assurance suites | 1 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Long-horizon recovery differential harness suites | 1 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Artifact and release assurance suites | 3 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Concrete protocol-machine refinement suites | 3 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Compiler and serialization pipeline suites | 5 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Deadlock automation fragment assurance suites | 3 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Explicit unsupported or fail-closed property notes | 0 | Curated unsupported-surface note list in `scripts/check/verification-inventory.sh` |

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
| Admission | Theorem-pack and bundle assurance | `rust/bridge/tests/protocol_bundle_admission_contracts.rs`, `rust/bridge/tests/invariant_verification.rs`, `rust/tests/dsl_runtime_semantics_tests.rs` | Proof-bundle declarations, capability drops, and admission-gated runtime requests are now exercised end to end with stable diagnostics |
| Distributed topology | Deterministic harness | `rust/simulator/tests/distributed.rs`, `rust/machine/tests/topology_effect_ingress.rs`, `rust/runtime/tests/generated_topology_public_path.rs` | Distributed replay, ordered topology ingress, generated helpers, and invalid placement rejection now run through executable runtime paths without ambient network dependency |
| Agreement | Runtime commitment semantics | `rust/machine/src/effect/core_types.rs`, `rust/machine/src/semantic_objects.rs`, `rust/machine/tests/threaded_equivalence.rs`, `rust/tests/dsl_runtime_semantics_tests.rs` | Agreement profiles and child-effect rollups are checked as runtime semantics across scenario tables, lowering, and cross-driver parity |
| Extension boundary | Deterministic parse-to-runtime dispatch + middleware stacks | `rust/runtime/tests/extension_integration.rs`, `rust/runtime/tests/middleware_semantic_hardening.rs` | Registered statement rules now parse into `Protocol::Extension`, lower into runtime extension effects, execute through deterministic extensible handlers, fail with stable diagnostics when handlers are missing or payloads are malformed, and remain middleware-safe under retry, metrics, trace, and seeded fault injection |
| Generated deployment path | Public helper end-to-end execution | `rust/runtime/tests/generated_topology_public_path.rs` | `handler(...)`, `with_topology(...)`, and named inline topology helpers are exercised as public surfaces with real loopback remote transport, negative validation coverage, executable region semantics, preservation of inline role-family constraints, and a transport-agnostic runtime topology API |
| Runtime substrate | Target-aware wrapper contracts | `rust/runtime/tests/runtime_substrate_contracts.rs`, `rust/runtime/tests/wasm_compat.rs` | Native and WASM wrapper seams now have direct regression coverage for `spawn`, `spawn_local`, and deterministic clock/RNG discipline, and deterministic assurance suites are guarded against accidental `SystemClock` / `SystemRng` drift |
| Handler contract boundary | Machine-checkable contract profiles for core handlers and fail-closed extension dispatch | `rust/runtime/tests/handler_contracts.rs` | `ChoreoHandler` now has an explicit machine-checkable contract ledger that separates protocol-semantic obligations from transport policy choices, validates production and harness handler profiles mechanically, and proves deterministic registered-only extension dispatch plus fail-closed unregistered behavior through runtime tests |
| Recovery | Long-horizon differential harness | `rust/bridge/tests/reconfiguration_recovery_harness.rs` | Ownership-transfer replay artifacts, bridge export/import, topology-derived placement artifacts, atomic multi-step reconfiguration plans, snapshot/restore recovery, and deterministic suffix replay now execute as one end-to-end recovery family with explicit divergence detection |
| Artifact / release | Packaged-crate and resume verification | `scripts/check/package-artifacts.sh`, `scripts/check/package-resource-audit.sh`, `scripts/check/release-recovery.sh` | Every publishable crate now goes through `cargo publish --dry-run --locked`, packaged tarballs for `telltale`, `telltale-runtime`, and `telltale-bridge` are smoke-checked from extraction roots, package-root resource escapes are fail-closed, the packaged WASM and embedded-grammar surfaces are verified explicitly, and release resume behavior is exercised under a deterministic fake cargo/git harness |
| Concrete refinement | Exact cooperative/Lean/threaded state-slice parity plus Lean proof-connected slice | `rust/bridge/tests/protocol_machine_differential_steps.rs`, `rust/machine/tests/lean_protocol_machine_equivalence.rs`, `rust/machine/tests/threaded_equivalence.rs` | The first concrete protocol-machine refinement slice now compares coroutine/session/scheduler state exactly across Rust, Lean, and canonical threaded execution, exports bounded `u64` bridge fields fail-closed, and is connected to dedicated Lean refinement theorems over the same slice |
| Compiler / serialization pipeline | Strict DSL-to-theory lowering, exact-shape JSON bridge, and Lean-backed projection acceptance | `rust/bridge/tests/compiler_pipeline_conformance.rs`, `rust/bridge/tests/projection_equivalence.rs`, `rust/bridge/tests/proptest_json_roundtrip.rs`, `rust/bridge/tests/lean_integration_tests.rs`, `rust/bridge/tests/merge_semantics_tests.rs` | The supported DSL subset now runs through parser -> `protocol_to_global()` / `local_to_local_r()` -> exact-shape import/export -> Lean projection export and validator acceptance in deterministic strict lanes; bridge import rejects unknown fields fail-closed so schema drift cannot hide behind permissive parsing |
| Deadlock automation | Lean-sound regular-fragment checker mirrored into Rust diagnostics | `rust/types/src/local.rs`, `rust/bridge/tests/regular_practical_fragment_checks.rs`, `rust/tests/dsl_runtime_semantics_tests.rs` | The automatic deadlock-discharge fragment is now mechanically characterized as closed + contractive projected locals whose full unfold exposes send/recv, checked first in Lean on `SessionTypes.LocalTypeR`, mirrored in Rust only for macro/proof-status diagnostics, and exercised end to end through bridge parity and generated `proof_status` surfaces |

## Bridge Normalization Trust Surface

The Lean bridge still contains a small amount of trusted normalization logic.
That logic is intentionally narrow and is audited explicitly in CI by
`just check-bridge-normalization`.

| Surface | Normalization rule | Why permitted | Enforcing artifacts |
|---|---|---|---|
| semantic-audit tick normalization | Normalize only `tick`, and only per extracted session id | Absolute cross-session scheduling order is not semantic protocol truth; per-session observable order is | `rust/bridge/src/protocol_machine_trace.rs`, `rust/bridge/tests/protocol_machine_correspondence_tests.rs`, `rust/bridge/tests/protocol_machine_differential_steps.rs` |
| session-status ordering | Sort session-status rows by `sid` before comparison | Output list order is not semantic; `sid` and `terminal` remain exact comparison fields | `rust/bridge/src/protocol_machine_runner.rs` |
| runner JSON schema backfill | Inject missing `schema_version` fields only at the root, nested trace/session/step-event nodes, and semantic-object export | Older runner payloads may omit nested schema tags; the bridge must not synthesize semantic fields | `rust/bridge/src/protocol_machine_runner_json_parsing.rs`, `scripts/check/bridge-normalization-ledger.sh` |

## Explicit Unsupported / Fail-Closed Notes

No explicit unsupported or fail-closed implementation-gap notes remain in the
tracked inventory. New notes should be added here only for intentional,
documented non-goals or for temporary regressions that are not yet executable.

The inventory deliberately does not track raw unit-test totals, assertion
counts, or line counts for tests.
