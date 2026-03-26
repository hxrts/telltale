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
| Lean core-library files | 647 | `lean/CODE_MAP.md` total row |
| Lean core-library lines | 131,670 | `lean/CODE_MAP.md` total row |
| Ownership contract gate commands | 6 | `just check-ownership-contracts` |
| Aura-derived boundary checks | 6 | `just check-aura-borrowed-lints` |
| Explicit failure/timeout observable event kinds | 5 | `rust/machine/src/engine/protocol_machine_config.rs` (`ObsEvent`) |
| Macro UI pass fixtures | 8 | `rust/macros/tests/macro_ui.rs` |
| Macro UI compile-fail fixtures | 8 | `rust/macros/tests/macro_ui.rs` |
| Property buckets with executable assurance suites | 11 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Property buckets currently lacking executable assurance suites | 0 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Authority and ownership semantic assurance suites | 2 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Identity and replay semantic assurance suites | 3 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Commitment and progress semantic assurance suites | 4 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Cross-mode semantic parity suites | 4 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Fail-closed lowering and admission gate suites | 4 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Structural locality and reconfiguration executable assurance suites | 1 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Semantic lifecycle invariant suites | 1 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Deterministic adversarial lifecycle scenarios | 10 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| End-to-end DSL runtime semantic conformance suites | 1 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Simulator semantic contract categories enforced automatically | 6 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Theorem-pack and admission executable assurance suites | 3 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Distributed and topology semantic harness suites | 3 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Agreement and composition runtime semantic suites | 4 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Extension and middleware semantic hardening suites | 2 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Generated topology and transport public-path suites | 1 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Explicit unsupported or fail-closed property notes | 3 | Curated unsupported-surface note list in `scripts/check/verification-inventory.sh` |

## Property Coverage Baseline

This baseline records whether each conserved-property bucket has at least one
high-signal executable assurance suite today.
It is intentionally curated.
The aim is to make gaps explicit rather than to produce vanity totals.

| Property bucket | Executable status | High-signal suites | Current note |
|---|---|---|---|
| Evidence | Spot checks | `rust/machine/tests/ownership_contracts.rs`, `rust/machine/tests/conformance_lean.rs` | Evidence-bearing paths are exercised, but not yet as a full semantic lifecycle harness |
| Authority | Cross-path checks | `rust/machine/tests/ownership_contracts.rs`, `rust/simulator/tests/ownership_faults.rs` | Strongest current area |
| Identity | Cross-path checks | `rust/machine/tests/serialization_replay.rs`, `rust/bridge/tests/semantic_object_roundtrip.rs`, `rust/bridge/tests/protocol_machine_cross_target_tests.rs` | Replay and semantic-object identity are checked across multiple surfaces |
| Commitment | Spot + path checks | `rust/machine/tests/unit/protocol_machine/tests_semantic_state.rs`, `rust/machine/tests/conformance_lean.rs`, `rust/machine/tests/threaded_equivalence.rs`, `rust/machine/src/runtime_contracts.rs` | Progress and terminalization are covered, but cross-object lifecycle assurance is still incomplete |
| Commitment | Deterministic lifecycle harness | `rust/machine/src/engine/runtime_exec/semantic_state.rs` | Seeded lifecycle and adversarial corpus now exercise terminalization, invalidation, proof-gaps, and progress escalation as one semantic state machine |
| Structure | Deterministic runtime structure suite | `rust/machine/src/engine/runtime_exec/semantic_state.rs` | Region locality, structural handoff transfer, and transformation obligations are now checked on executable runtime paths. Reconfiguration remains fail-closed elsewhere |
| Premise | Fail-closed + admission checks | `rust/machine/src/runtime_contracts.rs`, `rust/machine/src/composition.rs`, `rust/language/src/compiler/parser/mod.rs`, `rust/runtime/tests/authority_compile_fail.rs` | Assumption-heavy paths are rejected or gated, but not yet deeply scenario-tested |
| Premise | End-to-end supported/fail-closed lowering | `rust/tests/dsl_runtime_semantics_tests.rs` | Supported DSL forms now run through parser -> projection -> theory conversion -> protocol machine, while unsupported commitment lifecycle lowering fails closed |
| Admission | Theorem-pack and bundle assurance | `rust/bridge/tests/protocol_bundle_admission_contracts.rs`, `rust/bridge/tests/invariant_verification.rs`, `rust/tests/dsl_runtime_semantics_tests.rs` | Proof-bundle declarations, capability drops, and admission-gated runtime requests are now exercised end to end with stable diagnostics |
| Distributed topology | Deterministic harness | `rust/simulator/tests/distributed.rs`, `rust/machine/tests/topology_effect_ingress.rs`, `rust/runtime/tests/generated_topology_public_path.rs` | Distributed replay, ordered topology ingress, generated helpers, and invalid placement rejection now run through executable runtime paths without ambient network dependency |
| Agreement | Runtime commitment semantics | `rust/machine/src/effect/core_types.rs`, `rust/machine/src/semantic_objects.rs`, `rust/machine/tests/threaded_equivalence.rs`, `rust/tests/dsl_runtime_semantics_tests.rs` | Agreement profiles and child-effect rollups are checked as runtime semantics across scenario tables, lowering, and cross-driver parity |
| Extension boundary | Fail-closed + deterministic middleware stacks | `rust/runtime/tests/extension_integration.rs`, `rust/runtime/tests/middleware_semantic_hardening.rs` | Registered extension paths span parse -> codegen -> runtime, while retry, metrics, trace, and seeded fault injection remain explicit and deterministic |
| Generated deployment path | Public helper end-to-end execution | `rust/runtime/tests/generated_topology_public_path.rs` | `handler(...)`, `with_topology(...)`, and named inline topology helpers are exercised as public surfaces with transport intent checks and negative validation coverage |

## Explicit Unsupported / Fail-Closed Notes

These surfaces are intentionally not counted as executable support yet.
They remain visible here so the inventory does not overstate what the system
currently guarantees.

| Surface | Current status | Why it is not counted as executable support yet |
|---|---|---|
| Extension statement runtime dispatch | Fail-closed | Timeout-extension statement parsing is covered, but runtime statement dispatch remains intentionally unsupported and must reject clearly |
| Topology region constraints | Not yet executable | Placement validation now enforces colocated, separated, and pinned constraints, but region constraints still lack an executable runtime check and are therefore not counted |
| Remote transport realization | Intent checked only | Generated topology/transport public-path tests assert transport intent and deterministic routing through `TopologyHandler`, but real remote transport backends are still placeholder surfaces |

The inventory deliberately does not track raw unit-test totals, assertion
counts, or line counts for tests.
