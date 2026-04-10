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
| Lean core-library files | 669 | `lean/CODE_MAP.md` total row |
| Lean core-library lines | 136,402 | `lean/CODE_MAP.md` total row |
| Lean-backed search fairness inventory entries | 37 | `lean/Runtime/Proofs/Search/Inventory.lean` |
| Ownership contract gate commands | 6 | `just check-ownership-contracts` |
| Aura-derived boundary checks | 9 | `just check-aura-borrowed-lints` |
| Explicit failure/timeout observable event kinds | 5 | `rust/machine/src/engine/protocol_machine_config.rs` (`ObsEvent`) |
| Macro UI pass fixtures | 10 | `rust/macros/tests/macro_ui.rs` |
| Macro UI compile-fail fixtures | 13 | `rust/macros/tests/macro_ui.rs` |
| Property buckets with executable assurance suites | 22 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Property buckets currently lacking executable assurance suites | 0 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Authority and ownership semantic assurance suites | 2 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Lean-backed correspondence strict suites | 8 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
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
| Handler contract boundary assurance suites | 2 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Long-horizon recovery differential harness suites | 1 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Artifact and release assurance suites | 4 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Mutation fail-closed assurance suites | 2 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Concrete protocol-machine refinement suites | 3 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Compiler and serialization pipeline suites | 5 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Deadlock automation fragment assurance suites | 3 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Docs-as-contract assurance suites | 3 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Deterministic scale and budget assurance suites | 1 | Curated property-suite map in `scripts/check/verification-inventory.sh` |
| Explicit unsupported or fail-closed property notes | 1 | Curated unsupported-surface note list in `scripts/check/verification-inventory.sh` |

## Current Formal Verification Claim

Telltale is formally verified for the declared shipped surface documented in
this inventory, under the assumptions listed in the public TCB ledger below.

The exact public claim is:

> Telltale is formally verified for its declared shipped surface: the Lean
> session-type, projection, protocol-machine, and conservation-property models
> and theorems, the theorem-defined Rust↔Lean protocol-machine runtime
> correspondence core for the audited supported corpus, the shipped first-party
> handler/transport boundary as documented by machine-checkable contract
> profiles, and the shipped first-party crate artifacts through the audited
> artifact-correspondence pipeline.

This does not mean every Rust API, compiler helper, macro path, plugin, or
third-party integration is mechanically proved. Anything outside the declared
shipped surface is listed explicitly below and is not part of the formal claim.

The runtime heap now has a focused Lean parity lane for canonical bytes,
tagged preimages, ordering, proof-path structure, and deterministic replay.
Its digest algorithm remains an operational conformance surface checked through
published vectors and runtime tests rather than a first-class Lean hash model.

The simulator assurance story now includes explicit exact-backend parity,
canonical replay reproduction, exact checkpoint resume, durable WAL fault
injection and crash/recovery matrices, batch-order reproducibility, fail-closed
theorem-classification matrices, approximation admissibility gates, nested
distributed invariance, and helper-surface non-authoritativeness checks. These
remain executable assurance lanes rather than part of the current mechanized
formal claim.

The search crate now has a scoped Lean fairness lane as well. The current
proved search fairness surface is:

- canonical serial search is exact one-step fair for the current legal min-key
  batch
- canonical serial search now has an executable reduced machine semantics plus
  an explicit reduced Rust-facing state/artifact projection boundary
- canonical serial search now also has a reduced machine-level invariant and
  projection layer, including executable machine-step invariant preservation,
  executable trace refinement into the packaged machine theorem surface, and a
  machine-trace restatement of current min-key eventual service
- canonical serial search also has a dynamic liveness theorem under an explicit
  stability premise: if an entry remains continuously eligible and no strictly
  better entry appears, it is eventually serviced
- canonical serial search has a fixed-phase termination theorem under an
  explicit finite reachable-node premise bundle
- canonical serial search also has a rebuild-aware ARA-style termination
  theorem under an explicit lexicographic phase/work measure premise bundle
- canonical serial search has both bounded strict-preemption and finite
  better-entry exhaustion theorems for entries that are not initially in the
  current min-key batch
- canonical serial search has both frontier-level and machine-level
  witness-path goal-reachability theorems for the reduced model
- canonical serial search now also has a graph-reachability-driven
  completeness theorem under explicit reachable-path, finiteness, and
  heuristic premises
- canonical serial search also has an explicit machine-level bridge from goal
  reachability to incumbent publication under a publication premise bundle
- canonical serial search now also has an eventual optimal-goal publication
  theorem under explicit admissibility and consistency premises
- threaded exact single-lane search has the same exact one-step fairness
  through reduced one-step, commit-trace, state-slice, and observation-slice
  refinement theorems to canonical serial search
- batched exact search has a certified-window fairness theorem with explicit
  premises plus a bounded dynamic starvation-freedom theorem under an explicit
  bounded-preemption premise, and its theorem-pack/export surface now also
  carries explicit support-class metadata alongside the certified multi-step
  window-trace validity theorem
- envelope-bounded batched search still remains outside the unconditional proved
  fairness surface, but that boundary is now made explicit by a checked-in Lean
  design-boundary theorem, an empty theorem-backed observable surface, and a
  premise-scoped theorem-pack classification rather than left as an
  undocumented omission

These search fairness claims are exposed operationally through the
`SearchFairnessArtifact` and `SearchFairnessCertificate` runtime surfaces and
checked by the dedicated `just check-search-fairness` gate, the Rust↔Lean
search parity suite, and the verification-inventory gate. The current theorem
pack is a first-class Lean artifact under
`Runtime.Proofs.Search.TheoremPack`, with a mirrored Rust
`SearchTheoremPackArtifact` for release-facing inventory export, now including
per-theorem support classes that distinguish executable-semantics theorems,
refinement corollaries, and premise-scoped theorems. Exact runtime runs now
also export `SearchStateArtifact` plus per-round state/certificate traces.
They also export `SearchRouteBoundArtifact`, whose current discovery surface
is an observed run-scoped bound to first candidate publication, an observed
recovery bound after the latest epoch transition, and a theorem-backed
one-step goal-window service bound from the fairness certificate surface, now
packaged as a structured `SearchRouteDiscoveryCertificate` and attached to the
exact observed goal-window and publication steps for that run. The selected-route
summary also carries a stable generic metric list alongside its scalar
convenience fields. Its current quality surface remains profile-scoped rather
than a separate Lean end-to-end discovery theorem. The release/provenance lane records the generated
`target/search-theorem-pack/search-theorem-pack.json` artifact plus the
generated canonical vector artifact
`target/search-artifacts/search-vectors-v1.json` and the generated recovery
vector artifact `target/search-artifacts/search-recovery-vectors-v1.json`.
These claims are also backed by source-controlled search artifact vectors
checked by the `search_vectors` and `search_recovery_vectors` conformance
tests. They are still narrower than a blanket proof of fairness and
completeness for all future frontier growth, all rebuild schedules, and all
parallel modes without premises.

## Claimed Surface

The current proved or proof-backed claimed surface is:

- the Lean `SessionTypes`, `SessionCoTypes`, `Choreography`, `Protocol`, and
  `Runtime` models and theorem libraries
- the strict Rust↔Lean correspondence corpora and comparison contracts tracked
  in the Lean correspondence rows below
- the first-class protocol-critical capability/finalization/transition model
  carried by the Lean capability-model surface and its strict Rust↔Lean bridge
  correspondence suite
- the packaged first-party crates and binaries only at the level of
  operationally checked artifact/release assurance, not full mechanized proof

## Compiler and Macro Claim Boundary

The current public formal-verification claim does not include any Rust parser, lowering, projection, import/export, or macro-expansion entry path.
More concretely: the current public formal-verification claim does not include any Rust parser, lowering, projection, import/export, or macro-expansion entry path.

For the current claim:

- `parse_choreography_str`, `parse_choreography_file`, `choreography_to_global`,
  `local_to_local_r`, Rust-side projection/codegen/import-export helpers, and
  `tell!` macro expansion are outside the formal claim
- because those entry paths are outside the current formal claim, no
  compiler-facing theorem-object JSON/import-export path remains on the
  current claim-critical path
- those Rust compiler and macro paths are still covered by strict operational
  gates, especially the compiler-pipeline, projection-equivalence, exact-shape
  JSON, Lean-validator, and macro-UI suites
- the exact DSL fragment that would need mechanized compiler proof before the
  public claim can broaden is the theory-convertible subset already tracked in
  the property table below: straight-line send/recv, communicated `choice`,
  `call`, counted `loop`, and guarded recursion
- `par`, `case/of`, `timeout`, and any other fail-closed or runtime-only forms
  are outside both the current formal claim and that future proof-target subset

## Artifact Correspondence Claim

For the current public claim, the shipped first-party crate artifacts are
covered only by operational artifact correspondence, not by mechanized proof.

More concretely, the current release/artifact claim is:

- every publishable first-party crate tarball for the released version is built
  from the checked workspace manifests for that version
- the packaged tarballs compiled by the artifact lane are the same tarballs
  whose hashes, sizes, git revision, toolchain versions, and critical embedded
  resource hashes are recorded in the provenance manifest under
  `target/package-artifact-tarballs/provenance.json`
- critical embedded resources on the shipped path, including packaged README
  files, the embedded runtime grammar, and release metadata like the WASM
  example lockfile, are part of the audited artifact pipeline rather than an
  unchecked side channel

This is still narrower than a fully reproduced, mechanically proved binary
build pipeline. Cargo, crates.io, git hosting, and the local build toolchain
remain explicit external assumptions.

## Out of Scope / Assumption Boundaries

First-class protocol-critical capability semantics are in scope.
General host application authorization is out of scope.

The current public claim does not include:

- Rust parser/lowering/projection/import-export and `tell!` macro expansion
- user-supplied handlers, transports, plugins, or deployment adapters
- third-party infrastructure or deployment environments
- Cargo, crates.io, git hosting, OS, compiler, and toolchain correctness beyond
  the documented operational checks
- cryptographic hardness assumptions beyond standard SHA-256-style assumptions
- a blanket claim that every shipped Rust code path is mechanically proved
- general host application authorization or arbitrary app-policy capability
  systems unrelated to protocol-critical semantics

## Final Surface Audit

This table is the final public audit of which major surfaces are inside the
formal claim and which are deliberately outside it.

| Surface | Claim status | Note |
|---|---|---|
| Lean `SessionTypes`, `SessionCoTypes`, `Choreography`, `Protocol`, and `Runtime` semantics/theorems | inside | Core mechanized proof surface |
| Theorem-defined protocol-machine runtime core (`ConcreteScheduledStep`, claimed state/transition/event slice) | inside | Exact Rust↔Lean refinement/correspondence surface |
| First-party documented handlers (`InMemoryHandler`, `TelltaleHandler`, middleware profiles) | inside | Included through machine-checkable contract profiles |
| First-party documented transports (`InMemoryChannelTransport`, runtime topology TCP helper, `telltale-transport` TCP transport) | inside | Included through machine-checkable contract profiles |
| First-party packaged crate tarballs and embedded resources | inside | Included through the operational artifact-correspondence and provenance pipeline |
| Rust parser, lowering, projection, import/export helpers | outside | Publicly supported but outside the formal claim and guarded operationally |
| `tell!` and other proc-macro convenience surfaces | outside | Publicly supported but outside the formal claim and guarded operationally |
| User-supplied third-party handlers, transports, plugins, and deployment adapters | outside | Remain assumption-boundary integrations unless separately justified |
| External build/delivery infrastructure (`cargo`, crates.io, git hosting, toolchains, OS) | assumption boundary | Explicit public TCB items rather than proved surfaces |

## Public TCB Ledger

The current trusted computing base for the public claim is:

| Component | Why it remains trusted | Current enforcement |
|---|---|---|
| Lean kernel and imported proof libraries | theorem checker and proof environment | Lean build + code map + proof targets |
| Lean model definitions | theorems are only as correct as the modeled semantics | Lean proof suites and docs inventory |
| Rust/Lean bridge normalization and interchange | comparison/equality surface between Rust and Lean | `just check-bridge-normalization`, strict correspondence suites |
| Rust runtime implementation | shipped executable semantics are still comparison-checked, not fully proved | strict correspondence, semantic assurance, refinement slice |
| First-party handlers/transports | external impurity boundary for the runtime | handler-contract, transport-contract, and runtime-boundary suites |
| Release/package scripts and generated resources | artifact identity path from workspace to published crates | package-artifact, package-provenance, release-recovery, and docs-as-contract gates |
| Cargo / crates.io / git / toolchains | external delivery/build platform | operational checks only |

If that TCB shrinks or the claim broadens, this section must be updated before a
broader public wording is used.

## Final Public Claim Text

Use this exact wording in docs, release material, and summaries:

> Telltale is formally verified for the declared shipped surface documented in
> the verification inventory, under the listed public assumptions and TCB.

Supporting scope statement:

> The declared shipped surface includes the Lean semantics/theorems, the
> theorem-defined Rust↔Lean protocol-machine runtime correspondence core, the
> shipped first-party handler/transport contract boundary, and the shipped
> first-party crate artifacts through the audited artifact-correspondence
> pipeline. It does not include Rust compiler/macro entry paths or third-party
> integrations unless stated otherwise.

Supporting TCB statement:

> The remaining public TCB consists of the Lean kernel and imported proof
> libraries, the minimized Rust/Lean bridge/interchange layer, the comparison-
> checked Rust runtime implementation for the claim-critical surface, the
> documented first-party handler/transport boundary, the audited release/package
> and generated-resource pipeline, and external build/delivery infrastructure
> such as Cargo, crates.io, git hosting, and the underlying toolchains.

## Refinement Coverage Map

This map names the current protocol-machine state surfaces that matter to the
claimed runtime story and shows whether they are already inside the exact
Rust↔Lean refinement slice.

| Runtime state component | Rust surface | Lean surface | Current refinement status | Note |
|---|---|---|---|---|
| Coroutine identity, program counter, status, owned-endpoint count, progress-token count | `rust/machine/src/refinement.rs` (`CoroutineRefinementSlice`) | `lean/Runtime/Proofs/ProtocolMachine/ConcreteRefinement.lean` (`ConcreteCoroutineSlice`) | exact slice | Compared exactly across cooperative, Lean, and threaded executions today |
| Session id, role count, local-type entry count, buffer-edge count, buffered-message count, status tag, epoch | `rust/machine/src/refinement.rs` (`SessionRefinementSlice`) | `lean/Runtime/Proofs/ProtocolMachine/ConcreteRefinement.lean` (`ConcreteSessionSlice`) | exact slice | The theorem-side session slice now carries the same session-status and buffer-edge surface used by the Rust runtime slice |
| Scheduler ready queue, blocked-set tags, step count | `rust/machine/src/refinement.rs` (`SchedulerRefinementSlice`) | `lean/Runtime/Proofs/ProtocolMachine/ConcreteRefinement.lean` (`ConcreteSchedulerSlice`) | exact slice | The canonical scheduler slice is compared exactly today |
| Per-step event stream, theorem-defined `pre_state`/`post_state`, selected coroutine/type state, `session_type_counts`, `ready_queue`, and `blocked` snapshots | `rust/bridge/src/protocol_machine_runner.rs` (`ProtocolMachineStepState`), `rust/machine/src/refinement.rs` (`TransitionRefinementSummary`, `ClaimedRuntimeCoreBundle`) | `lean/Runtime/Proofs/ProtocolMachine/ConcreteRefinement.lean`, `lean/Runtime/Tests/ProtocolMachineRunner.lean` step-state JSON export | theorem-defined claimed transition surface with exact strict correspondence to Rust | The claim-critical transition object is now defined on the Lean side as a scheduled-step projection carrying pre/post slices, transition summary, and step event projection. Rust is compared against that exact surface, while compiler-layout-specific program counters remain exported for audit/debugging rather than as a separate semantic claim |
| Effect exchanges and output-condition trace | `rust/bridge/src/protocol_machine_runner.rs` (`effect_exchanges`, `output_condition_trace`) | Lean runner JSON export and strict bridge suites | outside the current claim-critical refinement core | Compared in strict lanes, but the current mechanized runtime-refinement claim is intentionally scoped to the theorem-defined protocol-machine state/transition/event surface above |
| Semantic-object families (handoffs, progress contracts, publications, agreement state, transformation obligations) | `rust/machine/src/engine/runtime_exec/introspection.rs`, `rust/machine/src/threaded/runtime_introspection.rs` | `lean/Runtime/Proofs/ProtocolMachine/SemanticObjects/*` | theorem-backed separately, outside the current claim-critical refinement core | Conservation theorems and strict comparison exist, but they are tracked as separate theorem families rather than folded into the concrete protocol-machine refinement core |

## Gate Ownership

The verification surface is organized around three canonical just-entry lanes.
`just ci-dry-run`, `check.yml`, and `verify.yml` should call these names rather
than duplicating their inner gate lists by hand.

| Gate | Canonical entry point | Primary owning files | Local run surface | GitHub run surface |
|---|---|---|---|---|
| Fast structural verification | `just check-fast-structure` | `justfile`, `scripts/check/ci-assurance-lanes.sh`, `scripts/check/formal-claim-scope.sh`, `scripts/check/verification-inventory.sh`, `scripts/check/bridge-normalization-ledger.sh`, `scripts/check/fail-closed-mutations.sh`, `scripts/check/source-doc-snippets.sh`, `scripts/check/tooling-convergence.sh`, Lean bootstrap scripts | `just check-pr-critical`, `just ci-dry-run`, direct local recipe use | `check.yml`, `verify.yml` |
| Focused assurance | `just check-focused-assurance` | `justfile`, strict Lean bridge suites, compiler pipeline suites, metatheory/refinement/runtime boundary suites | `just check-pr-critical`, `just ci-dry-run`, direct local recipe use | `check.yml`, `verify.yml` |
| Packaged artifact assurance | `just check-package-artifacts` | `justfile`, `scripts/check/package-artifacts.sh`, `scripts/check/package-provenance.sh`, `scripts/check/package-resource-audit.sh`, `scripts/check/release-recovery.sh` | `just check-pr-critical`, `just ci-dry-run`, direct local recipe use | `check.yml`, `verify.yml` |
| PR-critical assurance | `just check-pr-critical` | `justfile`, `.github/workflows/check.yml`, `.github/workflows/verify.yml` | `just ci-dry-run`, direct local recipe use | `check.yml`, `verify.yml` |
| Scheduled deep assurance | `just check-deep-assurance` | `justfile`, `.github/workflows/verify.yml`, scale-budget and larger-corpus verification lanes | `just ci-dry-run full`, direct local recipe use | `verify.yml` |

For staged diffs restricted to the simulator subsystem, the narrower local gate is now `just check-simulator-subsystem-staged`.
That path is intentionally local-only and does not replace the canonical repo-wide lanes above.
It exists so simulator-only staged work still gets formatting, compile, test, and simulator-doc link enforcement without being blocked by unrelated pre-existing breakage elsewhere in the workspace.

The dedicated local search-fairness gate is `just check-search-fairness`.
That gate is intentionally narrower than the canonical repo-wide lanes above
and exists to keep the Lean theorem-pack, parity fixture, and inventory rows
aligned while working inside `telltale-search`.

## Property Coverage Baseline

This baseline records whether each conserved-property bucket has at least one
high-signal executable assurance suite today.
It is intentionally curated.
The aim is to make gaps explicit rather than to produce vanity totals.

| Property bucket | Executable status | High-signal suites | Current note |
|---|---|---|---|
| Evidence | Spot checks | `rust/machine/tests/ownership_contracts.rs`, `rust/machine/tests/conformance_lean.rs` | Evidence-bearing paths are exercised directly in runtime and Lean-backed spot checks. The current theorem-focused authority slice starts from authoritative reads plus canonical publication/materialization and the explicit finalization/canonical-handle subsystem rather than the whole authority lifecycle family |
| Authority | Cross-path checks | `rust/machine/tests/ownership_contracts.rs`, `rust/simulator/tests/ownership_faults.rs` | The supported authority theorem slice is now explicit: evidence-bearing reads, transfer receipts, semantic handoff, and canonical publication/materialization are justified at the semantic-object and lifecycle layer, while broader host-policy lifecycle surfaces still rely on the wider protocol-machine conservation theorems |
| Lean correspondence | Strict executable validation checks | `rust/bridge/tests/lean_trace_validation.rs`, `rust/bridge/tests/property_tests.rs`, `rust/bridge/tests/protocol_bundle_admission_contracts.rs`, `rust/bridge/tests/protocol_machine_correspondence_tests.rs`, `rust/bridge/tests/protocol_machine_differential_steps.rs`, `rust/bridge/tests/capability_model_correspondence.rs`, `rust/bridge/tests/heap_lean_parity.rs`, `rust/simulator/tests/lean_reference_parity.rs` | `validateTrace`, `validateSimulationTrace`, `runSimulation`, `verifyProtocolBundle`, deterministic reconfiguration-transition validation, epoch-aware multi-step reconfiguration phase validation, explicit capability/finalization/transition-model correspondence, exact normalized simulator-trace parity, heap canonical-byte and replay parity, full protocol-machine event-stream parity, session-status parity, and step-indexed scheduler-state parity now execute in strict deterministic lanes for the supported corpus |
| Identity | Cross-path checks | `rust/machine/tests/serialization_replay.rs`, `rust/machine/tests/replay_persistence_identity.rs`, `rust/bridge/tests/semantic_object_roundtrip.rs`, `rust/bridge/tests/protocol_machine_cross_target_tests.rs`, `rust/bridge/tests/reconfiguration_recovery_harness.rs` | Replay, snapshot/restore, canonical fragment roundtrip, semantic-object identity, ownership-transfer replay artifacts, and bridge-exported reconfiguration snapshot identity are now checked as one differential family across multiple surfaces |
| Commitment | Spot + path checks | `rust/machine/tests/unit/protocol_machine/tests_semantic_state.rs`, `rust/machine/tests/conformance_lean.rs`, `rust/machine/tests/threaded_equivalence.rs`, `rust/machine/src/runtime_contracts.rs` | Progress and terminalization are covered across runtime contracts, lifecycle harnesses, and cross-driver parity |
| Commitment | Deterministic lifecycle harness | `rust/machine/src/engine/runtime_exec/semantic_state.rs` | Seeded lifecycle and adversarial corpus now exercise terminalization, invalidation, proof-gaps, and progress escalation as one semantic state machine |
| Structure | Deterministic runtime structure suite | `rust/machine/src/engine/runtime_exec/semantic_state.rs`, `rust/machine/tests/ownership_contracts.rs`, `rust/machine/src/composition.rs`, `rust/bridge/tests/protocol_bundle_admission_contracts.rs`, `rust/runtime/tests/generated_topology_public_path.rs` | Structural handoff locality, transformation obligations, pre-transfer witness invalidation, generated topology validation, executable region inheritance/conflict checks, bridge-to-runtime reconfiguration admission, atomic multi-step plan execution, canonical placement/transport-boundary phase artifacts, deterministic reconfiguration history, snapshot/restore state, and Lean-validated transition artifacts are now exercised on executable runtime paths |
| Premise | Fail-closed + admission checks | `rust/machine/src/runtime_contracts.rs`, `rust/machine/src/composition.rs`, `rust/language/src/compiler/parser/mod.rs`, `rust/runtime/tests/authority_compile_fail.rs`, `rust/runtime/tests/authority_control_flow_corpus.rs` | Assumption-heavy paths are rejected or gated, and the authority/control-flow boundary is now exercised with deterministic accepted/rejected `.tell` and `tell!` fixtures |
| Premise | End-to-end supported/fail-closed lowering | `rust/tests/dsl_runtime_semantics_tests.rs` | The theory-backed supported subset is explicit and executable: `choice`, `call`, counted `loop`, and recursion remain parser -> projection -> theory-conversion -> protocol-machine clean. `par`, `case/of`, and `timeout` stay outside that theory-convertible subset and are covered through the executable/runtime and boundary suites above |
| Admission | Theorem-pack and bundle assurance | `rust/bridge/tests/protocol_bundle_admission_contracts.rs`, `rust/bridge/tests/invariant_verification.rs`, `rust/machine/src/runtime_contracts.rs`, `rust/tests/dsl_runtime_semantics_tests.rs` | Proof-bundle declarations, capability drops, admission-gated runtime requests, and the explicit transported-theorem boundary ledger are now exercised end to end with stable diagnostics. Runtime-critical instantiated premises are separated from Lean-only assumption boundaries and black-box/background theorem inventory |
| Distributed topology | Deterministic harness | `rust/simulator/tests/distributed.rs`, `rust/machine/tests/topology_effect_ingress.rs`, `rust/runtime/tests/generated_topology_public_path.rs` | Distributed replay, ordered topology ingress, generated helpers, and invalid placement rejection now run through executable runtime paths without ambient network dependency |
| Simulator replay and classification assurance | Deterministic executable regression net | `rust/simulator/tests/correctness_regression.rs`, `rust/simulator/tests/threaded_backend.rs`, `rust/simulator/tests/classification_assurance.rs`, `rust/simulator/tests/environment_models.rs`, `rust/simulator/tests/distributed.rs`, `rust/simulator/tests/durable_assurance.rs` | Canonical exact, threaded exact, canonical replay, exact checkpoint resume, durable WAL fault injection, crash/recovery coverage matrices, write-ahead and evidence-consistency monitors, fail-closed theorem eligibility, approximation admissibility, normalized observability boundaries, observed-only distributed manifests, and non-authoritative helper surfaces are now checked together as one simulator-facing assurance family |
| Agreement | Runtime commitment semantics | `rust/machine/src/effect/core_types.rs`, `rust/machine/src/semantic_objects.rs`, `rust/machine/tests/threaded_equivalence.rs`, `rust/tests/dsl_runtime_semantics_tests.rs` | Agreement profiles and child-effect rollups are checked as runtime semantics across scenario tables, lowering, and cross-driver parity |
| Extension boundary | Deterministic parse-to-runtime dispatch + middleware stacks | `rust/runtime/tests/extension_integration.rs`, `rust/runtime/tests/middleware_semantic_hardening.rs` | Registered statement rules now parse into `Protocol::Extension`, lower into runtime extension effects, execute through deterministic extensible handlers, fail with stable diagnostics when handlers are missing or payloads are malformed, and remain middleware-safe under retry, metrics, trace, and seeded fault injection |
| Generated deployment path | Public helper end-to-end execution | `rust/runtime/tests/generated_topology_public_path.rs` | `handler(...)`, `with_topology(...)`, and named inline topology helpers are exercised as public surfaces with real loopback remote transport, negative validation coverage, executable region semantics, preservation of inline role-family constraints, and a transport-agnostic runtime topology API |
| Runtime substrate | Target-aware wrapper contracts | `rust/runtime/tests/runtime_substrate_contracts.rs`, `rust/runtime/tests/wasm_compat.rs` | Native and WASM wrapper seams now have direct regression coverage for `spawn`, `spawn_local`, and deterministic clock/RNG discipline, and deterministic assurance suites are guarded against accidental `SystemClock` / `SystemRng` drift |
| Handler contract boundary | Machine-checkable contract profiles for first-party handlers and transports, plus fail-closed extension dispatch | `rust/runtime/tests/handler_contracts.rs`, `rust/runtime/tests/transport_contracts.rs` | `ChoreoHandler` and the first-party transport families now have explicit machine-checkable contract ledgers that separate protocol-semantic obligations from policy choices, validate shipped production and harness profiles mechanically, and prove deterministic registered-only extension dispatch plus fail-closed unregistered behavior through runtime tests. User-supplied third-party handlers/transports remain outside the formal claim unless they separately satisfy the same contract |
| Recovery | Long-horizon differential harness | `rust/bridge/tests/reconfiguration_recovery_harness.rs` | Ownership-transfer replay artifacts, bridge export/import, topology-derived placement artifacts, atomic multi-step reconfiguration plans, snapshot/restore recovery, and deterministic suffix replay now execute as one end-to-end recovery family with explicit divergence detection |
| Artifact / release | Packaged-crate, provenance, and resume verification | `scripts/check/package-artifacts.sh`, `scripts/check/package-provenance.sh`, `scripts/check/package-resource-audit.sh`, `scripts/check/release-recovery.sh` | Every publishable crate now goes through the `cargo publish --dry-run --locked --no-verify` packaging path, package-manifest resource paths are checked before packaging, the full packaged crate set is compiled from extracted tarballs, critical embedded resources are compared byte-for-byte against source, external consumer canaries for `telltale`, `telltale-runtime`, and `telltale-bridge` run outside the workspace layout with exact last-line stdout assertions, a provenance manifest records tarball hashes plus source/resource/toolchain metadata for the packaged set, package-root resource escapes are fail-closed, the packaged WASM and embedded-grammar surfaces are verified explicitly, and release resume behavior is exercised under a deterministic fake cargo/git harness |
| Mutation pressure | Direct fail-closed perturbation suites | `rust/machine/src/runtime_contracts.rs`, `scripts/check/fail-closed-mutations.sh` | Representative bridge payload, theorem-boundary, source-derived docs-row, package-registry, package-manifest, package-resource, and inventory mutations are injected directly against the narrow owning gates so drift is rejected before broader integration lanes run |
| Concrete refinement | Exact cooperative/Lean/threaded state-slice parity plus Lean proof-connected slice | `rust/bridge/tests/protocol_machine_differential_steps.rs`, `rust/machine/tests/lean_protocol_machine_equivalence.rs`, `rust/machine/tests/threaded_equivalence.rs` | The first concrete protocol-machine refinement slice now compares coroutine/session/scheduler state exactly across Rust, Lean, and canonical threaded execution, exports bounded `u64` bridge fields fail-closed, and is connected to dedicated Lean refinement theorems over the same slice |
| Compiler / serialization pipeline | Strict DSL-to-theory lowering, exact-shape JSON bridge, and Lean-backed projection acceptance | `rust/bridge/tests/compiler_pipeline_conformance.rs`, `rust/bridge/tests/projection_equivalence.rs`, `rust/bridge/tests/proptest_json_roundtrip.rs`, `rust/bridge/tests/lean_integration_tests.rs`, `rust/bridge/tests/merge_semantics_tests.rs` | This pipeline is operationally checked, not part of the current formal claim: the supported DSL subset runs through parser -> `protocol_to_global()` / `local_to_local_r()` -> exact-shape import/export -> Lean projection export and validator acceptance in deterministic strict lanes, and bridge import rejects unknown fields fail-closed so schema drift cannot hide behind permissive parsing |
| Deadlock automation | Lean-sound regular-fragment checker mirrored into Rust diagnostics | `rust/types/src/local.rs`, `rust/bridge/tests/regular_practical_fragment_checks.rs`, `rust/tests/dsl_runtime_semantics_tests.rs` | The automatic deadlock-discharge fragment is now mechanically characterized as closed + contractive projected locals whose full unfold exposes send/recv, checked first in Lean on `SessionTypes.LocalTypeR`, mirrored in Rust only for macro/proof-status diagnostics, and exercised end to end through bridge parity and generated `proof_status` surfaces |
| Public docs as contract | Source-derived capability/admission, authority-support, and trust-surface tables | `rust/bridge/tests/docs_contract_tests.rs`, `scripts/check/verification-inventory.sh`, `scripts/check/bridge-normalization-ledger.sh` | The highest-value public verification/capability docs now separate source-derived tables from explanatory prose, and those rows are checked mechanically against runtime-contract, DSL-tier, and bridge-ledger facts |
| Deterministic scale budgets | Larger supported corpora with structural size envelopes | `rust/bridge/tests/scale_budget_contracts.rs` | Larger lowering/projection corpora, longer record/replay histories, larger reconfiguration snapshots, and larger Lean bridge payloads now run as deterministic structural-budget gates with exact replay/snapshot equality and explicit serialized-size envelopes rather than ambient wall-clock benchmarks |

## Bridge Normalization Trust Surface

The Lean bridge still contains a small amount of trusted normalization logic.
That logic is intentionally narrow and is audited explicitly in CI by
`just check-bridge-normalization`.
The rows in this table are source-derived and checked by
`telltale_bridge::bridge_normalization_ledger()` via
`scripts/check/bridge-normalization-ledger.sh`.

| Surface | Normalization rule | Classification | Why permitted |
|---|---|---|---|
| semantic-audit tick normalization | Normalize only `tick`, and only per extracted session id | irreducible trusted comparison logic | Absolute cross-session scheduling order is not semantic protocol truth. Per-session observable order is. |

Enforcing artifacts:

- `rust/bridge/src/protocol_machine_trace.rs`
- `rust/bridge/tests/protocol_machine_correspondence_tests.rs`
- `rust/bridge/tests/protocol_machine_differential_steps.rs`
Session-status ordering is no longer part of the trusted comparison surface.
Both the Lean runner and Rust-side correspondence harness now emit session rows
in canonical `sid` order, so comparison is exact rather than normalized.

The older `schema_version` backfill helper remains only as a test-only
compatibility shim for legacy fixture coverage. It is outside the claim-critical
bridge surface and must not synthesize semantic content.

## Explicit Unsupported / Fail-Closed Notes

No explicit unsupported or fail-closed implementation-gap notes remain in the
tracked inventory. New notes should be added here only for intentional,
documented non-goals or for temporary regressions that are not yet executable.

The inventory deliberately does not track raw unit-test totals, assertion
counts, or line counts for tests.
