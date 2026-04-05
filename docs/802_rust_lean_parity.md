# Rust-Lean Bridge and Parity

This document defines the typed Rust↔Lean bridge surface and the parity contract enforced across that boundary for protocol-machine behavior, choreography projection, semantic-object schemas, and deviation governance.

## Contract Levels

Parity is enforced at two levels. Level 1 covers policy and data shape parity for shared runtime encodings. Level 2 covers behavior parity for executable traces under the declared concurrency envelope.

## Bridge Scope

The `telltale-bridge` crate is the typed boundary between Rust artifacts and Lean validation entrypoints.
It handles JSON conversion, schema versioning, runner invocation, trace comparison, semantic-object export, and typed invariant bundle export.

The bridge does not define protocol-machine semantics.
Semantics remain in `telltale-machine`, `telltale-theory`, and Lean runtime modules.
Host-runtime handlers also remain outside the bridge and re-enter through typed effect surfaces.

This document covers the bridge behavior implemented in `rust/bridge/src`:

- `export`
- `import`
- `schema`
- `runner`
- `protocol_machine_runner`
- `heap_parity_runner`
- `sim_reference`
- `semantic_objects`
- `protocol_machine_trace`
- `invariants`
- `equivalence`
- `validate`

## Bridge Crate Surface

The canonical public bridge surface uses:

- `LeanRunner`
- `ProtocolMachineRunner`
- `HeapParityRunner`
- `ProtocolMachineRunInput`
- `ProtocolMachineRunOutput`
- `HeapParityOutput`
- `ProtocolMachineSemanticObjects`

No public legacy compatibility modules are part of the supported bridge story.

## Features and Binaries

The crate has feature-gated modules and binaries.
The default feature set enables Lean runner integration.

```toml
[features]
default = ["runner"]
cli = ["clap"]
runner = ["telltale-theory"]
exporter = ["telltale-runtime", "anyhow", "bpaf"]
golden = ["clap", "anyhow", "runner"]

[[bin]]
name = "lean-bridge"
required-features = ["cli"]

[[bin]]
name = "lean-bridge-exporter"
required-features = ["exporter"]

[[bin]]
name = "golden"
required-features = ["golden"]
```

`runner` controls `LeanRunner`, `ProtocolMachineRunner`, `HeapParityRunner`, and the equivalence modules.
Without `runner`, conversion and schema modules remain available.

## Conversion and Schema Families

`export::global_to_json()` and `export::local_to_json()` map Rust protocol types into Lean-compatible JSON.
`import::json_to_global()` and `import::json_to_local()` parse those JSON forms back into `GlobalType` and `LocalTypeR`.

The bridge defines three main schema families with explicit version constants:

| Family | Version Constant | Value | Primary Payloads |
|---|---|---|---|
| Lean bridge core | `LEAN_BRIDGE_SCHEMA_VERSION` | `lean_bridge.v1` | `ProtocolMachineRunInput`, `ProtocolMachineRunOutput`, `SimRunInput`, `SimRunOutput`, replay bundles |
| Protocol bundles | `PROTOCOL_BUNDLE_SCHEMA_VERSION` | `protocol_bundle.v1` | `ProtocolBundle` |
| Protocol-machine semantic objects | `SEMANTIC_OBJECTS_SCHEMA_VERSION` | `protocol_machine.semantic_objects.v1` | `ProtocolMachineSemanticObjects` export payloads |

`schema::ensure_supported_schema_version()` rejects unsupported bridge-core versions.
Unsupported or missing schema versions are rejected rather than normalized.

## Lean Runners

`LeanRunner` invokes the validator binary at `lean/.lake/build/bin/telltale_validator`.
It supports validation and projection export workflows.

`ProtocolMachineRunner` invokes `lean/.lake/build/bin/protocol_machine_runner`.
It serializes `ProtocolMachineRunInput` to stdin and parses `ProtocolMachineRunOutput` from stdout.
It also exposes `validate_trace()`, `run_reference_simulation()`, `validate_simulation_trace()`, `verify_invariants()`, and `compare_execution()`.

`HeapParityRunner` invokes `lean/.lake/build/bin/heap_parity_runner`.
It loads the published heap parity corpus and returns typed `HeapParityOutput` values for strict Rust↔Lean comparison.

## Semantic Objects and Trace Normalization

`semantic_objects` provides the canonical bridge payloads for the protocol-machine semantic-object family.
`ProtocolMachineRunOutput.semantic_objects` and `ProtocolMachineRunOutput.effect_exchanges` are the canonical bridge-side exports for semantic runtime state and typed effect exchange data.

`protocol_machine_trace::event_session()` extracts session ids from common event shapes.
`normalize_semantic_audit()` rewrites tick values into per-session local counters.
`semantic_audits_equivalent()` and `observationally_equivalent()` compare traces after that normalization.

## Invariant, Equivalence, and Validator Utilities

`invariants` defines typed claim schemas for Lean-side protocol bundle verification through `ProtocolBundle`.
`equivalence::EquivalenceChecker` supports both golden-file comparison and live Lean comparison.
`validate::Validator` provides lightweight checks for projection, roundtrip, and subtype-related workflows that do not require full protocol-machine execution.

## Bridge Test and Tooling Lanes

Bridge tests in `rust/bridge/tests` cover conversion, projection parity, schema compatibility, invariant verification, protocol-machine correspondence, and heap parity.
Examples include:

- `lean_integration_tests.rs`
- `lean_trace_validation.rs`
- `projection_runner_tests.rs`
- `protocol_machine_correspondence_tests.rs`
- `protocol_machine_differential_steps.rs`
- `heap_lean_parity.rs`
- `capability_model_correspondence.rs`
- `protocol_bundle_admission_contracts.rs`

These lanes align with repository-level gates such as `just check-parity --types`, `just check-parity --suite`, and `just check-capability-gates`.

## Protocol-Machine Policy and Data Shapes

The following shapes must remain aligned between Lean and Rust unless a deviation entry is active.

| Area | Lean Surface | Rust Surface | Status |
|---|---|---|---|
| `FlowPolicy` variants | `Runtime/ProtocolMachine/Model/Knowledge.lean` | `rust/machine/src/engine/` | Aligned |
| `FlowPredicate` variants | `Runtime/ProtocolMachine/Model/Knowledge.lean` | `rust/machine/src/engine/` | Aligned |
| `OutputConditionPolicy` | `Runtime/ProtocolMachine/Model/OutputCondition.lean` | `rust/machine/src/output_condition.rs` | Aligned |
| Capability/finalization model (`FinalizationPath`, `FinalizationReadClass`, `FinalizationStage`, `RuntimeUpgradeArtifact`) | `lean/Runtime/Proofs/CapabilityModel.lean`, `Runtime/Tests/ProtocolMachineRunner.lean` | `rust/machine/src/semantic_objects.rs`, `rust/machine/src/composition.rs`, `rust/machine/src/capabilities.rs` | Aligned |
| Runtime `Value` variants | `Protocol/Values.lean` | `rust/machine/src/coroutine.rs` | Aligned |
| `ProgressToken` fields | `Runtime/ProtocolMachine/Model/State.lean` | `rust/machine/src/coroutine.rs` | Aligned |
| `CommunicationReplayMode` variants | `Runtime/ProtocolMachine/Model/Config.lean` | `rust/machine/src/communication_replay/mod.rs` | Aligned |
| `SignedValue` transport fields (`payload`, `signature`, `sequence_no`) | `Runtime/ProtocolMachine/Model/TypeClasses.lean` | `rust/machine/src/buffer.rs` | Aligned |
| Payload hardening controls (`payload_validation_mode`, `max_payload_bytes`) | `Runtime/ProtocolMachine/Model/Config.lean`, `Runtime/ProtocolMachine/Semantics/ExecComm.lean` | `rust/machine/src/engine/` | Aligned |
| Register bounds failure semantics (`OutOfRegisters`) | `Runtime/ProtocolMachine/Semantics/ExecSteps.lean` | `rust/machine/src/engine/`, `rust/machine/src/threaded/` | Aligned |
| Explicit failure/timeout observable event inventory (`TimeoutIssued`, `CancellationRequested`, `Cancelled`, `FailureBranchEntered`, `SessionTerminal`) | `Runtime/ProtocolMachine/Model/State.lean`, `Runtime/ProtocolMachine/Runtime/Json.lean`, `Runtime/Proofs/TheoremPack/ReleaseConformance.lean` | `rust/machine/src/engine/protocol_machine_config.rs`, `rust/machine/src/trace.rs` | Aligned |

These checks are automated by `just check-parity --types`.

## Protocol-Machine Behavior Contract

| Regime | Required Behavior |
|---|---|
| Canonical `n = 1` | Exact parity between cooperative and threaded execution |
| Threaded `n > 1` | Conformance within declared `EnvelopeDiff` bounds |
| Failure-visible artifacts | Snapshot parity within declared failure envelope class |
| Speculation | No sentinel fallback behavior for join/abort with deterministic gated semantics |
| Register bounds | Out-of-range register operands fail with `OutOfRegisters` (no unchecked panic paths) |
| Load boundary | Runtime rejects malformed trusted image role/type shape before session open |
| Explicit failure and timeout ordering | per-session trace preserves `TimeoutIssued`, `CancellationRequested`, `Cancelled`, `FailureBranchEntered`, and `SessionTerminal` ordering |

These checks are automated by `just check-parity --suite`.

Explicit failure, timeout, cancellation, and session-terminal events are part of the executable Lean runtime/event inventory.
Replay tagging, JSON serialization, and theorem-pack release conformance all use the same observable event family.

Language-level nominal `effect` declarations do not introduce a second runtime bridge.
Their intended justification remains the existing protocol-machine `invoke` boundary and handler-typing obligations in `Runtime/Proofs/protocol machine/BridgeStrengthening.lean`.

Typed effect requests and outcomes are part of the parity surface directly.
Rust and Lean must agree on effect-interface metadata, request bodies, outcome statuses, and replay-visible effect exchanges.
That now includes the internal `wal_sync` effect metadata and the shared durable recovery vocabulary used to classify checkpoint-plus-WAL resume decisions.

## Effect Interface Justification

The language-level effect interface design follows the same proof boundary used by the MPST-plus-effects papers and the Lean runtime.

- typed effect obligations remain attached to the executable handler boundary,
  not to a separate host-only mechanism
- authority-sensitive language constructs must lower to explicit effect
  observations, witness issuance/consumption, and failure-visible events
- proof-carrying evidence remains fail-closed on missing or invalid authority
- behavioral correspondence is observational, through traces and effect/audit
  surfaces, rather than through arbitrary host internals

This is why the current language design is nominal-first:

- `effect` declarations and `uses` clauses are stable names for explicit host
  obligations
- lowering stays centered on the existing protocol-machine `invoke` and `EffectSpec` story
- generalized effect polymorphism waits until the nominal surface,
  lowering, and parity/audit semantics are stable

### Durability Alignment

The durability layer is now part of the documented Rust↔Lean correspondence boundary for runtime effects.

- Rust `EffectRequestBody::WalSync` corresponds to Lean `walSyncMetadata` plus the shared `EffectRequestBody` / `EffectResponse` effect model in `lean/Runtime/ProtocolMachine/Model/Effects.lean`
- Rust `DurableRecoveryAction` / `DurableRecoveryDecision` correspond to Lean `Runtime.ProtocolMachine.Model.DurableRecoveryAction` / `DurableRecoveryDecision`
- The current Lean theorem surface for this layer is intentionally narrow:
  `walSyncMetadata_legal`, internal-handler admissibility, recovery-rank monotonicity from `AgreementEscalation`, and gate-crossing / terminal-truth consequences from `DurableRecoveryDecision.sound`

The simulator-side WAL backend wrappers and fault-injection helpers remain Rust assurance surfaces.
They consume the typed durability vocabulary above but are not themselves part of the current mechanized claim.

## Choreography Projection Parity

The parity scope covers projection behavior from global choreography forms to local session forms. This includes `send`, `choice`, recursion, and merge behavior for non-participant branches. Rust-only runtime conveniences and extension-only AST constructs are excluded.

### Shared Projection Semantics

Rust and Lean are expected to align on the following surfaces.

| Area | Lean Surface | Rust Surface | Status |
|---|---|---|---|
| Projection core relation | `lean/Choreography/Projection/Project.lean` | `rust/runtime/src/compiler/projection.rs` | Aligned on supported subset |
| Merge semantics | `lean/Choreography/Projection/Erasure/Merge.lean` | `rust/language/src/compiler/projection/merge.rs` | Aligned |
| Projection validation pipeline | `lean/Choreography/Projection/Validator.lean` | `rust/bridge/src/runner_projection_export.rs` | Aligned |

### Rust-Only Extensions

The following surfaces are intentionally outside direct Lean parity. They must be documented as extensions and must not be confused with theorem-backed projection claims.

| Surface | Rust Module | Parity Status |
|---|---|---|
| `LocalType::LocalChoice` | `rust/language/src/ast/local_type.rs` | Rust extension |
| Timeout wrappers in local AST | `rust/language/src/ast/local_type.rs` | Rust extension |
| Effect runtime `Parallel` execution contract | `rust/runtime/src/effects/interpreter.rs` | Rust runtime contract |

### Projection Cross-Validation

Projection cross-validation is exercised through `rust/bridge/tests/projection_runner_tests.rs`. Tests skip per test when the Lean validator binary is unavailable. Skipping one test must not terminate the rest of the suite.

## Heap Parity Surface

The runtime heap now has a focused Lean mirror for the parts of the contract that must remain cross-implementation stable.

| Surface | Lean Surface | Rust Surface | Status |
|---|---|---|---|
| Canonical resource bytes and tagged preimages | `lean/Runtime/Resources/HeapModel.lean` | `rust/runtime/src/heap/encoding.rs`, `rust/runtime/src/heap/resource.rs` | Aligned |
| Active/nullifier ordering and replay interpreter | `lean/Runtime/Resources/HeapModel.lean`, `lean/Runtime/Proofs/Heap.lean` | `rust/runtime/src/heap/heap_impl.rs` | Aligned |
| Proof-index and sibling-direction semantics | `lean/Runtime/Resources/HeapModel.lean` | `rust/runtime/src/heap/merkle.rs` | Aligned |
| Published heap parity corpus | `lean/Runtime/Tests/HeapParityRunner.lean` | `rust/runtime/tests/data/heap_lean_parity_v1.json`, `rust/bridge/tests/heap_lean_parity.rs` | Aligned |

This heap lane is narrower than a full cryptographic equivalence proof.
Lean does not currently implement BLAKE3.
Instead, Lean reconstructs canonical bytes, tagged preimages, ordering, proof-path structure, and deterministic replay from the published corpus, and Rust must match the published digest values exactly.

The authoritative digest corpus remains the published heap vector set documented in [Resource Heap](602_resource_heap.md).
`rust/runtime/tests/data/heap_vectors_v1.json` remains the minimal public digest vector file.
`rust/runtime/tests/data/heap_lean_parity_v1.json` is the richer Rust↔Lean parity corpus.

### Heap Enforcement

The Lean heap surface is split into three files:

| Surface | Location |
|---|---|
| Executable heap model | `lean/Runtime/Resources/HeapModel.lean` |
| Basic determinism lemmas | `lean/Runtime/Proofs/Heap.lean` |
| Executable parity runner | `lean/Runtime/Tests/HeapParityRunner.lean` |

The strict Rust↔Lean heap suite is `rust/bridge/tests/heap_lean_parity.rs`.
It runs the Lean executable, recomputes the same values in Rust through public heap APIs, and checks that both sides match the published corpus exactly.

This lane justifies a stronger statement than “heap behavior is only tested in Rust,” but it is still not a full theorem-backed digest proof.

Current claim:

- Lean and Rust agree on canonical heap bytes, tagged preimages, ordering, proof-path structure, and deterministic replay for the published heap corpus.
- Rust produces the authoritative digest values, and those values must match the published vectors exactly.

Not yet claimed:

- a pure Lean implementation of BLAKE3
- a theorem that the Rust digest implementation is cryptographically correct
- full mechanized heap refinement against all runtime heap code paths

## State Schema

Lean and Rust schemas remain shape-equivalent on safety-visible and replay-visible fields. Runtime-only helper fields are permitted when they do not alter observable semantics.

### Semantic Object Family

The canonical cross-language semantic-object family must remain aligned between Lean, Rust, and the Rust/Lean bridge.

| Object | Lean Surface | Rust Surface | Bridge Surface | Status |
|---|---|---|---|---|
| `OperationInstance` | `Runtime/ProtocolMachine/Model/SemanticObjects/Core.lean` | `rust/machine/src/semantic_objects.rs` | `rust/bridge/src/semantic_objects.rs` | Aligned |
| `OutstandingEffect` | `Runtime/ProtocolMachine/Model/SemanticObjects/Core.lean` | `rust/machine/src/semantic_objects.rs` | `rust/bridge/src/semantic_objects.rs` | Aligned |
| `SemanticHandoff` | `Runtime/ProtocolMachine/Model/SemanticObjects/Core.lean` | `rust/machine/src/semantic_objects.rs` | `rust/bridge/src/semantic_objects.rs` | Aligned |
| `TransformationObligation` | `Runtime/ProtocolMachine/Model/SemanticObjects/Core.lean` | `rust/machine/src/semantic_objects.rs` | `rust/bridge/src/semantic_objects.rs` | Aligned |
| `AuthoritativeRead` / `ObservedRead` | `Runtime/ProtocolMachine/Model/SemanticObjects/Core.lean` | `rust/machine/src/semantic_objects.rs` | `rust/bridge/src/semantic_objects.rs` | Aligned |
| `MaterializationProof` / `CanonicalHandle` | `Runtime/ProtocolMachine/Model/SemanticObjects/Core.lean` | `rust/machine/src/semantic_objects.rs` | `rust/bridge/src/semantic_objects.rs` | Aligned |
| `ProgressContract` | `Runtime/ProtocolMachine/Model/SemanticObjects/Core.lean` | `rust/machine/src/semantic_objects.rs` | `rust/bridge/src/semantic_objects.rs` | Aligned |
| `ProgressTransition` | `Runtime/ProtocolMachine/Model/SemanticObjects/Core.lean` | `rust/machine/src/semantic_objects.rs` | `rust/bridge/src/semantic_objects.rs` | Aligned |
| typed effect metadata / request / outcome model | `Runtime/ProtocolMachine/Model/Effects.lean` | `rust/machine/src/effect.rs` | `rust/bridge/src/protocol_machine_runner.rs` (`effect_exchanges`) | Aligned |

`OperationInstance` and `OutstandingEffect` are compared as canonical runtime state, not as post-hoc derivations from generic effect-trace order.
Parity on these objects covers owner identity, phase/status, budget/invalidation fields, dependent-operation edges, and terminal publication state.

`SemanticHandoff` parity also covers explicit owner revocation and activation (`revoked_owner_id`, `activated_owner_id`).
`TransformationObligation` parity covers transformed fragments, affected operations/effects, transport vs invalidation policy, and publication transfer or revocation.
Bridge-side execution comparison reports these handoff and invalidation surfaces separately from raw trace equivalence.
This prevents stale-owner and late-result mismatches from hiding inside otherwise equivalent instruction traces.

The same strict bridge layer now also compares the first-class
capability/finalization/transition facade exported by
`inspectCapabilityModel`. That lane checks canonical vs invalidated
finalization paths and committed-cutover vs rolled-back runtime-upgrade
artifacts directly, instead of treating them as documentation-only structure.

Canonical layout mapping for this family is:

- Lean executable spec:
  `lean/Runtime/ProtocolMachine/Model/SemanticObjects/*.lean`
- Rust runtime mirror:
  `rust/machine/src/semantic_objects.rs`
- Rust bridge mirror:
  `rust/bridge/src/semantic_objects.rs`
  This bridge surface must re-export the machine semantic-object family rather than carrying a duplicate schema copy.

`Region` is now part of the canonical protocol-machine semantic-object family.
It names the session-scoped locality and framing domain over operations,
effects, authoritative reads, canonical handles, and publication events.

`ProgressContract` parity covers bounded-wait metadata, explicit no-progress and degraded states, and timeout escalation state.
`ProgressTransition` parity makes those escalations replay-visible instead of leaving them as target-specific scheduling heuristics.

The Lean implementation layer keeps executable semantic-object definitions in `Runtime/ProtocolMachine/Model/SemanticObjects/Core.lean`.
Basic theorem-facing predicates live in `Runtime/ProtocolMachine/Model/SemanticObjects/Discipline.lean`.
The re-export facade is `Runtime/ProtocolMachine/Model/SemanticObjects.lean`.

Deferred-effect admissibility, retry shape, and late-result rejection live in `Runtime/ProtocolMachine/Model/SemanticObjects/OutstandingEffects.lean`.
Associated theorem-facing lemmas are in `Runtime/Proofs/ProtocolMachine/SemanticObjects/OutstandingEffects.lean`.

Semantic handoff realization lives in `Runtime/ProtocolMachine/Model/SemanticObjects/SemanticHandoffTransition.lean`.
Theorem-facing owner/publication/delegation bridge lemmas are in `Runtime/Proofs/ProtocolMachine/SemanticObjects/SemanticHandoff.lean`.

Authoritative-read commitment contexts and canonical publication-path uniqueness live in `Runtime/ProtocolMachine/Model/SemanticObjects/AuthoritativeReadsPublication.lean`.
Observer-projection, blindness, and noninterference lemmas are in `Runtime/Proofs/ProtocolMachine/SemanticObjects/AuthoritativeReadsPublication.lean`.

Proof-backed success contexts and materialization-proof adequacy live in `Runtime/ProtocolMachine/Model/SemanticObjects/MaterializationSuccess.lean`.
Lemmas ruling out proof-less success and observational materialization promotion are in `Runtime/Proofs/ProtocolMachine/SemanticObjects/MaterializationSuccess.lean`.

Progress-contract semantics live in `Runtime/ProtocolMachine/Model/SemanticObjects/ProgressContracts.lean`.
Owner-liveness, escalation, and Lyapunov/weighted-measure/scheduling-bound compatibility lemmas are in `Runtime/Proofs/ProtocolMachine/SemanticObjects/ProgressContracts.lean`.

Transformation-local obligation bundles live in `Runtime/ProtocolMachine/Model/SemanticObjects/TransformationLocalObligations.lean`.
Coverage/admissibility lemmas and lightweight linking/reconfiguration bridge structures are in `Runtime/Proofs/ProtocolMachine/SemanticObjects/TransformationLocalObligations.lean`.

Theorem-pack attachment for these semantic-object proof families lives in `Runtime/Proofs/InvariantSpace.lean` via `SemanticObjectWitnessBundle`.
The same attachment points are exposed through `Runtime/Proofs/TheoremPack/Inventory.lean`, `Runtime/Proofs/TheoremPack/API.lean`, and `Runtime/Proofs/Contracts/RuntimeContracts.lean`.

### Lean ProtocolMachineState

Source: `lean/Runtime/ProtocolMachine/Model/State.lean`

`CoroutineState` contains `id`, `programId`, `pc`, `regs`, `status`, `effectCtx`, `ownedEndpoints`, `progressTokens`, `knowledgeSet`, `costBudget`, and `specState`.

The Lean protocol-machine state structure (`ProtocolMachineState`) contains `config`, `programs`, `coroutines`, `sessions`, `monitor`, `sched`, `resourceStates`, `persistent`, `obsTrace`, failure/topology state fields, and output-condition state.

### Rust Protocol Machine

Source: `rust/machine/src/engine/`

The Rust protocol-machine structure (`ProtocolMachine`, exported as an alias for `protocol machine`) contains `config`, `programs`, `code`, `coroutines`, `sessions`, `monitor`, `sched`, `resource_states`, `persistent`, `obs_trace`, symbol/clock counters, failure/topology state fields, and output-condition state.

`Coroutine` in `rust/machine/src/coroutine.rs` contains identity/program/pc/status, register file, ownership/progress/knowledge sets, cost budget, speculation metadata, and effect context.

### Canonical Rust Runtime Object Inventory

The Rust public runtime surface now exposes one canonical naming scheme:
protocol-machine objects use `ProtocolMachine*`, guest-runtime objects use
`GuestRuntime*`, and bridge execution objects use `ProtocolMachineRunner*`.
No public `telltale_machine::vm::*`, `telltale_machine::threaded::*`,
`telltale_bridge::protocol_machine_runner::*`, or `telltale_bridge::vm_trace::*`
entrypoints remain.

| Runtime Object | Lean Surface | Rust Surface | Bridge Surface | Status |
|---|---|---|---|---|
| protocol-machine config | `Runtime/ProtocolMachine/Model/Config.lean` | `telltale_machine::ProtocolMachineConfig` | `telltale_bridge::ProtocolMachineRunInput` | Aligned |
| protocol-machine state | `Runtime/ProtocolMachine/Model/State.lean` | `telltale_machine::ProtocolMachineState` | `telltale_bridge::ProtocolMachineRunOutput` | Aligned |
| protocol-machine executor | `Runtime/ProtocolMachine/API.lean`, `Runtime/ProtocolMachine/Runtime/Runner.lean` | `telltale_machine::ProtocolMachine` | `telltale_bridge::ProtocolMachineRunner` | Aligned |
| protocol-machine step result | `Runtime/ProtocolMachine/Model/State.lean` | `telltale_machine::StepResult` | `telltale_bridge::ProtocolMachineStepState` | Aligned |
| protocol-machine run status | `Runtime/ProtocolMachine/Model/State.lean` | `telltale_machine::RunStatus` | `telltale_bridge::ProtocolMachineRunOutput.status` | Aligned |
| protocol-machine error surface | `Runtime/ProtocolMachine/Model/State.lean`, `Runtime/ProtocolMachine/Runtime/Json.lean` | `telltale_machine::ProtocolMachineError` | `telltale_bridge::LeanStructuredError` | Aligned |
| protocol-machine memory accounting | `Runtime/ProtocolMachine/Model/State.lean` | `telltale_machine::ProtocolMachineMemoryUsage`, `telltale_machine::ProtocolMachineRetainedBytes` | n/a | Aligned |
| guest runtime driver | `Runtime/ProtocolMachine/API.lean` | `telltale_machine::GuestRuntime`, `telltale_machine::ThreadedGuestRuntime` | n/a | Aligned |
| threaded protocol-machine adapter | `Runtime/ProtocolMachine/API.lean`, `Runtime/ProtocolMachine/Composition.lean` | `telltale_machine::ThreadedProtocolMachine` | parity tests under `rust/bridge/tests/protocol_machine_cross_target_tests.rs` | Aligned |
| semantic-object inventory | `Runtime/ProtocolMachine/Model/SemanticObjects*.lean` | `telltale_machine::{ProtocolMachineSemanticObjects, OperationInstance, OutstandingEffect, SemanticHandoff, TransformationObligation, AuthoritativeRead, ObservedRead, MaterializationProof, CanonicalHandle, PublicationEvent, Region, ProgressContract, ProgressTransition}` | `telltale_bridge::{ProtocolMachineSemanticObjects, OperationInstance, OutstandingEffect, SemanticHandoff, TransformationObligation, AuthoritativeRead, ObservedRead, MaterializationProof, CanonicalHandle, PublicationEvent, Region, ProgressContract, ProgressTransition}` | Aligned |
| runtime admission contracts | `Runtime/Proofs/Contracts/RuntimeContracts.lean` | `telltale_machine::{requires_protocol_machine_runtime_contracts, admit_protocol_machine_runtime, enforce_protocol_machine_runtime_gates, request_determinism_profile, runtime_capability_snapshot}` | n/a | Aligned |

## Runtime Capability Gates

Runtime modes that require theorem/capability evidence are admission gated.

| Gate Surface | Lean API | Rust API | Status |
|---|---|---|---|
| Advanced mode admission | `requiresVMRuntimeContracts`, `admitVMRuntime` | `requires_protocol_machine_runtime_contracts`, `admit_protocol_machine_runtime` | Aligned |
| Determinism profile validation | `requestDeterminismProfile` | `request_determinism_profile` | Aligned |
| Runtime capability snapshot | `runtimeCapabilitySnapshot` | `runtime_capability_snapshot` | Aligned |

The Rust surfaces are in `rust/machine/src/runtime_contracts.rs` and `rust/machine/src/composition.rs`.
On the Lean side, `TheoremPackCapabilityContract.semanticAttachmentPoints` provides the canonical runtime-facing list of enabled semantic-object theorem attachment points.

## Determinism Profiles

| Profile | Lean | Rust | Status |
|---|---|---|---|
| Full | `full` | `DeterminismMode::Full` | Aligned |
| Modulo effect trace | `moduloEffectTrace` | `DeterminismMode::ModuloEffects` | Aligned |
| Modulo commutativity | `moduloCommutativity` | `DeterminismMode::ModuloCommutativity` | Aligned |
| Replay | `replay` | `DeterminismMode::Replay` | Aligned |

`Full` is exact-trace mode.
`ModuloEffects` and `ModuloCommutativity` require mixed-profile capability evidence and artifact support.
`Replay` requires replay artifact support and mixed-profile capability evidence.

## Threaded Concurrency Envelope

| Regime | Lean Surface | Rust Surface | Status |
|---|---|---|---|
| `n = 1` exact refinement | `runScheduledThreaded_one_eq_runScheduled` | `threaded_equivalence.rs::test_threaded_matches_cooperative` | Aligned |
| Spawn step parity (`n = 1`) | `Runtime/ProtocolMachine/Semantics/ExecControl.lean`, `Runtime/ProtocolMachine/Semantics/ExecSteps.lean` | `differential_step_corpus.rs::threaded_matches_cooperative_step_corpus_control_spawn` | Aligned |
| Certified-wave fallback | `executeCertifiedRound` | `threaded.rs` wave certificate check with one-step fallback | Aligned |
| `n > 1` envelope-bounded parity | `ThreadedRoundRefinementPremises` (premise-scoped) | `parity_fixtures_v2.rs::envelope_bounded_parity_holds_for_n_gt_1` | Aligned under envelope contract |

## Simulator Field Mirror

Lean includes executable mirror dynamics for simulator field handlers under `lean/Runtime/Simulation/`. Rust field handlers live under `rust/simulator/src/field_handlers/`.
The mirror now includes a Lean-native field-model boundary in `lean/Runtime/Simulation/Field.lean`, including built-in catalog dispatch and default initial-state derivation for shipped field families.
It remains an executable parity layer, not a mirror of Rust trait objects or serde-based scenario parsing.

Parity fixtures are enforced by:

- `rust/simulator/tests/field_handler_parity.rs`
- `lean/Runtime/Tests/SimulatorParity.lean` (built as `simulator_parity_tests`)

## Reduced Semantic-Effect Parity

Lean also publishes a reduced semantic-effect fixture surface for the protocol-machine/runtime boundary.
This lane is narrower than full executable protocol-machine equivalence: it checks the semantic classification we rely on for effect-facing debugging and replay exactness without claiming that Lean executes the full Rust effect handler stack.

The reduced surface covers:

- effect kind
- lifecycle classification (`blocked` / `succeeded`)
- interface and operation naming
- output-condition predicate material visible to publications
- whether the successful send path materializes an authoritative publication handle

Parity fixtures are enforced by:

- `lean/Runtime/Tests/SemanticEffectParity.lean` (built as `semantic_effect_parity_runner`)
- `rust/machine/tests/semantic_effect_lean.rs`
- `rust/simulator/tests/semantic_effect_lean.rs`

The machine and simulator tests compare canonical Rust outputs against the Lean fixture bundle for:

- one blocked-send fixture
- one successful send/publication fixture
- one `output_condition_hint` fixture
- one `wal_sync` fixture

This lane is intended to keep Lean, Rust machine semantics, replay/runtime behavior, and simulator artifact extraction aligned on the effect-visible semantic slice that matters for time-travel debugging and exact replay.

## Lean Module Boundaries

The `lean/Runtime/ProtocolMachine` directory is organized into executable and proof modules.

The `Runtime/ProtocolMachine/Model/` directory contains runtime data types, config, state, instruction forms, and event surfaces. The `Runtime/ProtocolMachine/Semantics/` directory contains executable step semantics. The `Runtime/ProtocolMachine/Runtime/` directory contains runtime adapters for loading, JSON, monitoring, and failure ingress.

The `Runtime/ProtocolMachine/API.lean` file provides the stable facade for executable protocol-machine API imports. The `Runtime/ProtocolMachine/Composition.lean` file contains composition/admission and theorem-pack integration surfaces. The `Runtime/Proofs/` directory contains proof/theorem-pack modules not required for core executable stepping.

Executable modules must not depend on placeholder proof definitions. Proof-only placeholders stay isolated under proof modules. Any executable-path dependency on a stub or placeholder is a release blocker.

## Deviation Governance

Any intentional parity break must be recorded in the deviation table below before merge.
Required fields include id, owner, status, reason, impact, alternatives considered, revisit date, and coverage scope.

### Deviation Registry (Active)

| ID | Status | Owner | Revisit | Summary |
|----|--------|-------|---------|---------|
| _none_ | _n/a_ | _n/a_ | _n/a_ | No active parity deviations |

Resolved deviations move to history after one stable release cycle with no regressions on the covered surfaces.

### Resolved Deviation History

| ID | Status | Owner | Moved On | Summary |
|----|--------|-------|----------|---------|
| threaded-round-extension | resolved | protocol-machine-runtime | 2026-02-27 | Threaded backend defaults to canonical one-step rounds |
| payload-hardening-extension | resolved | protocol-machine-runtime | 2026-02-27 | Lean and Rust now enforce payload-size admission on executable send/receive paths and strict-schema annotation rejection on annotationless send/receive shapes |
| comm-replay-label-context | resolved | protocol-machine-runtime | 2026-02-27 | Rust receive replay identity now canonicalizes to the Lean-style typed-context label token when session payload annotation is available |
| types-merge-payload-annotation | resolved | types-parity | 2026-02-27 | Lean canonical merge now enforces payload-annotation compatibility on overlapping send/recv labels and exposes matching soundness at the compatibility-gated entrypoint |
| types-content-id-closedness | resolved | types-parity | 2026-02-27 | Lean now exposes explicit closed-only canonical identity and open-term template identity policy surfaces with proofs matching Rust `content_id`/`template_id` contract |
| types-local-db-payload-retention | resolved | types-parity | 2026-02-27 | Lean payload-preserving DB conversion is promoted via parity surfaces with explicit success-equivalence bridge theorems to legacy erased conversion |
| theory-async-subtyping-conservative | resolved | theory-parity | 2026-02-27 | Lean and Rust both expose conservative executable async-subtyping with cross-validation tests |
| theory-orphan-free-conservative | resolved | theory-parity | 2026-02-27 | Lean and Rust both expose conservative executable orphan-freedom with cross-validation tests |

### Deviation Details (Active)

### Resolved Deviation Notes

#### threaded-round-extension

**Lean:** `Runtime/ProtocolMachine/Runtime/Runner.lean`
**Rust:** `rust/machine/src/threaded.rs`

**Resolution:** `ProtocolMachineConfig` exposes `threaded_round_semantics` and defaults to canonical one-step semantics aligned with Lean.

**Covers:** `threaded.round.wave.parallelism`

#### payload-hardening-extension

**Lean:** `lean/Runtime/ProtocolMachine/Model/Config.lean`, `lean/Runtime/ProtocolMachine/Semantics/ExecComm.lean`
**Rust:** `rust/machine/src/engine/`, `rust/machine/src/threaded.rs`, `rust/machine/tests/parity_fixtures_v2.rs`

**Resolution:** Lean and Rust both expose executable payload-size admission controls. Lean now emits strict-schema annotation rejection on annotationless single-branch send/receive shapes. Parity fixtures cover oversized payload rejection behavior at canonical concurrency.

**Covers:** `runtime.payload.admission`, `runtime.payload.size_bound`, `runtime.payload.strict_schema`

#### comm-replay-label-context

**Lean:** `Runtime/ProtocolMachine/Semantics/ExecComm.lean`, `Runtime/ProtocolMachine/Model/State.lean`
**Rust:** `rust/machine/src/engine/instruction_effects.rs`, `rust/machine/src/threaded/instructions_send_recv.rs`, `rust/machine/src/communication_replay/identity.rs`

**Resolution:** Rust receive replay identity now canonicalizes to typed-context replay labels (`recv:<ValType>`) when expected payload annotations are present, matching Lean receive identity construction.

**Covers:** `comm.replay.identity.label_context`

#### types-merge-payload-annotation

**Lean:** `lean/Choreography/Projection/Erasure/Merge.lean`, `lean/Choreography/Projection/Erasure/PayloadCompat.lean`, `lean/Choreography/Projection/Erasure/MergeSoundness.lean`
**Rust:** `rust/types/src/merge.rs`

**Resolution:** Lean `merge` is now compatibility-gated directly via `payloadAnnotationsCompatible`. `mergeWithPayloadCompat` is a stable alias to canonical `merge`. `merge_with_payload_compat_sound` proves soundness at the compatibility-gated entrypoint.

**Covers:** `types.merge.payload_annotation.compatibility`

#### types-content-id-closedness

**Lean:** `lean/SessionTypes/ContentIdentityPolicy.lean`
**Rust:** `rust/types/src/contentable.rs`

**Resolution:** Lean now exposes executable closed-only canonical identity surfaces (`globalToCanonicalIdentityBytes?`, `localToCanonicalIdentityBytes?`) and open-term template identity surfaces (`globalToTemplateIdentityBytes`, `localToTemplateIdentityBytes`). Proofs show that canonical identity is admitted iff terms are closed/all-bound.

**Covers:** `types.content_id.closed_only`

#### types-local-db-payload-retention

**Lean:** `lean/SessionTypes/LocalTypeDB/Annotated.lean`, `lean/SessionTypes/LocalTypeConv.lean`, `lean/SessionTypes/LocalTypeConvProofs/PayloadParityBridge.lean`
**Rust:** `rust/types/src/de_bruijn.rs`, `rust/types/src/contentable.rs`

**Resolution:** Lean `LocalTypeDBAnn` is promoted via parity-facing conversion surfaces (`toDBParity?`, `fromDBParity`, `toDBParity_closed_safe`). Bridge theorems prove success/failure equivalence between payload-preserving and legacy erased conversion (`to_db_ann_is_some_eq_to_db_is_some`). Lift witnesses from erased-success to payload-preserving success are provided by `to_db_lifts_to_db_ann`.

**Covers:** `types.local_db.payload_annotation.retention`

#### theory-async-subtyping-conservative

**Lean:** `lean/SessionTypes/LocalTypeR/AsyncSubtype.lean`, `lean/Choreography/Projection/Validator.lean`
**Rust:** `rust/theory/src/subtyping/async.rs`, `rust/bridge/src/runner_projection_export.rs`

**Resolution:** Lean and Rust now expose matching conservative executable async-subtyping with parity tests.

**Covers:** `theory.async_subtyping.conservative_subset`

#### theory-orphan-free-conservative

**Lean:** `lean/SessionTypes/LocalTypeR/AsyncSubtype.lean`, `lean/Choreography/Projection/Validator.lean`
**Rust:** `rust/theory/src/subtyping/async.rs`, `rust/bridge/src/runner_projection_export.rs`

**Resolution:** Lean and Rust now expose matching conservative executable orphan-freedom with parity tests.

**Covers:** `theory.orphan_free.conservative_local_check`

#### conservative-async-subtyping-contract

Conservative async-subtyping (Lean and Rust) is intentionally phase- and tree-structural:

- SISO decomposition must succeed on both sides under bounded unfolding.
- Subtype and supertype must have equal phase counts.
- Each aligned phase must satisfy input-tree and output-tree structural compatibility.
- Empty behavior (`End`) only matches supertypes with empty phase decomposition under this conservative contract.

## CI Gates

The minimum parity governance gates are `just check-parity --all`, `just check-release-conformance`, and workflow gates in `.github/workflows/verify.yml` and `.github/workflows/check.yml`.

If any gate fails, parity drift is treated as a release blocker.

## Performance SLA

Runtime performance governance enforces explicit thresholds from `artifacts/v2/benchmark_matrix/summary.json` through `just perf-baseline sla`.

- `TT_SLA_THROUGHPUT_RATIO_MIN` (default `1.0`)
- `TT_SLA_P99_REGRESSION_MAX_PERCENT` (default `15.0`)
- `TT_SLA_LOCK_CONTENTION_REDUCTION_MIN_PERCENT` (default `50.0`)

If any threshold is violated, CI fails before benchmark lanes are considered healthy.

## Update Rules

When any parity matrix row changes, update the Deviation Registry table in this file in the same change set. For any protocol-machine PR that changes public runtime behavior, include a parity impact statement in the PR checklist. Add differential tests when observable behavior changes.

Any Rust PR that changes projection or merge semantics must include:

1. The affected Rust module list.
2. The Lean module list reviewed for parity.
3. New or updated cross-validation tests for the changed behavior.
4. A parity note update in this document when scope or status changes.

## Type-Level Parity Checklist

Every Rust PR that changes type semantics must include this checklist in the PR description.

1. List affected Rust modules under `rust/types/src/`.
2. List corresponding Lean modules reviewed for parity.
3. State whether behavior is aligned or intentionally divergent.
4. If divergent, add or update a Deviation Registry entry in this document.
5. Link tests that cover new behavior and edge cases.

## Naming Surface

Rust protocol-machine code uses one canonical snake_case naming surface. Lean-specific casing remains on the Lean side. Rust APIs should not preserve parallel wrapper names such as `openDelta`, `siteName`, or `signValue`.

### Semantic Object Name Parity

Shared semantic/runtime objects keep the same PascalCase type name in Lean and Rust.
Field names may differ only by language casing convention: Lean uses `camelCase`, Rust uses `snake_case`.
Proof-only Lean packaging objects and Rust-only operational wrappers are listed separately and are not parity targets.

Lean source of truth:
[lean/Runtime/ProtocolMachine/Model/SemanticObjects/Core.lean](../lean/Runtime/ProtocolMachine/Model/SemanticObjects/Core.lean)

Rust source of truth:
[rust/machine/src/semantic_objects.rs](../rust/machine/src/semantic_objects.rs)

| Shared object | Lean | Rust | Status |
|---|---|---|---|
| Operation instance | `OperationInstance` | `OperationInstance` | Exact name match |
| Outstanding effect | `OutstandingEffect` | `OutstandingEffect` | Exact name match |
| Semantic handoff | `SemanticHandoff` | `SemanticHandoff` | Exact name match |
| Transformation obligation | `TransformationObligation` | `TransformationObligation` | Exact name match |
| Authoritative read | `AuthoritativeRead` | `AuthoritativeRead` | Exact name match |
| Observed read | `ObservedRead` | `ObservedRead` | Exact name match |
| Materialization proof | `MaterializationProof` | `MaterializationProof` | Exact name match |
| Canonical handle | `CanonicalHandle` | `CanonicalHandle` | Exact name match |
| Publication event | `PublicationEvent` | `PublicationEvent` | Exact name match |
| Progress contract | `ProgressContract` | `ProgressContract` | Exact name match |
| Progress transition | `ProgressTransition` | `ProgressTransition` | Exact name match |
| Semantic object bundle | `ProtocolMachineSemanticObjects` | `ProtocolMachineSemanticObjects` | Exact name match |

| Shared enum | Lean | Rust | Status |
|---|---|---|---|
| Operation phase | `OperationPhase` | `OperationPhase` | Exact name match |
| Outstanding effect status | `OutstandingEffectStatus` | `OutstandingEffectStatus` | Exact name match |
| Authoritative read kind | `AuthoritativeReadKind` | `AuthoritativeReadKind` | Exact name match |
| Authoritative read lifecycle | `AuthoritativeReadLifecycle` | `AuthoritativeReadLifecycle` | Exact name match |
| Canonical handle kind | `CanonicalHandleKind` | `CanonicalHandleKind` | Exact name match |
| Publication observer class | `PublicationObserverClass` | `PublicationObserverClass` | Exact name match |
| Publication status | `PublicationStatus` | `PublicationStatus` | Exact name match |
| Progress state | `ProgressState` | `ProgressState` | Exact name match |
| Ownership scope | `OwnershipScope` | `OwnershipScope` | Exact name match |
| Delegation status | `DelegationStatus` | `DelegationStatus` | Exact name match |

Representative field casing mappings:

| Lean field | Rust field |
|---|---|
| `operationId` | `operation_id` |
| `ownerId` | `owner_id` |
| `effectIds` | `effect_ids` |
| `terminalPublication` | `terminal_publication` |
| `publicationId` | `publication_id` |
| `observerClass` | `observer_class` |
| `lastProgressTick` | `last_progress_tick` |

### Lean-Only Proof Packaging Names

These are canonical Lean proof/runtime packaging objects not expected to have direct Rust runtime peers.

`ProtocolMachineInvariantSpace`, `ProtocolMachineTheoremPack`, `ProtocolMachineRuntimeContracts`, `ProtocolMachineLivenessBundle`, `ProtocolMachineSchedulerBundle`, `ProtocolMachineEnvelopeAdherenceProtocol`, `ProtocolMachineEnvelopeAdmissionProtocol`, `ProtocolMachineBridgePremises`, `CoroutineViewEquiv`, `protocolMachinePotential`.

### Rust-Only Operational Wrapper Names

These are canonical Rust operational or embedding surfaces not expected to have direct Lean theorem peers.

`GuestRuntime`, `ThreadedGuestRuntime`, `EffectHandler`, `ProtocolMachine`, `ProtocolMachineConfig`, `ProtocolMachineState`, `ProtocolMachineError`, `ProtocolMachineRunner`, `ProtocolMachineRunInput`, `ProtocolMachineRunOutput`, `ProtocolMachineReplayBundle`, `GuestRuntimeDeclaration`.

### Name Parity Maintenance Rule

When a shared semantic/runtime object is added, renamed, split, or removed:

1. Update the Lean definition in `lean/Runtime/ProtocolMachine/Model/SemanticObjects/Core.lean`.
2. Update the Rust definition in `rust/machine/src/semantic_objects.rs`.
3. Update the bridge re-export surface in `rust/bridge/src/semantic_objects.rs`.
4. Update this parity inventory in the same change.

## Related Docs

- [Protocol Machine Architecture](401_protocol_machine_architecture.md)
- [Protocol-Machine Bytecode Instructions](402_bytecode_instructions.md)
- [Lean Verification](801_lean_verification.md)
- [Capability Admission](702_capability_admission.md)
