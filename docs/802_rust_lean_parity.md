| rust-communication-hash-model | telltale-machine runtime maintainers | Active, runtime-only | Lean models communication nullifiers and replay roots as injective `reprStr` preimages; Rust digests the same preimage with the configured `HashModel` | Hash choice changes digest bytes only, not acceptance: both sides reject exactly the repeated preimages for the selected `CommunicationNullifierIdentity`; default model digests are unchanged | Modeling a concrete hash in Lean would add a collision assumption without strengthening the replay contract | 2027-04-08 | Rust unit and engine regressions cover default digest stability, custom-model determinism, content-only duplicate rejection and fail-closed deserialization; Lean runtime tests 41a and 41b cover both identity scopes |
| `CommunicationNullifierIdentity` variants (`sequence_bound`, `content_only`) | `Runtime/ProtocolMachine/Model/Config.lean`, `Runtime/ProtocolMachine/Model/State.lean` | `rust/machine/src/communication_replay/identity.rs` | Aligned |
# Rust-Lean Bridge and Parity

This document defines the typed Rust<->Lean bridge surface and the parity contract enforced across that boundary for protocol-machine behavior, choreography projection, semantic-object schemas, and deviation governance.

## Contract Levels

Parity is enforced at two levels. Level 1 covers policy and data shape parity for shared runtime encodings. Level 2 covers behavior parity for executable traces under the declared concurrency envelope.

## Bridge Scope

The `telltale-bridge` crate is the typed boundary between Rust artifacts and Lean validation entrypoints.
It handles JSON conversion, schema versioning, runner invocation, trace comparison, semantic-object export, and typed invariant bundle export.

The bridge does not define protocol-machine semantics.
Semantics remain in `telltale-machine`, `telltale-theory`, and Lean runtime modules.
Host-runtime handlers also remain outside the bridge and re-enter through typed effect surfaces.

The same reduced-fixture parity style  also applies to `telltale-search` for
the concurrency-critical slice. That lane covers:

- canonical min-key batch extraction
- proposal independence over declared authority surfaces
- replay epoch and phase contracts
- epoch-barrier transitions
- fairness-bundle fixture alignment

It is intentionally reduced. It does not attempt to prove full ARA* optimality
or every scheduler policy.

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
It loads the published heap parity corpus and returns typed `HeapParityOutput` values for strict Rust<->Lean comparison.

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
| `FlowPolicy` variants | `Runtime/ProtocolMachine/Model/Kledge.lean` | `rust/machine/src/engine/` | Aligned |
| `FlowPredicate` variants | `Runtime/ProtocolMachine/Model/Kledge.lean` | `rust/machine/src/engine/` | Aligned |
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
| Host targeted retirement | Cooperative and threaded disposal share the required retirement contract; Lean host-lifecycle deviation is recorded as `rust-host-targeted-disposal` |

These checks are automated by `just check-parity --suite`.

Explicit failure, timeout, cancellation, and session-terminal events are part of the executable Lean runtime/event inventory.
Replay tagging, JSON serialization, and theorem-pack release conformance all use the same observable event family.

Language-level nominal `effect` declarations do not introduce a second runtime bridge.
Their intended justification remains the existing protocol-machine `invoke` boundary and handler-typing obligations in `Runtime/Proofs/protocol machine/BridgeStrengthening.lean`.

Typed effect requests and outcomes are part of the parity surface directly.
Rust and Lean must agree on effect-interface metadata, request bodies, outcome statuses, and replay-visible effect exchanges.
Thatincludes the internal `wal_sync` effect metadata and the shared durable recovery vocabulary used to classify checkpoint-plus-WAL resume decisions.

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

The durability layer is  part of the documented Rust<->Lean correspondence boundary for runtime effects.

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

The runtime heap  has a focused Lean mirror for the parts of the contract that must remain cross-implementation stable.

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
`rust/runtime/tests/data/heap_lean_parity_v1.json` is the richer Rust<->Lean parity corpus.

### Heap Enforcement

The Lean heap surface is split into three files:

| Surface | Location |
|---|---|
| Executable heap model | `lean/Runtime/Resources/HeapModel.lean` |
| Basic determinism lemmas | `lean/Runtime/Proofs/Heap.lean` |
| Executable parity runner | `lean/Runtime/Tests/HeapParityRunner.lean` |

The strict Rust<->Lean heap suite is `rust/bridge/tests/heap_lean_parity.rs`.
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

The same strict bridge layer also compares the first-class
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

`Region` is  part of the canonical protocol-machine semantic-object family.
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

`CoroutineState` contains `id`, `programId`, `pc`, `regs`, `status`, `effectCtx`, `ownedEndpoints`, `progressTokens`, `kledgeSet`, `costBudget`, and `specState`.

The Lean protocol-machine state structure (`ProtocolMachineState`) contains `config`, `programs`, `coroutines`, `sessions`, `monitor`, `sched`, `resourceStates`, `persistent`, `obsTrace`, failure/topology state fields, and output-condition state.

### Rust Protocol Machine

Source: `rust/machine/src/engine/`

The Rust protocol-machine structure (`ProtocolMachine`, exported as an alias for `protocol machine`) contains `config`, `programs`, `code`, `coroutines`, `sessions`, `monitor`, `sched`, `resource_states`, `persistent`, `obs_trace`, symbol/clock counters, failure/topology state fields, and output-condition state.

`Coroutine` in `rust/machine/src/coroutine.rs` contains identity/program/pc/status, register file, ownership/progress/kledge sets, cost budget, speculation metadata, and effect context.

### Canonical Rust Runtime Object Inventory

The Rust public runtime surface  exposes one canonical naming scheme:
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
The mirror  includes a Lean-native field-model boundary in `lean/Runtime/Simulation/Field.lean`, including built-in catalog dispatch and default initial-state derivation for shipped field families.
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

### Deviation Registry

| Id | Owner | Status | Reason | Impact | Alternatives considered | Revisit date | Coverage scope |
|---|---|---|---|---|---|---|---|
| rust-host-targeted-disposal | telltale-machine runtime maintainers | Active, runtime-only | Exclusive host disposal and scoped Rayon worker acknowledgment concern Rust execution custody outside the Lean small-step program | Adds targeted retirement APIs and typed preflight errors; no shared wire schema, instruction or capability shape changes; host retirement does not establish protocol success | Status-only close leaves runnable custody; whole-machine drop removes unrelated sessions | 2027-01-03 | Cooperative and threaded required-reap regressions cover surviving stable ids, actual worker acknowledgment, preflight faults, natural terminal epochs, repeated acknowledgment and cooperative deserialization; cross-backend disposal summary regression covers the common retirement contract |
| rust-host-worker-pool-error-source | telltale-machine runtime maintainers | Active, runtime-only | Native worker construction and its original I/O cause are outside Lean protocol state and small-step execution | ThreadPoolBuild retains the actual Rayon error chain; diagnostic display is unchanged; no instruction, capability, wire format or successful protocol trace changes; constructor refusal supplies no worker-termination ACK | Stringifying native causes or treating constructor failure and pool Drop as acknowledged teardown | 2027-01-20 | Two native multi-thread fixtures declare first-spawn refusal and later-spawn refusal after an actual first-worker acknowledgment; the latter retains and joins original native handles before assertions; these tests do not establish production pool-join capability |
| rust-host-owned-session-parity | telltale-machine runtime maintainers | Active, runtime-only | Host session mutation, staged ownership receipt validation and original Rust error sources are embedding contracts outside endpoint/coroutine small-step transfer | Both backends share resident-state ownership transitions; owned handles validate receipt/session association and current generation; transfer/attenuation cannot widen scope; release/reclaim generations remain monotonic; exhausted counters fail before mutation; the canonical journal preserves actual cross-session emission order and machine ticks across disposal; cooperative snapshots add a defaulted ordered journal and last-generation storage; OwnershipContract carries a typed source | Duplicated threaded ownership logic, bare-store mutation, saturating/reused authority ids, stringified causes, or reconstructing authority from audit records | 2027-01-19 | owned_backend_parity exercises both backends, claim-specific failed commit/rollback, foreign receipt refusal, witness consumption/rejection, stale and scoped handles, terminal ordering, typed causes and retained audit; ownership_preflight_tests covers release/reclaim restoration, scope escalation, counter exhaustion before terminal mutation and foreign edges; ownership_lock_tests exercises the original poisoned custody and audit locks before mutation |

The Lean `Runtime/ProtocolMachine/Model/State.lean` session state and
`Runtime/ProtocolMachine/Semantics/ExecSteps.lean` execution surfaces remain the
reference for protocol steps. Targeted host disposal is not a new instruction,
transition witness, or claim that Lean proves Rayon worker termination. Rust's
exclusive owner and joined worker scope enforce that runtime obligation.

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

## Related Docs

- [Protocol Machine Architecture](401_protocol_machine_architecture.md)
- [Protocol-Machine Bytecode Instructions](402_bytecode_instructions.md)
- [Lean Verification](801_lean_verification.md)
- [Capability Admission](702_capability_admission.md)

## Native worker-pool settlement deviation

The Rust-only private worker-pool disposal API concerns real host thread custody,
not a Lean instruction, session status, capability witness or machine-tick
transition. Its opaque receipt is issued from actual native JoinHandle results.
It cannot reconstruct protocol authority or certify signed-terminal success.

Native join-operation unwind is distinct from a worker panic returned by a
completed join. The original native custodian retains untouched handles,
completed-join counts and chronological causes across that unwind. A consumed
handle with unproven settlement permanently prevents whole-pool acknowledgment,
even after same-original retry joins every remaining worker. This repairs host
custody rather than adding a Lean instruction or protocol authority witness.
Injected join-boundary tests establish this retention transaction, not an actual
OS deadlock diagnosis or physical settlement of an uncertain consumed handle.

| Id | Owner | Status | Reason | Impact | Alternatives considered | Revisit date | Coverage scope |
|---|---|---|---|---|---|---|---|
| rust-host-native-pool-settlement | telltale-machine runtime maintainers | Active, runtime-only | Native worker exit and join are outside Lean protocol small-step state | Consuming explicit machine teardown joins original workers; partial construction retains actual worker handles and Rayon source; no instruction, wire or successful trace change | Rayon Drop and targeted session receipt do not acknowledge private native-pool termination | 2027-01-20 | Eleven native source-declared component fixtures cover real worker TLS exit before ACK, original panic payload, actual machine pool, first spawn refusal and partial start followed by original joins, actual self-worker refusal returning the machine for external retry, join-operation unwind retaining untouched original workers and chronological causes, retained consumed-worker refusal after unwind, and observation during actual pending join; execution evidence remains required |

## Authority Binding Artifact Boundary

The communication-only theory artifact route cannot certify execution of an
AST authority binding. It now rejects authority/observation modes, explicit
check/observe/transfer expressions, linear aliases and unclassified calls rather
than erasing those operations. Plain non-linear identifiers and constructors
remain local communication abstractions. Their projection is not a value
interpreter or authority witness.

The existing authority semantic-object conservation and supported-slice Lean
theorems remain unchanged. They do not prove that the DSL compiler emitted an
Invoke, passed the original nominal effect request, preserved typed outcome
branching or bound a continuation to the issued owner. Those compiler and
execution correspondence obligations remain open. A positive communication
machine run and an explicit authority-artifact refusal are separate evidence.

In the current producer, a named Invoke action is recorded as action metadata,
but step_invoke still submits the generic invokeStep request with role and
register state. Renaming that action to a declared effect operation would not
invoke that operation. Lean's corresponding invokeStep request has the same
role/state boundary. A nominal request/typed-outcome and continuation contract
must be established at this shared boundary before claiming positive lowering.

## Typed Outcome Acceptance Prerequisite

The Rust outcome adapters now separate raw status from accepted success. The
same exact request/response-kind rule controls register updates, lifecycle
publication and effect-composition success on cooperative and threaded paths.
Recording and replay state adapters consume their actual returned outcome. They
do not recover a state payload by rereading the latest shared trace entry.

The pinned release19 Lean model has eight request/response families, while Rust
also has WalSync as a ninth family. The new pure acceptedStatusFor and
invokeStepState helpers cover the actual eight modeled families. Their examples
are not an execution correspondence proof. Existing EffectAlgebra.succeeded
still classifies raw status, and ExecGuardEffect.stepInvoke executes the abstract
total EffectRuntime.exec without a typed outcome gate. Connecting those premises
to accepted typed outcomes, updating composition proofs and modeling WalSync are
open correspondence prerequisites. The earlier durability alignment description
must not be read as proof that the pinned request enum already contains WalSync.

Full nominal dispatch also remains open: the original declaration and uses
admission, argument/result types, actual coroutine role and owner generation,
result destination and success/failure continuation must be bound to one issued
invocation. Late or duplicate completion must target that same live occurrence.
No named audit string, post-hoc owner lookup or new side ledger establishes this
contract. Host physical future and worker custody remain the embedding owner's
separate responsibility.

VM Invoke and Receive requests retain their actual configured register width as
optional instruction context. All VM state-replacing responses, including branch
Choose/Receive, must preserve that width before register replacement or effect-
success publication. This enforces the canonical Rust `wf_coroutine_state`
register-width invariant, not an inferred equal-length convention. Receive also
retains its actual destination and requires that register to exist. Branch receive
omits the destination because it performs no destination write, but retains width.
Handler-only wrappers omit both instruction contexts. Missing fields on older
serialized requests decode as absent and do not invent historical VM context. The original raw outcome remains observational evidence. This check
is not rollback of earlier buffer dequeue, replay consumption, clock or type work.
Optional observability retention cannot replace an original host failure: the
canonical recorded exchange supplies lifecycle status without a second synthetic
issue/complete cycle. Blocked remains a Blocked observation while the synchronous
instruction reports its existing blocked-contract fault.
The Lean request schema does not yet carry instruction width/destination context.
Its pure family/status examples do not prove this Rust applicability rule. That
schema and executable-semantics correspondence remain an explicit prerequisite.

Host-response acceptance is distinct from whole-instruction commit. In particular,
Invoke may apply its accepted register state and host-success observation before
persistence-delta application faults. No rollback of that state, emitted events,
or earlier communication work is implied by the response-kind/destination guard.
The prior cooperative owner could evict live enforcement inputs under diagnostic
retention, while the prior threaded owner used untrimmed vectors. The canonical
live/resident retention rule below repairs that storage boundary in both existing
owners. Response/error preservation alone was insufficient. Neither correction
claims nominal authority, a disposal acknowledgment or a Lean correspondence proof.

Serialized request context is an observation used to validate response shape, not
proof of original request ownership or nominal authority. The replay handler
selects by expected entry kind. It does not establish full incoming request
identity. Actual VM producers attach current configured width before execution,
including when replay supplies the response. Lean's abstract effect-context step
and spawn register copying are not a proof of this concrete Rust register ABI.

Canonical host exchanges also supply Acquire/Release/SendDecision outcome
observations directly. Duplicate synthetic issue/complete cycles must not replace
the original typed failure under optional diagnostic retention. Existing policy
is preserved: cooperative Acquire Blocked waits on AcquireDenied, threaded Acquire
Blocked reports its synchronous blocked-contract fault, and Release/SendDecision
Blocked remain synchronous faults. The separate Send buffer WouldBlock producer
retains its actual live capacity obligation: successful host decision is not queue
admission, so that issue/complete pair is not a duplicate host outcome.

## Canonical Live Effect Retention

Cooperative and threaded owners retain active effect, operation and progress
records independently of Disabled/Capped diagnostic history. Both use the same
live/resident classification and retired terminal-history pruning rule. Actual blocked Acquire
and next-round topology producers must retain the original owner/budget and
progress/reentrancy enforcement. Targeted disposal permits terminal history to
obey its configured bound. The pre-existing instruction policy for Blocked
Acquire still differs (cooperative blocks, threaded faults). Paired retention
fixtures do not claim that wider behavior is equivalent.

Lean progress/reentrancy predicates concern retained semantic objects and their
actual steps. They do not authorize observational eviction of an uncompleted
operation. This Rust retention repair does not add a Rust/Lean correspondence
proof, capture arbitrary asynchronous work, or equate invalidation with physical
teardown. New fixture declarations require actual discovery and execution.

The original terminal-only retention child was insufficient: actual
current_wal_sync_request consumes terminal operation/publication records through
semantic_objects. Both backends now additionally protect every canonical record
of an actually resident session. Terminal history eligibility starts only after
actual session retirement. A terminal lifecycle status is not proof of
nonresidency or irrelevance. A shared real Invoke/commit/WalSync fixture compares
the exact handler request, agreement state and evidence under all three modes.
Full correspondence and physical teardown remain separate obligations.

The composed required native ownership/disposal inventory contains 59 unique
fixtures: the original 35 plus 17 strict-outcome/error, six live/resident retention
and one cooperative full-queue/Disabled regression. The existing canonical checker
requires their nonignored declarations, actual harness discovery and successful
execution. Declarations alone are not passing evidence. Module filters can also
execute required fixtures appearing in a narrower sub-suite, without changing the
unique required count. Authority guard DSL/compiler/bridge fixtures and formal
examples remain separate targets and obligations.

## Explicit Placement Source Representation

The optional `Protocol::Let.execution_role` field preserves an explicit `at Role`
clause through parsing, clone and continuation append. AST Protocol is not a
serde wire type: no CodeImage or effect trace schema changes here. Existing Rust
literal constructors now explicitly supply None. This is a Rust source migration,
not an implicit role reconstruction. Legacy DSL forms remain unplaced.

Lean LocalTypeR contains communication and recursion only. CompileLocalTypeR
cannot preserve a local typed authority binding. EffectRuntime.exec remains a
total action/context transition. StepInvoke checks handler presence but has no
nominal operation/generation/result-continuation transaction. Therefore no new
Lean constructor, execution theorem or parity claim follows from source placement.
The placed artifact refusal is deliberate until the actual shared model and
Rust executable producers implement that transaction. Direct local
projection of unplaced local expressions remains communication analysis, not
proof that those expressions execute. This child does not change that existing
analysis contract or classify its result as executable authority lowering.

## Nominal Command Transaction Prerequisite

The Rust selected-operation compiler produces a static nominal declaration and
call plus existing communication continuations. The owned loader retains the
issued OwnedSession in coroutine custody. Serde deliberately omits that handle
and the live result continuation. Static descriptors, effect traces and restored
ownership metadata do not reconstruct it. A source-selected agreement profile
is explicit on the existing OperationInstance. Legacy instances deserialize to
None and retain their previous derivation rules.

Both Rust backends issue the canonical outstanding effect, operation and progress
owner before the callback. The threaded path performs issuance before worker
dispatch, retains the actual continuation on the original coroutine, and gates
the main-thread result commit after the worker returns. The raw exchange remains
separate from accepted status. Immediate Blocked is refused. MayBlock retains
the selected original budget. Admission and commit use the inclusive original
issued tick plus budget. Progress escalation never extends that endpoint.
Semantic handler identity is observed before admission and once at final commit,
with no subsequent identity callback after derived success publication. It is
not proof of a physical provider identity or native-future settlement.

The executable Lean path uses typed action classifiers and `invokeCommand`,
with the original typed action supplied to sum composition. The default callback
refuses. Parsing/classification alone never falls through to generic `exec`.
Products retain nominal classification but have no admitted result-combination
contract, so their default nominal callback/relocation refuses. Legacy models
with no nominal classifiers keep the existing generic path.

The model's canonical coroutine, outstanding-effect, operation and progress
fields retain the same nominal occurrence through Blocked and output refusal.
The original typed exchange is an observation. A returned value is held before
post-callback validation. Output refusal retains that holder instead of rolling
back to the pre-issuance state. Exact logical-window, ordering preservation and
typed-branch commit theorem declarations accompany real loader/opcode/commit
fixtures. These source declarations require actual Lean checking. They are not
a completed Rust/compiler refinement theorem.

Canonical Halt keeps the program counter at the actual terminal instruction
while marking the coroutine done and removing its active endpoint type. Both
Rust backends and the executable Lean transition use this same terminal PC.
The pending nominal bridge case runs through declaration, the peer's blocked
choice, and the first invocation at logical tick three. It checks that actual
original occurrence and its selected budget before testing retained authority.
This does not change the scheduler clock or extend the original window.

Role entry PCs in Lean need not be zero. Static declarations apply only to the
prefix of the actual role's executable chunk, and the loader fixes that role on
the original coroutine. A declaration is a static manifest, not an executed
capability grant. Typed result branches must stay in that chunk. Converting an
executable image to a role map now slices and rebases its actual instructions.
It never recompiles local communication types and discards nominal actions.
Typed action relocation must preserve the exact rebased descriptor or refuse.
Missing/lying adapters and cross-role targets have negative fixture declarations.

Rust's issued `OwnedSession` and generation checks remain the additional host
boundary described by `rust-host-owned-session-parity`. Lean endpoint/occurrence
records do not reconstruct that handle or prove physical host cleanup. The
source compiler, both backend fixtures and executable Lean relation are still
uncompiled/unexecuted in this prepared child. Full source-to-model refinement,
authoritative evidence/readiness, publication, materialization and transfer
lowering remain required and open. No broader authority proof follows from this
Command application-result slice.

### Executable nominal bridge scope

The existing protocol-machine runner has a separate `runNominalImage` operation.
It installs the source compiler's actual tagged instructions through the checked
role-image loader. Missing bytecode or typed outcomes cannot fall back to local
communication-type recompilation. The legacy communication operation remains
communication-only. The targeted Lean prerequisite builds this runner module and
its nominal model fixtures explicitly before `lean --run` imports them.

The comparison retains actual application outcomes, accepted statuses, semantic
fault payloads, issuance and callback-observation ticks, operation/profile/proof
requirements, registers, PCs, and readonly observations of the original pending
continuation, staged result and independent refusal. These observations contain
no `OwnedSession` and cannot restore authority. Unsupported typed responses and
terminal fault families refuse rather than becoming absent payloads.

The source-derived normalization ledger permits only the validated single
original occurrence-ID relation and an exact original-or-plus-one reply relation.
It does not equate arbitrary foreign IDs, normalize ticks, or erase retained
results. Explicit local payload annotations and unsupported instructions remain
outside this narrow image bridge and refuse. The fixture declarations include
actual Blocked and output-denied executions plus omitted-holder, changed-result,
changed-terminal-cause and foreign-ID controls. They require real Rust/Lean
execution. No source-only preparation counts as correspondence acceptance or a
full compiler-refinement theorem.

### Finite simulation-counter admission

Lean `Runtime/ProtocolMachine/Runtime/Runner.lean::runScheduled` and
`ThreadedRunner.lean::runScheduledThreaded` advance the model clock by one before
the round. Rust preserves that one-round increment over its representable domain.
Its `u64` tick and `Duration` are finite, unlike the mathematical model clock.
At either boundary, Rust returns a typed admission error before changing either
counter or entering the round. This refuses an unrepresentable execution. It
never saturates, wraps, advances per worker wave, or substitutes a physical clock.

| Id | Owner | Status | Reason | Impact | Alternatives considered | Revisit date | Coverage scope |
|---|---|---|---|---|---|---|---|
| rust-finite-simclock-admission | telltale-machine runtime maintainers | Active, finite representation boundary | Rust tick and simulated duration have finite successors while Lean model arithmetic is unbounded | Typed atomic refusal before round mutation; all representable rounds retain one tick each; no authority or cleanup ACK | Wrapping, saturation, panic or partial tick mutation changes the selected model time | 2027-01-21 | Three direct clock declarations and two actual-round declarations per backend; source-only until discovered and executed |

### Prepared readiness continuation and session authority state

The typed nominal result now distinguishes Boolean application values from
`ReadinessWitness` data. Both Rust backends use the existing canonical session
issuer/consumer and the retained original `OwnedSession`. The witness is consumed
only at gated commit. Lean adds owner/current-generation and issued/consumed
readiness state to the same canonical `SessionState`, with explicit model owner
admission and issuance independent of callback fields. The original model owner
is retained in the nominal continuation. Model data is not an issued Rust host
handle, and does not establish physical resource custody or asynchronous cleanup.

`Value` and `ValType` readiness cases are appended, preserving prior enum order.
Witness data keeps the original registry witness field order and scope shape.
The previously unreleased nominal reply uses an explicitly tagged typed result
(the Bool-only nominal draft shape is rejected). This is not claimed compatible
with old draft nominal JSON/binary artifacts. Released v19 has no nominal reply
surface. No canonical replay/trace v1 field or existing variant is reordered.
Original owner/continuation serde skips are unchanged: decoding a register or
witness never restores live authority. Both JSON and canonical binary roundtrips
and old value/type tags have declared regressions. Broad source-to-model bridge
normalization must explicitly handle the new typed result and cannot erase it.

New Rust and Lean cases are uncompiled/unexecuted source. No static proof of
physical custody, complete DSL authority lowering, or restoration follows.

The prepared existing compiled-image bridge uses `nominal_image.v2` for explicit
typed Boolean/readiness results and complete original owner/registry observations.
Admission input carries only an owner intent and an after-Blocked scheduling
choice. The actual original runtime/model session issues the witness between
rounds after a genuine Blocked occurrence. Transported witness fields cannot mint
authority. Commit uses the canonical store-owned audit adapter with the current
SimClock tick. Observations include genuine issue, consumption and rejection.
The single-original effect-id relation does not normalize witness ids, owner,
session, generation, predicate, callback ticks, ordering or completion ticks.

The canonical `OutstandingEffect.applyEvent` contract preserves the original
ordering key for blocked/completed/timeout/cancellation/invalidation transitions.
Only an explicit retry event replaces it. The prepared native producers now
preserve that key, retain no terminal completion for a Blocked transition, and
record the actual current tick for terminal settlement. Bridge output separates
original request issuance, ordering key and completion tick. The existing model
ordering-preservation theorem remains unchanged. This source correction and the
actual Blocked-to-later-success regressions still require execution.


### Prepared original source-operation correspondence

The existing compiled-image bridge now preserves typed Begin/Await/Resolve/
Invalidate opcodes and exact required-child manifests. It does not regenerate
these actions from communication projections. Both native backends retain the
same enclosing coroutine holder, distinct from the singleton `effect:id` child,
and the executable model uses the same canonical coroutine, session ownership,
operation, effect and progress fields. Every selected nominal call captures the
original coroutine-held model owner through the canonical owning-load admission.
Looking up the current registry owner is insufficient. Model owner data does not
prove Rust opaque-handle issuance or native resource custody.

Comparison includes the original enclosing declaration, admitted slots, actual
child outcome, proposed resolution, typed first execution failure and canonical
parent/progress records. The raw original parent id is retained. Its comparison
relation validates the actual role entry and installed original PC before
relating the role-local PC and derived occurrence id. It does not normalize
ticks, generations, policy, values or failures. Child ids follow the existing
validated single-original relation. Missing parent records or executable payload,
unknown response families and unsupported fault observations refuse comparison.
This is a prepared executable relation, not an elaborated compiler-refinement
theorem or full authority-language proof. Required Rust/Lean execution is open.
