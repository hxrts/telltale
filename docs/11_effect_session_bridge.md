# Effect Handlers and Session Types

This document defines the integration boundary between Telltale and a host runtime.
The boundary is the protocol-machine `EffectHandler` interface.
It is centered on typed `EffectRequest` and `EffectOutcome` values.

## Scope

Use this document when integrating Telltale into another execution environment.
Use [Choreography Effect Handlers](09_effect_handlers.md) when implementing async handlers for generated choreography code.

## Three-Layer Contract

Telltale uses three layers.

| Layer | Artifact | Role |
|---|---|---|
| Global protocol layer | choreography and projection | defines role-local protocol obligations |
| Effect layer | handler interfaces | defines runtime action behavior |
| Protocol-machine layer | bytecode and monitor checks | enforces instruction-level typing and admission rules |

Projection and runtime checks preserve obligations across these layers.

This document describes a host-runtime contract.
It is normative for Rust embedders. It is not itself a theorem statement.
The theorem-backed protocol properties remain in projection, coherence, and harmony.
The host ownership rules below are implementation contracts enforced by the protocol-machine boundary.

## Rust Handler Surfaces

Rust exposes two handler interfaces.

| Interface | Location | Purpose |
|---|---|---|
| `ChoreoHandler` | `rust/choreography/src/effects/handler.rs` | async typed API for generated choreography code |
| `EffectHandler` | `rust/vm/src/effect.rs` | sync protocol-machine API over bytecode values |

Third-party runtime integration should use `EffectHandler`.

## Why the Protocol-Machine Boundary

`EffectHandler` is synchronous.
This matches deterministic host execution models.
It avoids futures and runtime-specific scheduling inside handler calls.

`EffectHandler` operates on protocol-machine values and labels.
This keeps the wire and storage boundary host-defined.
It avoids coupling to generated Rust message types.

The protocol machine enforces session typing before and during execution.
The boundary keeps typing logic in Telltale.
It keeps host logic focused on effect interpretation.

## Canonical Ingress and Ownership

External host events must enter the protocol machine through canonical typed
effect requests.

| Typed ingress | Purpose | Ownership rule |
|---|---|---|
| `EffectRequestBody::TopologyEvents` | inject crash, partition, heal, corruption, and timeout events | must not mutate session-local host state directly |
| `EffectRequestBody::SendDecision` | compute outbound delivery behavior | may inspect request-local state only |
| `EffectRequestBody::Receive` | apply receive-side host effects | may mutate request-local state only |
| `EffectRequestBody::InvokeStep` | perform `Invoke`-scoped integration work | may mutate request-local state only |
| `EffectRequestBody::OutputConditionHint` | provide authoritative commit metadata for proof-bearing success and canonical handle issuance | must not be synthesized from observational snapshots |

Session-local host mutation outside these request-local values flows through an explicit ownership capability such as `OwnedSession`.
This is the host integration path for mutating edge traces, handler bindings, or other session-local host metadata.

Protocol-critical host decisions should also use explicit witnesses where available:

- readiness checks should issue and later consume a `ReadinessWitness`
- ownership-failure cancellation paths issue a `CancellationWitness`
- topology timeout ingress emits a `TimeoutWitness`

Host rules:

- `EffectHandler` methods are synchronous. Async work must happen outside request handling and feed results back through a later ingress call.
- Admission and ownership are distinct. Passing admission/runtime gates does not imply the caller is the current session owner.
- Ownership is generation-bearing. Reusing the same owner label after transfer does not preserve authority.
- Fragment-scoped capabilities do not imply full-session ingress rights.
- Stale owners fail closed with typed ownership diagnostics before host mutation is applied.

## Boundary Ownership

The boundary separates protocol semantics from host materialization.

| Concern | Protocol machine owns | Host `EffectHandler` owns |
|---|---|---|
| Session typing | Local type checks and continuation advancement | none |
| Buffer and signature discipline | enqueue, dequeue, and signature verification | none |
| Scheduler and commit | coroutine scheduling and atomic step commit | none |
| Send policy | call point and branch label context | `send_decision` return value |
| Receive side effects | receive timing and source payload | register and host state mutation in `handle_recv` |
| Invoke integration | when invoke runs | integration state mutation in `step` |
| Guard transitions | protocol-machine guard instruction flow | grant or block in `handle_acquire`, validation in `handle_release` |
| Topology metadata | event ingestion order and application | produced events in `topology_events` |
| Output metadata | commit-time query point | optional hint from `output_condition_hint` |

Additional ownership split:

| Concern | Protocol machine owns | Host runtime owns |
|---|---|---|
| current owner identity and generation | validation and stale-owner rejection | choosing owner labels and transfer policy |
| transfer receipts and rollback | staged transfer enforcement and audit artifacts | when to request transfer |
| session-local mutation gate | capability and scope checks | operations performed through `OwnedSession` |

## Typed Effect Boundary

The protocol-machine dispatch path is in `rust/vm/src/vm.rs`.
The trait surface is in `rust/vm/src/effect.rs`.
The normative contract is documented in that trait module.

| Surface | protocol-machine call point | Runtime behavior | Integration note |
|---|---|---|---|
| `handle_effect(EffectRequest)` | all host-facing instruction sites | one canonical request/outcome surface | new runtime code must use this path |
| `EffectRequest.metadata` | all request construction sites | carries `EffectInterfaceMetadata` fields: interface name, operation name, authority class, admissibility, totality, timeout, reentrancy, handler domain | validated before dispatch |
| `EffectRequestBody::SendDecision` | `step_send`, `step_offer` | called before enqueue | receives send context plus optional precomputed payload |
| `EffectRequestBody::Receive` | `step_recv`, `step_choose` | called after dequeue and verification | use for state updates and host-side effects |
| `EffectRequestBody::Choose` | trait helper / custom runners | branch-selection helper | not part of the canonical default dispatch path |
| `EffectRequestBody::InvokeStep` | `step_invoke` | called during `Invoke` instruction | use for integration steps and persistent deltas |
| `EffectRequestBody::Acquire` | `step_acquire` | grant, block, or fail acquire | return evidence in `EffectResponse::Acquire` |
| `EffectRequestBody::Release` | `step_release` | release validation | return `EffectOutcome::failure(...)` to reject invalid evidence |
| `EffectRequestBody::TopologyEvents` | `ingest_topology_events` | called once per scheduler tick | events are sorted by deterministic ordering key before apply |
| `EffectRequestBody::OutputConditionHint` | post-dispatch pre-commit | queried only when a step emits events | return `None` to use protocol-machine default |
| `handler_identity` | trace and commit attribution | stable handler id in traces | defaults to `DEFAULT_HANDLER_ID` when not overridden |

Helper-method compatibility notes:

- `handle_send` and `handle_choose` must not become hidden side channels for session metadata mutation.
- helper methods remain compatibility helpers for default `handle_effect` implementations. They are not separate ingress paths.
- Bridge traits in `rust/vm/src/bridge.rs` are deterministic lookup/projection surfaces, not mutation surfaces.
- Public host integrations open sessions through `load_choreography_owned(...)` and mutate session-local host metadata through `OwnedSession`.

## Typed Effect Outcomes

The protocol machine now uses a typed effect boundary.
`EffectHandler::handle_effect` returns an `EffectOutcome`.
Helper methods use typed `EffectResult<T>` rather than `Result<T, String>`.

| Outcome surface | Purpose |
|---|---|
| `EffectOutcome::success(EffectResponse)` | request completed successfully |
| `EffectOutcome::blocked()` / `EffectResult::Blocked` | request requested a clean scheduler-visible block |
| `EffectOutcome::failure(EffectFailure)` / `EffectResult::Failure(EffectFailure)` | request failed with typed diagnostics |
| `EffectFailureKind` | coarse failure taxonomy including denied, timeout, cancellation, stale authority, invalid evidence, unavailable, invalid input, determinism, topology disruption, and contract violation |

Host guidance:

- Use `Blocked` only for genuinely resumable conditions such as acquire deferral.
- Use `Failure` for typed terminal or policy-visible failures.
- Do not encode timeout, cancellation, or ownership failure in ad hoc strings when a specific `EffectFailureKind` exists.
- Replay, recording, bridge export, and effect-exchange serialization preserve these typed outcomes directly.

## Language-Declared Effect Invocation

The choreography language now has nominal `effect` declarations, protocol-level `uses` clauses, and `check Effect.op(...)` expressions.

```tell
effect Runtime
  ready : Session -> Result CommitError ReadyWitness

protocol CommitFlow uses Runtime =
  let readiness = check Runtime.ready(session)
  ...
```

Host-boundary rule:

- this does not create a second integration channel beside the protocol-machine effect layer
- language-declared effect operations still lower to the same typed protocol machine
  `invoke` boundary and handler-obligation model
- missing or ambiguous authority must surface as typed failure or explicit
  evidence rejection, never as fallback success

Operational consequence:

- embedders implement one typed host boundary in `EffectHandler`
- language-level authority checks become explicit effect observations and
  semantic-audit records once lowered into the protocol machine

## Authoritative Reads, Materialization, and Publication

The protocol machine now distinguishes observational reads from semantic-path
authoritative reads.

| Surface | Meaning |
|---|---|
| `ObservedRead` | handler/effect observation only. Must not authorize semantic truth. |
| `AuthoritativeRead` | witness-bearing semantic input accepted on parity-critical paths |
| `MaterializationProof` | proof-bearing success artifact derived from canonical output-condition checks |
| `CanonicalHandle` | strong runtime handle that later parity-critical paths must require |
| `PublicationEvent` | one sealed canonical publication path for lifecycle-visible semantic state |

Host-runtime rules:

- observational effect results must not be promoted into semantic truth
- proof-bearing success is mandatory when an operation declares `requires_proof`
- canonical publication is derived from sanctioned runtime state. Embedders must
  not bypass it with parallel publish helpers.
- parity-critical follow-on work should require a `CanonicalHandle`, not a weak
  id reconstructed from observational state

## Authority Witnesses

The ownership boundary now includes explicit witness objects for protocol-critical authority flow.

| Witness | Issued by | Consumed by | Purpose |
|---|---|---|---|
| `ReadinessWitness` | `SessionStore::issue_readiness_witness` or `OwnedSession::issue_readiness_witness` | `consume_readiness_witness` | prove a readiness/admission-style check under a specific live owner generation |
| `CancellationWitness` | owner death or abandoned-transfer handling | observational/audit surface | make cancellation-triggering ownership failure explicit |
| `TimeoutWitness` | topology timeout ingress | observational/audit surface | make timeout issuance explicit and replay-visible |

Readiness witnesses are generation-bound and single-use.
They fail closed if the owner becomes stale, scope attenuates, the witness is forged, or a second consume is attempted.
These runtime witnesses are the evidence objects that back language-level
authority checks and evidence-bearing branches after lowering.

## Integration Workflow

1. Use `telltale-theory` at setup time to project global types to local types.
2. Compile local types to protocol-machine bytecode and load with `CodeImage`.
3. Open sessions with `load_choreography_owned(...)` so the host authority boundary is explicit from the first step.
4. Implement `EffectHandler` with deterministic host operations.
5. Map each typed effect request to host primitives without reimplementing protocol typing.
6. Run `run_loaded_vm_record_replay_conformance` to validate record and replay behavior on a loaded VM.
7. Run Lean bridge lanes for parity and equivalence checks.

## Integration Tooling

Use `just effect-scaffold` to generate host integration stubs.
The command now reads DSL `effect` declarations and emits:

- `generated_effects.rs` with canonical Rust request/outcome enums and host-handler traits
- `generated_simulator.rs` with first-class simulator traits, state, and scenario builders
- `generated_effect_manifest.json` with the exported effect-family schema
- a local scaffold `README.md` with next-step instructions

```text
just effect-scaffold path/to/protocol.tell
```

This command writes files under `artifacts/effect_handler_scaffold` by default. The direct form is:

```text
cargo run -p effect-scaffold -- --out artifacts/effect_handler_scaffold --dsl path/to/protocol.tell
```

Use `--no-simulator` when you want only the Rust effect boundary without simulator artifacts.

Use `just sim-run <config>` to execute a simulator harness config file.
This command runs the protocol machine with scenario middleware and contract checks.
It is the fastest path for CI validation in third party host projects.

```text
just sim-run artifacts/sim_integration.toml
```

This command prints a JSON report. The process exits with code `2` when contract checks fail.

## Simulator Validation Lane

Use `telltale-simulator` harness types for integration tests.
`HarnessSpec` carries local types, global type, scenario, and optional initial states.
`SimulationHarness` runs the spec with one `HostAdapter`.

```rust
let adapter = DirectAdapter::new(&my_effect_handler);
let harness = SimulationHarness::new(&adapter);
let result = harness.run(&spec)?;
assert_contracts(&result, &ContractCheckConfig::default())?;
```

This lane validates runtime behavior without reimplementing protocol-machine checks in the host project. See [Protocol-Machine Simulation](15_vm_simulation_overview.md) for harness config fields and preset helpers.

## Performance and Diagnostics Controls

`VMConfig.effect_trace_capture_mode` controls effect trace overhead.
Default mode is `full`.

`VMConfig.payload_validation_mode` controls runtime payload hardening.
Use `off` for trusted benchmarks, `structural` for standard deployments, and `strict_schema` for adversarial inputs.

`VMConfig.max_payload_bytes` bounds payload size in protocol-machine message validation.
Default is `65536`.

`VMConfig.host_contract_assertions` enables runtime checks for handler identity stability, topology ordering inputs, and transfer-event auditability.
Default value is `false`.

## Integration Checklist

- Determinism: use stable ordering and deterministic serialization.
- Atomicity: ensure a failed effect does not leave partial host state.
- Isolation: keep handler state scoped to the active endpoint and session.
- Ownership: route session-local host mutation through a current ownership capability, not ad hoc session-store access.
- Canonical ingress: surface async work by later ingress calls rather than performing it inside synchronous request handling.
- Replayability: validate traces with `RecordingEffectHandler` and `ReplayEffectHandler`.
- Admission: keep protocol-machine runtime gates and profile settings explicit in `VMConfig`.

## Lean Correspondence

Lean splits effect execution and typing.
This split is in `lean/Runtime/VM/Model/TypeClasses.lean` and the typed
request/outcome model in `lean/Runtime/VM/Model/Effects.lean`.

| Rust or protocol-machine surface | Lean surface | Purpose |
|---|---|---|
| `EffectHandler` execution boundary | `EffectRuntime.exec` | executable effect semantics |
| handler typing obligation | `EffectSpec.handlerType` | typing-level effect contract |
| typed request/outcome model | `Runtime/VM/Model/Effects.lean` | shared effect-interface metadata plus request/outcome correspondence |
| invoke typing | `WellTypedInstr.wt_invoke` in `lean/Runtime/VM/Runtime/Monitor.lean` | ties invoke to handler type |
| behavioral equivalence | `Runtime/Proofs/EffectBisim/*` | observer-level bisimulation bridge |
| config equivalence bridge | `Runtime/Proofs/EffectBisim/ConfigEquivBridge.lean` | links protocol quotient and effect bisimulation |
| composed effect domains | `Runtime/Proofs/VM/DomainComposition.lean` | sum and product composition instances |

## Glossary

| Term | Meaning |
|---|---|
| `Program` and `Effect` | choreography free algebra in `telltale-choreography` |
| `ChoreoHandler` | async typed handler for generated choreography code |
| `EffectHandler` | sync protocol-machine host interface for runtime integration |
| `EffectRuntime` | Lean executable effect action and context transition |
| `EffectSpec` | Lean typing obligation for effect actions |
| `telltale_types::effects` | shared deterministic clock and RNG traits for simulation support |

## Related Docs

- [Choreography Effect Handlers](09_effect_handlers.md)
- [Protocol Machine Architecture](12_vm_architecture.md)
- [Lean Verification](23_lean_verification.md)
- [Lean-Rust Bridge](24_lean_rust_bridge.md)
