# Effect Handlers and Session Types

This document defines the integration boundary between Telltale and a host runtime.
The boundary is the VM `EffectHandler` interface.

## Scope

Use this document when integrating Telltale into another execution environment.
Use [Choreography Effect Handlers](08_effect_handlers.md) when implementing async handlers for generated choreography code.

## Three-Layer Contract

Telltale uses three layers.

| Layer | Artifact | Role |
|---|---|---|
| Global protocol layer | choreography and projection | defines role-local protocol obligations |
| Effect layer | handler interfaces | defines runtime action behavior |
| VM layer | bytecode and monitor checks | enforces instruction-level typing and admission rules |

Projection and runtime checks preserve obligations across these layers.

## Rust Handler Surfaces

Rust exposes two handler interfaces.

| Interface | Location | Purpose |
|---|---|---|
| `ChoreoHandler` | `rust/choreography/src/effects/handler.rs` | async typed API for generated choreography code |
| `EffectHandler` | `rust/vm/src/effect.rs` | sync VM API over bytecode values |

Third-party runtime integration should use `EffectHandler`.

## Why the VM Boundary

`EffectHandler` is synchronous.
This matches deterministic host execution models.
It avoids futures and runtime-specific scheduling inside handler calls.

`EffectHandler` operates on VM values and labels.
This keeps the wire and storage boundary host-defined.
It avoids coupling to generated Rust message types.

The VM monitor enforces session typing before and during execution.
The boundary keeps typing logic in Telltale.
It keeps host logic focused on effect interpretation.

## Boundary Ownership

The boundary separates protocol semantics from host materialization.

| Concern | Telltale VM owns | Host `EffectHandler` owns |
|---|---|---|
| Session typing | Local type checks and continuation advancement | none |
| Buffer and signature discipline | enqueue, dequeue, and signature verification | none |
| Scheduler and commit | coroutine scheduling and atomic step commit | none |
| Send policy | call point and branch label context | `send_decision` return value |
| Receive side effects | receive timing and source payload | register and host state mutation in `handle_recv` |
| Invoke integration | when invoke runs | integration state mutation in `step` |
| Guard transitions | VM guard instruction flow | grant or block in `handle_acquire`, validation in `handle_release` |
| Topology metadata | event ingestion order and application | produced events in `topology_events` |
| Output metadata | commit-time query point | optional hint from `output_condition_hint` |

## VM Callback Semantics

The VM dispatch path is in `rust/vm/src/vm.rs`.
The trait surface is in `rust/vm/src/effect.rs`.
The normative contract is documented in that trait module.
The contract marks `handle_send` and `handle_choose` as compatibility hooks.

| Callback | VM call point | Runtime behavior | Integration note |
|---|---|---|---|
| `send_decision` | `step_send`, `step_offer` | called before enqueue | payload is provided by VM register value in current dispatch path |
| `handle_send` | default inside `send_decision` | fallback behavior | not used by canonical send path because payload is already provided |
| `handle_recv` | `step_recv`, `step_choose` | called after dequeue and verification | use for state updates and host-side effects |
| `handle_choose` | trait method only | no canonical call site today | keep implementation for compatibility and custom runners |
| `step` | `step_invoke` | called during `Invoke` instruction | use for integration steps and persistent deltas |
| `handle_acquire` | `step_acquire` | grant or block acquire | return `Grant` with evidence or `Block` |
| `handle_release` | `step_release` | release validation | return error to reject invalid evidence |
| `topology_events` | `ingest_topology_events` | called once per scheduler tick | events are sorted by deterministic ordering key before apply |
| `output_condition_hint` | post-dispatch pre-commit | queried only when a step emits events | return `None` to use VM default |
| `handler_identity` | trace and commit attribution | stable handler id in traces | use deterministic identity value |

## Error Classification

The VM keeps callback signatures as `Result<_, String>`.
Use `classify_effect_error` and `EffectError` from `telltale-vm` for typed diagnostics.
This keeps runtime semantics unchanged and improves host observability.

| Utility | Purpose |
|---|---|
| `classify_effect_error` | maps raw handler error strings to `EffectErrorCategory` |
| `classify_effect_error_owned` | wraps raw strings into `EffectError` |
| `EffectErrorCategory` | coarse taxonomy for timeout, topology, determinism, and contract failures |

## Integration Workflow

1. Use `telltale-theory` at setup time to project global types to local types.
2. Compile local types to VM bytecode and load with `CodeImage`.
3. Implement `EffectHandler` with deterministic host operations.
4. Map each callback to host primitives without reimplementing protocol typing.
5. Run `run_loaded_vm_record_replay_conformance` to validate record and replay behavior on a loaded VM.
6. Run Lean bridge lanes for parity and equivalence checks.

## Integration Tooling

Use `just effect-scaffold` to generate host integration stubs.
The command emits deterministic `EffectHandler` templates, VM smoke tests, and simulator harness contract tests.
It also writes a local scaffold `README.md` with next-step instructions.

```text
just effect-scaffold
```

This command writes files under `work/effect_handler_scaffold` by default. Use `cargo run -p effect-scaffold -- --no-simulator` when you want only VM level stubs without simulator harness artifacts.

Use `just sim-run <config>` to execute a simulator harness config file.
This command runs the VM with scenario middleware and contract checks.
It is the fastest path for CI validation in third party host projects.

```text
just sim-run work/sim_integration.toml
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

This lane validates runtime behavior without reimplementing VM checks in the host project. See [VM Simulation](14_vm_simulation.md) for harness config fields and preset helpers.

## Performance and Diagnostics Controls

`send_decision_fast_path` is an optional hook for host-side cache lookups.
Default behavior is unchanged when the hook returns `None`.

`VMConfig.effect_trace_capture_mode` controls effect trace overhead.
Default mode is `full`.

`VMConfig.payload_validation_mode` controls runtime payload hardening.
Use `off` for trusted benchmarks, `structural` for standard deployments, and `strict_schema` for adversarial inputs.

`VMConfig.max_payload_bytes` bounds payload size in VM message validation.
Default is `65536`.

`VMConfig.host_contract_assertions` enables runtime checks for handler identity stability and topology ordering inputs.
Default value is `false`.

## Integration Checklist

- Determinism: use stable ordering and deterministic serialization.
- Atomicity: ensure a failed effect does not leave partial host state.
- Isolation: keep handler state scoped to the active endpoint and session.
- Replayability: validate traces with `RecordingEffectHandler` and `ReplayEffectHandler`.
- Admission: keep VM runtime gates and profile settings explicit in `VMConfig`.

## Lean Correspondence

Lean splits effect execution and typing.
This split is in `lean/Runtime/VM/Model/TypeClasses.lean`.

| Rust or VM surface | Lean surface | Purpose |
|---|---|---|
| `EffectHandler` execution boundary | `EffectRuntime.exec` | executable effect semantics |
| handler typing obligation | `EffectSpec.handlerType` | typing-level effect contract |
| invoke typing | `WellTypedInstr.wt_invoke` in `lean/Runtime/VM/Runtime/Monitor.lean` | ties invoke to handler type |
| behavioral equivalence | `Runtime/Proofs/EffectBisim/*` | observer-level bisimulation bridge |
| config equivalence bridge | `Runtime/Proofs/EffectBisim/ConfigEquivBridge.lean` | links protocol quotient and effect bisimulation |
| composed effect domains | `Runtime/VM/Composition/DomainComposition.lean` | sum and product composition instances |

## Glossary

| Term | Meaning |
|---|---|
| `Program` and `Effect` | choreography free algebra in `telltale-choreography` |
| `ChoreoHandler` | async typed handler for generated choreography code |
| `EffectHandler` | sync VM host interface for runtime integration |
| `EffectRuntime` | Lean executable effect action and context transition |
| `EffectSpec` | Lean typing obligation for effect actions |
| `telltale_types::effects` | shared deterministic clock and RNG traits for simulation support |

## Related Docs

- [Choreography Effect Handlers](08_effect_handlers.md)
- [VM Architecture](11_vm_architecture.md)
- [Lean Verification](18_lean_verification.md)
- [Lean-Rust Bridge](19_lean_rust_bridge.md)
