# Protocol Machine Architecture

This document defines the protocol-machine architecture, scheduling semantics, and concurrency envelope. These surfaces are used by Rust runtime targets and Lean conformance surfaces.

## Architecture Overview

The protocol machine is the sole authority over semantic progression. It realizes structure conservation and authority conservation from the [Conservation Framework](37_conservation_framework.md). All protocol-visible truth is committed through the protocol machine. Handlers may stage and return effect outcomes, but they do not mutate semantic state directly.

The canonical semantic authority is `ProtocolMachineKernel`. The cooperative `ProtocolMachine` and threaded `ThreadedProtocolMachine` (backed by `NativeThreadedDriver`) are the guest-runtime execution surfaces that call kernel-owned step entrypoints. Both implement the `KernelMachine` trait, which provides `kernel_step_round` for executing scheduler rounds.

The runtime keeps a single state model across targets. Core state includes coroutines, sessions, scheduler queues, observable trace, and effect trace. It also includes live operation-instance state, live outstanding-effect state, delegation audit records, and failure-topology snapshot fields.
The canonical exported semantic surface is the semantic-object family:
`OperationInstance`, `OutstandingEffect`, `SemanticHandoff`,
`AuthoritativeRead`, `ObservedRead`, `MaterializationProof`,
`CanonicalHandle`, `PublicationEvent`, `ProgressContract`, and
`ProgressTransition`.

Canonicalization is not implicit in those object lists. The runtime derives a
first-class finalization subsystem from them in
`rust/machine/src/semantic_objects.rs`:

- `ProtocolMachineFinalization`
- `FinalizationPath`
- `FinalizationReadClass`
- `FinalizationStage`

That subsystem is the explicit runtime boundary between provisional
observation, authoritative evidence, proof-bearing materialization, canonical
publication/handle issuance, invalidation after handoff, and rejected
publication paths.

The first-class protocol-critical capability boundary is intentionally split
into four classes:

- admission capability surfaces
- ownership capability surfaces
- evidence/finalization capability surfaces
- transition capability surfaces

The source-of-truth Rust and Lean boundaries for that taxonomy are
`rust/machine/src/capabilities.rs` and `lean/Runtime/Proofs/Capabilities.lean`.
The bridge-facing strict correspondence surface for the first-class
capability/finalization model is `rust/bridge/tests/capability_model_correspondence.rs`
against `inspectCapabilityModel` in the Lean runner.

The canonical round model is one semantic step when concurrency is nonzero. Threaded execution is admitted as an extension only when the wave certificate gate is satisfied.

## Engine Roles

| Engine | Role | Contract Surface |
|---|---|---|
| `ProtocolMachine` (`protocol machine`) | Canonical cooperative protocol machine | Exact reference for parity at concurrency `1` |
| `ThreadedGuestRuntime` (`NativeThreadedDriver`) | Parallel wave executor | Certified-wave execution with fallback to canonical one-step |
| WASM guest runtime | Single-thread deployment | Cooperative schedule only |

## Scheduler Semantics

Canonical scheduling is one semantic step when concurrency is nonzero. `ProtocolMachineKernel` owns the selection and step contract. For cooperative execution, this gives exact behavior for deterministic replay and baseline parity.

The canonical Lean runner is `runScheduled` in `Runtime/ProtocolMachine/Runtime/Runner.lean`. For nonzero concurrency, canonical round semantics normalize to one scheduler step. This model is the semantic reference for parity at concurrency `1`.

## Scheduler Policies

Scheduler policy controls selection order. Policy does not change instruction semantics.

| Policy | Primary Runtime Use |
|---|---|
| `Cooperative` | Canonical single-step execution and WASM deployment |
| `RoundRobin` | Fair queue progression in native runs |
| `Priority` | Explicit priority maps or token weighting |
| `ProgressAware` | Token-biased pick behavior |

## Threaded Wave Execution

Threaded execution selects compatible picks per wave. Compatibility is lane-disjoint, session-disjoint, and footprint-disjoint for picks in the same wave.

The threaded extension is defined in `Runtime/ProtocolMachine/Runtime/ThreadedRunner.lean`. Concurrency `n = 1` is theorem-equal to canonical execution. For `n > 1`, execution is admitted through certified waves. Invalid certificates degrade to canonical one-step behavior.

Each wave is checked against a `WaveCertificate`. If certificate validation fails, the runtime degrades to canonical one-step behavior for that round.

## Refinement Envelope

| Concurrency Regime | Required Contract | Enforcement Lane |
|---|---|---|
| `n = 1` | Exact canonical parity | `threaded_equivalence.rs` |
| `n > 1` | Envelope-bounded parity with declared `EnvelopeDiff` | `parity_fixtures_v2.rs` |
| Invalid wave certificate | Mandatory fallback to canonical one-step | `threaded_lane_runtime.rs` |
| Undocumented deviation | Active deviation coverage required | `just check-parity --types` |

The regression lane validates both regimes. The test `canonical_parity_is_exact_at_concurrency_one` enforces exact equality. The test `envelope_bounded_parity_holds_for_n_gt_1` enforces envelope-bounded behavior.

## Runtime Gates

Runtime mode admission and profile selection are capability gated.

| Gate | Runtime Surface | Current Rust Path |
|---|---|---|
| Advanced mode admission | `requires_protocol_machine_runtime_contracts` and `admit_protocol_machine_runtime` | `rust/machine/src/runtime_contracts.rs`, `rust/machine/src/composition.rs` |
| Determinism profile validation | `request_determinism_profile` | `rust/machine/src/runtime_contracts.rs`, `rust/machine/src/composition.rs` |
| Threaded certified-wave fallback | `WaveCertificate` check with one-step degrade | `rust/machine/src/threaded.rs` |
| Deviation registry enforcement | Undocumented parity drift rejection | `just check-parity --types` |

## Runtime Hardening Contracts

The guest-runtime adapters now enforce explicit runtime hardening at load and startup boundaries.

- `ThreadedProtocolMachine` (backed by `NativeThreadedDriver`) provides `with_workers` for initialization. The inner driver also provides `try_with_workers` for fallible initialization.
- Cooperative and threaded `load_choreography` paths validate trusted `CodeImage` runtime shape before session allocation.
- Preferred host integration uses `load_choreography_owned(...)` and `OwnedSession` when the embedding runtime needs explicit session ownership after open.
- Register-bound violations are fail-closed through `Fault::OutOfRegisters` rather than unchecked index panic in executable instruction paths.
- Language-level `effect` declarations and `check` expressions lower through the
  same `Invoke`/`EffectHandler` boundary rather than introducing a second host
  execution channel.

## Host Ownership Contract in the Runtime

The protocol-machine architecture now distinguishes three runtime concepts:

| Runtime concept | Purpose |
|---|---|
| protocol typing | monitor/local-type correctness |
| capability admission | whether a runtime mode/profile is allowed |
| current ownership | which host capability may mutate session-local runtime state right now |

Ownership is a host-runtime contract, not a replacement for typing or admission.

Runtime ownership details:

- session-local host mutation flows through an ownership capability carrying owner label, generation, and scope
- transfer is staged with explicit receipts
- readiness, cancellation, and timeout witnesses are first-class runtime objects with explicit lifecycle transitions
- delegation emits auditable transfer records
- host assertion mode can reject transfer events that do not have matching committed audit records
- language-level authority/evidence constructs must lower to these runtime
  ownership and audit surfaces instead of bypassing them with host-local
  heuristics

## Failure and Timeout Event Surface

Failure-visible behavior now uses explicit observable events rather than relying on host-side inference from final state alone.

| Event | Runtime role |
|---|---|
| `TimeoutIssued` | records deterministic timeout activation and timeout-witness issuance |
| `CancellationRequested` | records the start of an explicit cancellation path |
| `Cancelled` | records successful cancellation completion |
| `FailureBranchEntered` | records typed failure visibility before coroutine fault finalization |
| `SessionTerminal` | records the terminal reason for close, cancel, abort, or fault |

For canonical ordering, the cooperative runtime emits the explicit event sequence before any coarser terminal summary. Threaded execution must preserve the same per-session ordering in its observable trace envelope.

## Semantic Audit Surface

Replay-visible auditability now has one canonical surface derived from existing semantic artifacts rather than ad hoc logging-only streams. Effect observations now flow from the runtime's live outstanding-effect state rather than being reconstructed only from generic trace order.

| Source surface | Canonical semantic record |
|---|---|
| authority witness audit log | `SemanticAuditRecord::Authority` |
| delegation audit log | `SemanticAuditRecord::Delegation` |
| explicit failure/timeout/cancellation/session-terminal events | `FailureBranchEntered`, `TimeoutIssued`, `CancellationRequested`, `Cancelled`, `SessionTerminal` |
| outstanding-effect runtime state | `EffectObservation` with nominal interface/operation classification |

Runtime accessors:

- `ProtocolMachine::semantic_audit_log()`
- `ThreadedGuestRuntime::semantic_audit_log()`
- `canonical_replay_fragment().semantic_audit_log`
- `ProtocolMachine::capability_lifecycle_audit_log()`
- `ThreadedGuestRuntime::capability_lifecycle_audit_log()`

This keeps replay, simulator harnesses, and parity checks aligned on one derived semantic audit vocabulary.
Language-level authority checks are expected to arrive at this same audit
surface after lowering, with the nominal effect interface and operation name
retained in `EffectObservation`.

## Canonical Semantic Objects

The protocol machine now exports one higher-level semantic object bundle derived
from live operation/effect runtime state plus authority, delegation, and
output-condition surfaces.

Runtime accessors:

- `ProtocolMachine::semantic_objects()`
- `ThreadedGuestRuntime::semantic_objects()`
- `canonical_replay_fragment().semantic_objects`

This bundle is the canonical bridge-facing and replay-facing representation of
operation instances, outstanding effects, semantic handoffs, authoritative and
observed reads, materialization proofs, canonical handles, publication events,
progress contracts, and progress transitions.

`OperationInstance` and `OutstandingEffect` are first-class runtime objects.
They carry owner id, budget ticks, retry policy, invalidation token,
dependent-operation edges, and terminal publication state. Replay export and
bridge payloads consume those runtime objects directly instead of deriving them
later from raw trace order.

`ProgressContract` is now live runtime state, not a post-hoc summary. It carries
bounded-wait metadata, last-progress tick, escalation timestamp, and the
current explicit state (`pending`, `blocked`, `no_progress`, `degraded`,
`timed_out`, and the existing terminal states). `ProgressTransition` makes each
escalation replay-visible. This allows late-result invalidation and degraded behavior to be
compared across cooperative, threaded, and wasm targets.

`PublicationEvent` is the one canonical runtime publication surface. It carries
publication id, operation id, observer class, publication status, and optional
proof/handle references. Proof-bearing success and publication-path
uniqueness are replay-visible through this surface.

## Delegation and Reconfiguration Path

Runtime delegation uses one sanctioned manager-style path rather than scattered owner mutation.

| Step | Runtime behavior |
|---|---|
| decode transfer | extract endpoint and target coroutine |
| coherence validation | ensure source, target, and delegated endpoint stay within the intended session boundary |
| issue receipt | allocate an explicit delegation receipt with endpoint-scoped authority |
| apply transfer | move endpoint bundle and associated runtime state |
| post-check | validate resulting owner state |
| audit or rollback | record committed transfer or roll back and emit rollback audit |

This path is the runtime realization of delegation/reconfiguration. It should not be read as the theorem statement itself. The theorem-level side remains `DelegationWF` and related harmony results.

Reconfiguration is no longer only a single-step membership swap. The runtime now
supports deterministic multi-step reconfiguration plans with:

- canonical per-phase `ReconfigurationEvent` artifacts
- placement observations and derived transport-boundary summaries per phase
- atomic plan execution, so invalid later steps do not partially commit earlier
  transitions
- serializable reconfiguration snapshots that preserve membership history and
  executed plan artifacts across recovery

Typesafe runtime upgrade is now modeled as a specialized transition family
inside that same reconfiguration subsystem rather than as an ambient host
story. The canonical upgrade surfaces are:

- `RuntimeUpgradeRequest`
- `RuntimeUpgradeExecution`
- `RuntimeUpgradeArtifact`
- `TransitionArtifactPhase`

Each runtime upgrade records an explicit staged, admitted, committed-cutover,
rolled-back, or failed artifact sequence. The admitted cutover contract is
explicit about:

- execution-profile compatibility
- ownership continuity across the first cutover
- pending-effect treatment
- canonical publication continuity

Those upgrade artifacts are serialized inside
`ReconfigurationRuntimeSnapshot.runtime_upgrades`, so replay, recovery, and
bridge-facing export can distinguish committed cutover from rollback/failure
instead of inferring it from final membership alone.

These artifacts stay transport agnostic. They record resolved placement facts
and boundary classes (`in_process`, `shared_memory`, `network`) rather than any
deployment-product-specific backend details.

## Capability Gate Architecture

| Capability Gate | Lean Surface | Rust Surface |
|---|---|---|
| Advanced mode admission | `requiresVMRuntimeContracts`, `admitVMRuntime` | `requires_protocol_machine_runtime_contracts`, `admit_protocol_machine_runtime` |
| Live migration switch | `requestLiveMigration` | Runtime contracts capability booleans in composition admission |
| Autoscale/repartition switch | `requestAutoscaleOrRepartition` | Runtime contracts capability booleans in composition admission |
| Placement refinement switch | `requestPlacementRefinement` | Runtime contracts capability booleans in composition admission |
| Relaxed reordering switch | `requestRelaxedReordering` | Runtime contracts capability booleans in composition admission |

## Determinism Profiles

`ProtocolMachineConfig.determinism_mode` includes `Full`, `ModuloEffects`, `ModuloCommutativity`, and `Replay`.

| Profile | Lean Profile | Rust Profile | Gate Requirement |
|---|---|---|---|
| Full | `full` | `DeterminismMode::Full` | Profile artifact support |
| Modulo effect trace | `moduloEffectTrace` | `DeterminismMode::ModuloEffects` | Mixed-profile capability plus artifact support |
| Modulo commutativity | `moduloCommutativity` | `DeterminismMode::ModuloCommutativity` | Mixed-profile capability plus artifact support |
| Replay | `replay` | `DeterminismMode::Replay` | Mixed-profile capability plus artifact support |

## Communication Consumption Identity

Communication replay-consumption uses one canonical identity schema across send and receive checks.

Canonical identity fields:

- Domain tag: `telltale.comm.identity.v1`
- Session id: `sid`
- Directed edge endpoints: `sender`, `receiver`
- Protocol step context: `step_kind` (`send`, `recv`, `offer`, `choose`) and local label context
- Message label: `label`
- Payload digest: domain-separated digest of serialized payload bytes
- Sequence number: `seq_no` (used by `sequence` mode, carried for all modes)

Replay semantics by mode:

- `off`: no replay-consumption checks are enforced.
- `sequence`: receive must consume exactly the expected next `seq_no` per `(sid, sender, receiver)`.
- `nullifier`: receive computes a nullifier over the canonical identity and rejects already-consumed identities.

Replay outcomes:

- Duplicate delivery: reject in `sequence` and `nullifier`, accept in `off`.
- Reordered delivery: reject in `sequence`, accepted when unseen in `nullifier`, accept in `off`.
- Cross-session reuse: reject in `sequence` and `nullifier` because `sid` is part of canonical identity.

## Proved Theorem Surfaces

| Area | Lean Surface | Status |
|---|---|---|
| Canonical round normalization | `Runtime/Proofs/Concurrency.lean` | Proved |
| Threaded equality at `n = 1` | `sched_round_threaded_one_eq_sched_round_one`, `run_scheduled_threaded_one_eq_run_scheduled` | Proved |
| Per-session trace equality at `n = 1` | `per_session_trace_threaded_one_eq_canonical` | Proved |
| Scheduler theorem exports | `Runtime/Proofs/protocol machine/Scheduler.lean` | Proved |

## Premise-Scoped Interface Surfaces

| Area | Lean Surface | Interface Type |
|---|---|---|
| Threaded `n > 1` refinement | `ThreadedRoundRefinementPremises` | Premise-scoped |
| Runtime admission/profile gates | `Runtime/Proofs/Contracts/RuntimeContracts.lean` | Interface consumed by runtime |
| Theorem-pack capability inventory APIs | `Runtime/Proofs/TheoremPack/API.lean` | Interface consumed by runtime |

These interfaces are intentionally explicit. They are not claimed as unconditional global theorems. Canonical one-step normalization and `n = 1` refinement are theorem-backed in Lean. Higher-concurrency threaded refinement is modeled as a certified interface with premise-scoped refinement obligations.

Rust uses executable certificate checking and parity fixtures as release guards.

## Release and CI Conformance

Release conformance surfaces are exported through theorem-pack APIs and enforced by `just check-release-conformance`. Parity and drift governance are enforced by `just check-parity --all`.

## Related Docs

- [Protocol-Machine Bytecode Instructions](13_bytecode_instructions.md)
- [Session Lifecycle](14_session_lifecycle.md)
- [Protocol-Machine Simulation](15_protocol_machine_simulation_overview.md)
- [Rust-Lean Parity](19_rust_lean_parity.md)
- [Effect Handlers and Session Types](11_effect_session_bridge.md)
- [Lean Verification](23_lean_verification.md)
- [Capability and Admission](25_capability_admission.md)
