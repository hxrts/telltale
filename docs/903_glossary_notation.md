# Glossary and Notation Index

This page defines shared terms and symbols used across the documentation and paper-aligned pages.
It serves as the stable lookup for terminology and notation.

## Core Terms

| Term | Meaning | Primary Docs |
|---|---|---|
| coherence | Session-wide compatibility invariant between local type state, buffers, and global structure. | [Theory](103_theory.md), [Theorem Program](804_theorem_program.md) |
| harmony | Projection and protocol evolution commute under declared premises. | [Theory](103_theory.md), [Theorem Program](804_theorem_program.md) |
| projection | Mapping from global choreography to per-role local session types. | [Choreographic Projection Patterns](203_projection.md) |
| local type | Per-role protocol view used for runtime typing and progression. | [Theory](103_theory.md), [Session Lifecycle](403_session_lifecycle.md) |
| effect handler | Runtime boundary that interprets protocol-machine or choreography actions. | [Choreography Effect Handlers](301_effect_handlers.md), [Effect Handlers and Session Types](303_effect_session_bridge.md) |
| theorem-pack | Lean-exported capability inventory used by runtime admission gates. | [Lean Verification](801_lean_verification.md), [Capability Admission](702_capability_admission.md) |
| capability taxonomy | The four first-class protocol-critical capability classes: admission, ownership, evidence, transition. | [Capability Model](701_capability_model.md), [Authority Language Surface](703_authority_language_surface.md) |
| admission | Runtime gate process that checks contracts and capability evidence. | [Capability Admission](702_capability_admission.md) |
| ownership capability | Runtime host authority token carrying owner label, generation, and scope. | [Effect Handlers and Session Types](303_effect_session_bridge.md), [Session Lifecycle](403_session_lifecycle.md) |
| evidence | Typed proof object or witness consumed by protocol-critical authority flow. | [Authority Language Surface](703_authority_language_surface.md) |
| receipt | Single-use transfer or handoff proof emitted by an explicit ownership/delegation path. | [Session Lifecycle](403_session_lifecycle.md), [Authority Language Surface](703_authority_language_surface.md) |
| finalization subsystem | The explicit runtime/Lean model that classifies observed, authoritative, materialized, canonical, invalidated, and rejected semantic paths. | [Protocol Machine Architecture](401_protocol_machine_architecture.md), [Capability Model](701_capability_model.md) |
| canonical handle | Non-forgeable runtime reference proving a materialized/publication path is consumable as canonical truth. | [Authority Language Surface](703_authority_language_surface.md), [Capability Model](701_capability_model.md) |
| transition artifact | Receipt, handoff, or reconfiguration/runtime-upgrade object that carries explicit transfer or cutover authority. | [Capability Model](701_capability_model.md), [Authority Language Surface](703_authority_language_surface.md) |
| linear binding | Binding that the compiler requires to be consumed exactly once. | [Choreographic DSL](202_choreographic_dsl.md), [Authority Language Surface](703_authority_language_surface.md) |
| `Result` | Built-in success/failure sum form with `Ok` and `Err`. | [Choreographic DSL](202_choreographic_dsl.md) |
| `Maybe` | Built-in optional-value sum form with `Just` and `Nothing`. | [Choreographic DSL](202_choreographic_dsl.md) |
| effect declaration | Nominal choreography declaration for one typed external host interface. | [Authority Language Surface](703_authority_language_surface.md) |
| `uses` clause | Protocol-level declaration of which named effect interfaces may be invoked. | [Authority Language Surface](703_authority_language_surface.md) |
| timeout branch | Protocol-visible timeout/cancellation construct with explicit alternate branches. | [Choreographic DSL](202_choreographic_dsl.md), [Authority Language Surface](703_authority_language_surface.md) |
| ownership epoch | Generation used to invalidate stale owner handles after transfer or scope attenuation. | [Session Lifecycle](403_session_lifecycle.md) |
| canonical ingress | Sanctioned host event entry path such as `topology_events`, `send_decision`, `handle_recv`, or `step`. | [Effect Handlers and Session Types](303_effect_session_bridge.md) |
| stale-owner rejection | Fail-closed behavior when a prior ownership capability is reused after transfer or attenuation. | [Effect Handlers and Session Types](303_effect_session_bridge.md), [Session Lifecycle](403_session_lifecycle.md) |
| envelope | Declared refinement boundary for higher-concurrency and profile-scoped behavior. | [Protocol Machine Architecture](401_protocol_machine_architecture.md), [Rust-Lean Bridge and Parity](802_rust_lean_parity.md) |
| determinism profile | Runtime trace-equivalence contract mode such as `Full` or `Replay`. | [Protocol Machine Architecture](401_protocol_machine_architecture.md), [Rust-Lean Bridge and Parity](802_rust_lean_parity.md) |
| communication replay mode | Transport replay-consumption policy: `off`, `sequence`, or `nullifier`. | [Protocol Machine Architecture](401_protocol_machine_architecture.md), [Session Lifecycle](403_session_lifecycle.md) |
| communication nullifier | Domain-separated digest of canonical communication identity used for one-time receive consumption checks. | [Protocol Machine Architecture](401_protocol_machine_architecture.md), [Session Lifecycle](403_session_lifecycle.md) |
| consumption root | Deterministic accumulator root over communication replay-consumption state. | [Protocol Machine Architecture](401_protocol_machine_architecture.md), [Rust-Lean Bridge and Parity](802_rust_lean_parity.md) |
| protocol machine | Single-thread execution engine (`ProtocolMachine`) that runs projected local types with session type monitoring. | [Protocol Machine Architecture](401_protocol_machine_architecture.md) |
| guest runtime | Telltale-owned driver (`GuestRuntime`) instantiated around the protocol machine for simulation and runtime integration. | [Protocol Machine Architecture](401_protocol_machine_architecture.md), [API Reference](901_api_reference.md) |
| effect handler | Host-runtime boundary trait (`EffectHandler`) implemented by embedders and simulators. | [Effect Handlers and Session Types](303_effect_session_bridge.md), [API Reference](901_api_reference.md) |
| semantic object | Typed introspection record (such as `OperationInstance`, `OutstandingEffect`, `CanonicalHandle`) maintained by the protocol machine for audit and replay. | [Protocol Machine Architecture](401_protocol_machine_architecture.md), [API Reference](901_api_reference.md) |
| typed outcome | Structured success/failure result at the effect boundary using `EffectResult` and `EffectFailure` rather than raw strings. | [Capability Model](701_capability_model.md), [Authority Language Surface](703_authority_language_surface.md) |
| content addressing | Cryptographic identity scheme (`ContentId`) for protocol artifacts enabling deduplication and integrity checks. | [API Reference](901_api_reference.md) |
| nominal effect interface | Named effect declaration (`effect Name`) that makes host dependencies explicit and typed at the language level. | [Authority Language Surface](703_authority_language_surface.md), [Capability Model](701_capability_model.md) |
| conservation framework | The organizing design principle: all semantically meaningful behavior is expressed in terms of six conserved quantities. | [Conservation Framework](102_conservation_framework.md) |
| evidence (conserved property) | The integrity of what has been established. Witnesses, proofs, and attestations are its concrete forms. | [Conservation Framework](102_conservation_framework.md) |
| authority (conserved property) | The exclusivity of who may act. Ownership is its concrete form. | [Conservation Framework](102_conservation_framework.md) |
| identity (conserved property) | The definiteness of object references across retries, effects, and handoffs. | [Conservation Framework](102_conservation_framework.md) |
| commitment (conserved property) | The account of outstanding obligations. Outstanding effects are its concrete form. | [Conservation Framework](102_conservation_framework.md) |
| structure (conserved property) | The essential shape of the protocol. Multiparty session types are its concrete form. | [Conservation Framework](102_conservation_framework.md), [Theory](103_theory.md) |
| premise (conserved property) | The explicitness of environmental assumptions. Failure models and fairness assumptions are its concrete forms. | [Conservation Framework](102_conservation_framework.md) |
| erasure principle | Behavior not part of the conserved quantities is not part of the programming model. | [Conservation Framework](102_conservation_framework.md) |
| reduction principle | All runtime behavior must reduce to the conservation framework. | [Conservation Framework](102_conservation_framework.md) |
| region | Locality and framing domain for structured coordination with lifecycle, authority, and observation boundaries. | [Conservation Framework](102_conservation_framework.md) |
| semantic core objects | The closed set of protocol-visible objects: `Region`, `OperationInstance`, `OutstandingEffect`, `SemanticHandoff`, `AuthoritativeRead`, `ObservedRead`, `MaterializationProof`, `CanonicalHandle`, `ProgressContract`. | [Conservation Framework](102_conservation_framework.md), [Protocol Machine Architecture](401_protocol_machine_architecture.md) |

## Symbol and Notation Index

| Symbol or Form | Meaning | Primary Docs |
|---|---|---|
| `G` | Global protocol type. | [Theory](103_theory.md) |
| `L` or `LocalTypeR` | Local role protocol type. | [Theory](103_theory.md), [Protocol-Machine Bytecode Instructions](402_bytecode_instructions.md) |
| `project(G, R)` | Projection of global type `G` for role `R`. | [Theory](103_theory.md), [Choreographic Projection Patterns](203_projection.md) |
| `μX. ... X` | Recursive protocol form with bound variable `X`. | [Theory](103_theory.md) |
| `⊕{...}` | Internal choice at the selecting endpoint. | [Theory](103_theory.md) |
| `&{...}` | External choice at the receiving endpoint. | [Theory](103_theory.md) |
| `!T.S` | Send `T`, then continue as `S`. | [Theory](103_theory.md) |
| `?T.S` | Receive `T`, then continue as `S`. | [Theory](103_theory.md) |
| `end` | Session termination state. | [Theory](103_theory.md) |
| `Consume` | Recursive receiver-side trace alignment kernel used in coherence proofs. | [Theory](103_theory.md), [Theorem Program](804_theorem_program.md) |
| `n = 1` | Canonical single-step concurrency regime for exact parity. | [Protocol Machine Architecture](401_protocol_machine_architecture.md), [Rust-Lean Bridge and Parity](802_rust_lean_parity.md) |
| `n > 1` | Higher-concurrency regime admitted under envelope and premise-scoped constraints. | [Protocol Machine Architecture](401_protocol_machine_architecture.md), [Rust-Lean Bridge and Parity](802_rust_lean_parity.md) |
| `Full`, `ModuloEffects`, `ModuloCommutativity`, `Replay` | Runtime determinism profiles. | [Protocol Machine Architecture](401_protocol_machine_architecture.md), [Rust-Lean Bridge and Parity](802_rust_lean_parity.md) |
| `off`, `sequence`, `nullifier` | Communication replay-consumption modes. | [Protocol Machine Architecture](401_protocol_machine_architecture.md), [Session Lifecycle](403_session_lifecycle.md) |
| `telltale.comm.identity.v1` | Domain-separation tag for canonical communication identity schema. | [Protocol Machine Architecture](401_protocol_machine_architecture.md) |
| `case ... of` | Exhaustive sum-pattern branching over forms such as `Result` and `Maybe`. | [Choreographic DSL](202_choreographic_dsl.md), [Authority Language Surface](703_authority_language_surface.md) |
| `let x = check Effect.op(args)` | Typed external query binding that later lowers to the protocol-machine effect boundary. | [Choreographic DSL](202_choreographic_dsl.md), [Authority Language Surface](703_authority_language_surface.md) |
| `effect Name` | Nominal effect-interface declaration. | [Authority Language Surface](703_authority_language_surface.md) |
| `protocol P uses Runtime, Audit` | Protocol declaration naming its allowed effect interfaces. | [Authority Language Surface](703_authority_language_surface.md) |
| `timeout 5s R at ... on timeout => ... on cancel => ...` | Protocol-visible timeout and cancellation branch form. | [Choreographic DSL](202_choreographic_dsl.md), [Authority Language Surface](703_authority_language_surface.md) |

## Notation Consistency Rules

Use one symbol for one concept in a local section.
Reintroduce symbols when crossing between theory and runtime notation.
Prefer existing symbols from this index unless precision requires a different one.

## Related Docs

- [Conservation Framework](102_conservation_framework.md)
- [Theory](103_theory.md)
- [Protocol Machine Architecture](401_protocol_machine_architecture.md)
- [Rust-Lean Bridge and Parity](802_rust_lean_parity.md)
- [Theorem Program](804_theorem_program.md)
