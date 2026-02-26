# Glossary and Notation Index

This page defines shared terms and symbols used across the docs and paper-aligned pages.
Use it as a stable lookup for terminology and notation.

## Core Terms

| Term | Meaning | Primary Docs |
|---|---|---|
| coherence | Session-wide compatibility invariant between local type state, buffers, and global structure. | [Theory](05_theory.md), [Theorem Program](26_theorem_program.md) |
| harmony | Projection and protocol evolution commute under declared premises. | [Theory](05_theory.md), [Theorem Program](26_theorem_program.md) |
| projection | Mapping from global choreography to per-role local session types. | [Choreographic Projection Patterns](07_projection.md) |
| local type | Per-role protocol view used for runtime typing and progression. | [Theory](05_theory.md), [Session Lifecycle](14_session_lifecycle.md) |
| effect handler | Runtime boundary that interprets VM or choreography actions. | [Choreography Effect Handlers](09_effect_handlers.md), [Effect Handlers and Session Types](11_effect_session_bridge.md) |
| theorem-pack | Lean-exported capability inventory used by runtime admission gates. | [Lean Verification](23_lean_verification.md), [Capability and Admission](25_capability_admission.md) |
| admission | Runtime gate process that checks contracts and capability evidence. | [Capability and Admission](25_capability_admission.md) |
| envelope | Declared refinement boundary for higher-concurrency and profile-scoped behavior. | [VM Architecture](12_vm_architecture.md), [VM Parity](19_vm_parity.md) |
| determinism profile | Runtime trace-equivalence contract mode such as `Full` or `Replay`. | [VM Architecture](12_vm_architecture.md), [VM Parity](19_vm_parity.md) |
| communication replay mode | Transport replay-consumption policy: `off`, `sequence`, or `nullifier`. | [VM Architecture](12_vm_architecture.md), [Session Lifecycle](14_session_lifecycle.md) |
| communication nullifier | Domain-separated digest of canonical communication identity used for one-time receive consumption checks. | [VM Architecture](12_vm_architecture.md), [Session Lifecycle](14_session_lifecycle.md) |
| consumption root | Deterministic accumulator root over communication replay-consumption state. | [VM Architecture](12_vm_architecture.md), [VM Parity](19_vm_parity.md) |

## Symbol and Notation Index

| Symbol or Form | Meaning | Primary Docs |
|---|---|---|
| `G` | Global protocol type. | [Theory](05_theory.md) |
| `L` or `LocalTypeR` | Local role protocol type. | [Theory](05_theory.md), [Bytecode Instructions](13_bytecode_instructions.md) |
| `project(G, R)` | Projection of global type `G` for role `R`. | [Theory](05_theory.md), [Choreographic Projection Patterns](07_projection.md) |
| `μX. ... X` | Recursive protocol form with bound variable `X`. | [Theory](05_theory.md) |
| `⊕{...}` | Internal choice at the selecting endpoint. | [Theory](05_theory.md) |
| `&{...}` | External choice at the receiving endpoint. | [Theory](05_theory.md) |
| `!T.S` | Send `T`, then continue as `S`. | [Theory](05_theory.md) |
| `?T.S` | Receive `T`, then continue as `S`. | [Theory](05_theory.md) |
| `end` | Session termination state. | [Theory](05_theory.md) |
| `Consume` | Recursive receiver-side trace alignment kernel used in coherence proofs. | [Theory](05_theory.md), [Theorem Program](26_theorem_program.md) |
| `n = 1` | Canonical single-step concurrency regime for exact parity. | [VM Architecture](12_vm_architecture.md), [VM Parity](19_vm_parity.md) |
| `n > 1` | Higher-concurrency regime admitted under envelope and premise-scoped constraints. | [VM Architecture](12_vm_architecture.md), [VM Parity](19_vm_parity.md) |
| `Full`, `ModuloEffects`, `ModuloCommutativity`, `Replay` | Runtime determinism profiles. | [VM Architecture](12_vm_architecture.md), [VM Parity](19_vm_parity.md) |
| `off`, `sequence`, `nullifier` | Communication replay-consumption modes. | [VM Architecture](12_vm_architecture.md), [Session Lifecycle](14_session_lifecycle.md) |
| `telltale.comm.identity.v1` | Domain-separation tag for canonical communication identity schema. | [VM Architecture](12_vm_architecture.md) |

## Notation Consistency Rules

Use one symbol for one concept in a local section.
Reintroduce symbols when crossing between theory and runtime notation.
Prefer existing symbols from this index unless precision requires a different one.

## Related Docs

- [Theory](05_theory.md)
- [VM Architecture](12_vm_architecture.md)
- [VM Parity](19_vm_parity.md)
- [Theorem Program](26_theorem_program.md)
