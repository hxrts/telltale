# Session Type Theory

This document summarizes the current theorem surfaces in the Lean libraries that back Telltale.

## Scope

The theory surface is no longer limited to core projection and duality.

It now includes SessionTypes, SessionCoTypes, Choreography, Semantics, Protocol, Runtime, Distributed, Classical, and theorem-pack admission layers.

The generated map currently reports 610 files and about 126,260 lines across these libraries.

## Core Session and Coinductive Foundations

Session syntax and conversions live in `lean/SessionTypes` and `lean/SessionCoTypes`.

| Surface | Main capability |
|---|---|
| `SessionTypes` | global and local syntax, well-formedness, named and de Bruijn forms |
| `SessionCoTypes` | coinductive equality, bisimulation, regularity, decidable checks |
| conversion bridge | named and coinductive roundtrip theorems |

These modules provide the base language for protocol safety and algorithmic decision procedures.

## Projection and Harmony

Projection theory lives in `lean/Choreography`.

| Surface | Main capability |
|---|---|
| projection algorithms | candidate generation, boolean checker, proof-carrying projection |
| blindness and erasure | decidable projectability side conditions |
| harmony proofs | local and global step commutation under stated premises |

These proofs connect global protocol structure to endpoint-local behavior.

## Operational Protocol Theory

Protocol metatheory lives in `lean/Protocol`.

| Surface | Main capability |
|---|---|
| coherence | active-edge buffered safety invariant |
| preservation and typing | step safety and subject reduction |
| determinism and independence | commuting-step and isolation statements |
| monitor and deployment | runtime well-typed monitoring and composition interfaces |

Deadlock and liveness claims are assumption-scoped in this stack. They require explicit fairness and progress premises.

## Runtime and VM Proof Layer

Runtime proof surfaces live in `lean/Runtime`.

| Surface | Main capability |
|---|---|
| VM model and semantics | instruction, state, and step definitions |
| theorem-pack inventory | capability extraction for release and admission |
| admission and adequacy | envelope adherence, admission soundness and completeness |
| Lean to runtime bridge | monitor and execution correspondence interfaces |

This layer is the direct proof interface consumed by Rust parity and runtime gate checks.

## Distributed and Classical Extensions

Distributed theorem families live in `lean/Distributed` and runtime adapters. Classical transport families live in `lean/Classical` and runtime adapters.

Distributed coverage includes FLP, CAP, quorum geometry, partial synchrony, responsiveness, Nakamoto security, reconfiguration, atomic broadcast, accountable safety, failure detectors, data availability, coordination, CRDT, Byzantine safety, consensus envelope, and failure envelope.

Classical coverage includes Foster-Lyapunov, MaxWeight, large deviations, mean-field, heavy-traffic, mixing, fluid limits, concentration bounds, Little's law, and functional CLT.

## Repository Status

Current generated reports indicate axiom-free and sorry-free status for the Lean tree.

Proof results that depend on additional premises are represented as explicit premise bundles and admission interfaces. They are not presented as unconditional theorem claims.

## Related Docs

- [Background](00_introduction.md)
- [Choreographic Projection Patterns](05_projection.md)
- [Lean Verification](18_lean_verification.md)
- [Theorem Program](26_theorem_program.md)
- [Distributed and Classical Families](27_distributed_classical_families.md)
