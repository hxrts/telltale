# Lean VM Executable Architecture

This document defines executable-module boundaries and ownership for `lean/Runtime/VM`.

## Module Boundaries

- `Runtime/VM/Model/*`: runtime data types, config, state, instruction forms, event surfaces.
- `Runtime/VM/Semantics/*`: executable step semantics (`step*` instruction transitions).
- `Runtime/VM/Runtime/*`: runtime adapters (loader, JSON, monitor, failure ingress).
- `Runtime/VM/API.lean`: stable facade for executable VM API imports.
- `Runtime/VM/Composition/*`: composition/admission and theorem-pack integration surfaces.
- `Runtime/Proofs/*`: proof/theorem-pack modules (not required for core executable stepping).

## Ownership Map

- Scheduler/state machine semantics: VM runtime owners.
- Loader/image representation and projection ingestion: VM runtime + bridge owners.
- Monitor precheck and fault classification: VM runtime owners.
- Flow/output policies: VM runtime owners with parity review from bridge owners.
- Adequacy/bridge proofs: proof owners, with executable trace-surface sign-off from VM runtime owners.

## Executable vs Proof Separation Rule

- Executable modules must not depend on placeholder proof definitions.
- Proof-only placeholders stay isolated under proof modules.
- Any executable-path dependency on a stub/placeholder is a release blocker.

## Change Control

For any VM PR that changes public runtime behavior:

1. Update `docs/31_lean_rust_parity_matrix.md`.
2. Include parity impact statement in PR checklist.
3. Add/update differential tests when observable behavior changes.
