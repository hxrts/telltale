# Choreography Parity

This document defines the Rust and Lean parity contract for choreography projection behavior.
It applies to the shared projection and merge semantics over the common type subset.

## Scope

The parity scope covers projection behavior from global choreography forms to local session forms.
It covers `send`, `choice`, recursion, and merge behavior for non-participant branches.
It does not cover Rust-only runtime conveniences or extension-only AST constructs.

## Shared Semantics

Rust and Lean are expected to align on the following surfaces.

| Area | Lean Surface | Rust Surface | Status |
|---|---|---|---|
| Projection core relation | `lean/Choreography/Projection/Project.lean` | `rust/choreography/src/compiler/projection.rs` | Aligned on supported subset |
| Merge semantics | `lean/Choreography/Projection/Erasure/Merge.lean` | `rust/choreography/src/compiler/projection/merge.rs` | Aligned |
| Projection validation pipeline | `lean/Choreography/Projection/Validator.lean` | `rust/lean-bridge/src/runner_projection_export.rs` | Aligned |

## Rust-Only Extensions

The following surfaces are intentionally outside direct Lean parity.
They must be documented as extensions and must not be confused with theorem-backed projection claims.

| Surface | Rust Module | Parity Status |
|---|---|---|
| `LocalType::LocalChoice` | `rust/choreography/src/ast/local_type.rs` | Rust extension |
| Timeout wrappers in local AST | `rust/choreography/src/ast/local_type.rs` | Rust extension |
| Effect runtime `Parallel` execution contract | `rust/choreography/src/effects/interpreter.rs` | Rust runtime contract |

## Cross-Validation

Projection cross-validation is exercised through `rust/lean-bridge/tests/projection_runner_tests.rs`.
Tests skip per test when the Lean validator binary is unavailable.
Skipping one test must not terminate the rest of the suite.

## Update Rule

Any Rust PR that changes projection or merge semantics must include:

1. The affected Rust module list.
2. The Lean module list reviewed for parity.
3. New or updated cross-validation tests for the changed behavior.
4. A parity note update in this document when scope or status changes.
