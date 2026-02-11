# VM Parity Contract

This document defines the Lean/Rust parity contract for VM policy and data encodings.

## Policy

- **Default rule**: Lean and Rust use the same shape and naming for VM policy/data encodings.
- **Project policy**: **spec-first for shape, runtime-first for justified execution details**.
- Any mismatch must be an explicit justified break, recorded before merge.

## Canonical Encodings

### Flow Policy

- Lean: `lean/Runtime/VM/Model/Knowledge.lean`
  - `FlowPolicy.allowAll`
  - `FlowPolicy.denyAll`
  - `FlowPolicy.allowRoles`
  - `FlowPolicy.denyRoles`
  - `FlowPolicy.predicate` (runtime closure; not serializable)
  - `FlowPolicy.predicateExpr`
- Rust: `rust/vm/src/vm.rs`
  - `FlowPolicy::AllowAll`
  - `FlowPolicy::DenyAll`
  - `FlowPolicy::AllowRoles`
  - `FlowPolicy::DenyRoles`
  - `FlowPolicy::Predicate` (runtime closure; not serializable)
  - `FlowPolicy::PredicateExpr`

### Flow Predicate

- Lean: `FlowPredicate.targetRolePrefix`, `factContains`, `endpointRoleMatchesTarget`, `all`, `any`
- Rust: `FlowPredicate::TargetRolePrefix`, `FactContains`, `EndpointRoleMatchesTarget`, `All`, `Any`

### Output-Condition Policy

- Lean: `lean/Runtime/VM/Model/OutputCondition.lean`
  - `OutputConditionPolicy.disabled`
  - `OutputConditionPolicy.allowAll`
  - `OutputConditionPolicy.denyAll`
  - `OutputConditionPolicy.predicateAllowList`
- Rust: `rust/vm/src/output_condition.rs`
  - `OutputConditionPolicy::Disabled`
  - `OutputConditionPolicy::AllowAll`
  - `OutputConditionPolicy::DenyAll`
  - `OutputConditionPolicy::PredicateAllowList`

### Core Runtime Values

- Lean: `lean/Protocol/Values.lean`
  - `Value.unit`
  - `Value.bool`
  - `Value.nat`
  - `Value.string`
  - `Value.prod`
  - `Value.chan`
- Rust: `rust/vm/src/coroutine.rs`
  - `Value::Unit`
  - `Value::Bool`
  - `Value::Nat`
  - `Value::Str`
  - `Value::Prod`
  - `Value::Endpoint`

### Progress Tokens

- Lean: `lean/Runtime/VM/Model/State.lean`
  - `ProgressToken.sid`
  - `ProgressToken.endpoint`
- Rust: `rust/vm/src/coroutine.rs`
  - `ProgressToken.sid`
  - `ProgressToken.endpoint`

### Output-Condition Claim/Check Metadata

- Lean `OutputConditionClaim`: `predicateRef`, `witnessRef`, `outputDigest : String`.
- Rust `OutputConditionMeta`: `predicate_ref`, `witness_ref`, `output_digest : String`.
- Default observable predicate ref in both runtimes: `vm.observable_output`.

### Default Predicate Reference

- Canonical default predicate ref for observable output checks: `vm.observable_output`.

### Output Digest Strategy

- Canonical representation is an opaque **string digest**.
- Current Lean executable path uses deterministic placeholder `"vm.output_digest.unspecified"` until full digest parity is wired.

## Serialization Rule

- Runtime closure flow predicates are intentionally non-serializable.
- Serializable interchange shape is `FlowPolicyRepr`/`FlowPredicate` (Lean) and `FlowPolicyRepr`/`FlowPredicate` (Rust).

## Justified Break Process

1. Add a deviation entry in `docs/lean_vs_rust_deviations.json`.
2. Fill the template in `docs/templates/justified_break.md`.
3. Assign an explicit owner and revisit date.
4. Include mismatch fingerprints under `covers`.

## CI Enforcement

- CI runs `scripts/check-parity-ledger.sh`.
- The check compares selected Lean/Rust policy/data shapes and fails when an uncovered mismatch appears.
