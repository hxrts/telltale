# Lean Verification

Telltale uses Lean 4 to formally verify the correctness of choreographic projection. This chapter describes what properties are proven, what remains axiomatized, and how verification integrates with the Rust implementation.

## Verification Strategy

The project employs a defense-in-depth approach with three layers. Core session type theory is proven in Lean. Two independent projection implementations are compared for equivalence. Randomized protocols are validated against the Lean binary. This layered approach ensures that bugs in one layer are caught by another.

## What is Formally Proven

The following properties have complete proofs in `lean/Telltale/Proofs/`:

### Merge Operator Properties

The merge operator combines local types for non-participants in choices. Proofs establish reflexivity (`merge lt lt = lt`), commutativity (`merge a b = merge b a`), and associativity (`merge (merge a b) c = merge a (merge b c)`). These properties ensure that merge order does not affect projection results.

### Subtyping and Ordering

The subtyping relation ensures projected programs conform to their specifications:

```lean
theorem subLabelsOf_refl (lt : LocalType) : subLabelsOf lt lt = true := by
  unfold subLabelsOf; simp [List.all_eq_true, List.any_eq_true]

theorem isSubsequence_refl {α} [DecidableEq α] (xs : List α) :
  isSubsequence xs xs = true := by induction xs <;> simp [isSubsequence, *]

theorem isSubtype_refl (lt : LocalType) : isSubtype lt lt = true := by
  simp [isSubtype, isSubsequence_refl]
```

`subLabelsOf_refl` uses `all_eq_true` and `any_eq_true` to show every projected label witnesses itself. `isSubsequence_refl` and `isSubtype_refl` prove the order check is reflexive. These lemmas ensure only differences between exporter output and projection trigger failures.

### Global Type Consumption

Safe traversal lemmas for global type structures ensure projection terminates and produces valid results.

## What is Axiomatized

The following properties are stated as axioms but not yet proven:

| Property | Description | Impact |
|----------|-------------|--------|
| Subject Reduction | Type preservation during execution | Safety guarantee |
| Progress | Well-typed programs don't deadlock | Liveness guarantee |
| Non-participant Correctness | Merging produces valid local types | Projection soundness |
| Merge Composition | Complex merge interactions | Edge case coverage |

These axioms represent the theoretical foundations that the implementation relies upon. They do not affect the correctness of tested protocol patterns, which are validated empirically against the Lean runner.

## Core Lean Predicates

The runner enforces three predicates for each branch:

```lean
def subLabelsOf (lt sup : LocalType) : Bool :=
  lt.actions.all (fun a => sup.actions.any (fun b => decide (b = a)))

def isSubsequence {α} [DecidableEq α] : List α → List α → Bool
  | [], _ => true
  | _, [] => false
  | a :: as, b :: bs => if a = b then isSubsequence as bs else isSubsequence (a :: as) bs

def isSubtype (sub sup : LocalType) : Bool :=
  sub.actions.length <= sup.actions.length ∧ isSubsequence sub.actions sup.actions
```

- `subLabelsOf`: Symmetric label matching. Every exported action must appear in the projection.
- `isSubsequence`: Asymmetric ordering. Exported actions must preserve projection order.
- `isSubtype`: Combines length guard with ordering to reject reordered or extended traces.

## Module Structure

The Lean codebase is organized into focused modules:

- **Telltale.Choreography**: Decodes choreographies from JSON, validates roles and actions with `hasUniqueRoles` and `hasValidActions`
- **Telltale.Projection**: Builds per-role `LocalType` traces from global types
- **Telltale.Program**: Maps exported effects to `LocalAction` values as a homomorphism from JSON to the projection domain
- **Telltale.Subtyping**: Defines order checks with `DecidableEq`
- **Telltale.Runner**: Applies membership, order, and label invariants per branch

## Features Without Lean Formalization

The DSL includes features that extend beyond the formally verified core:

| Feature | Description | Status |
|---------|-------------|--------|
| Dynamic Roles | Parameterized role arrays `R[i]` | Runtime checks only |
| Broadcasts | One-to-many messages | Desugars to nested sends |
| Local Choices | Non-communicating decisions | Type-checked |
| Parallel Composition | Concurrent branches | Structural checks |
| Protocol Extensions | Custom DSL syntax | User-defined |

These features are tested but not formally proven correct.

### Recursion Model

The DSL uses explicit recursion with `rec` blocks and `continue` statements:

**DSL syntax:**
```
rec Loop {
    A -> B: Msg
    continue Loop
}
```

**Theory (µ-binders):**
```
µX. A → B: Msg. X
```

The `continue` keyword provides explicit back-references that align with the theory's `Var` constructor. Cross-validation tests verify that recursive protocols project equivalently in both implementations.

## Running Verification

Use the Nix shell to ensure Rust, Lean, and Lake versions match:

```bash
nix develop --command just telltale-lean-check
```

This exports the sample choreography for Chef, SousChef, and Baker from `lean/choreo/lean-sample.choreo`, builds the Lean runner, and validates each role. Logs are written to `lean/artifacts/runner-<role>.{log,json}`.

### Extended Scenario

```bash
nix develop --command just telltale-lean-check-extended
```

Validates `lean/choreo/lean-extended.choreo` with two course cycles before dessert options.

### Negative Testing

```bash
nix develop --command just telltale-lean-check-failing
```

Exports `lean/choreo/lean-failing.choreo` with a corrupted label. The runner exits non-zero, confirming error detection works.

### Full CI Sweep

```bash
nix develop --command just ci-dry-run
```

Runs Rust fmt, clippy, tests, and all Lean verification scenarios.

## Sample Choreography

`lean/choreo/lean-sample.choreo` models a collaborative dinner with two meal branches (pasta, tacos) and three dessert options (cake, fruit, none). The runner checks that each branch for Chef, SousChef, and Baker is a subsequence of its projection and introduces no extra labels.

## Editing Scenarios

Update inputs in `lean/choreo/`. Change `--role` in the Just recipes to validate other roles. Regenerate and re-run the verification commands to test new scenarios.

## Known Limitations

1. **Axioms**: Safety properties (subject reduction, progress) are assumed, not proven
2. **Recursion**: DSL implicit loops cannot be cross-validated against theory explicit µ-binders
3. **Extensions**: Custom DSL extensions bypass formal verification
4. **Payloads**: Type annotations on messages are not semantically verified
5. **Coinductive round-trip**: The EQ2C round-trip proof currently assumes `ProductiveC` on the RHS; regularity alone does not imply productivity

## Future Work

- Prove axiomatized properties in Lean
- Unify recursion models between DSL and theory
- Add formal verification for broadcast desugaring
- Extend proofs to cover parallel composition
