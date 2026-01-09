# Bug Report: Message Type Names in BranchLabel Enum

**Status:** ✅ FIXED
**Version:** rumpsteak-aura v0.8.1, rumpsteak-aura-choreography v0.8.1
**Severity:** High - Causes compilation errors in generated code (WAS causing - now fixed)
**Location:** `rust/choreography/src/compiler/projection.rs` (fixed)

## Summary

When choreography projection merges multiple Receive operations with different message types, it incorrectly creates `LocalType::Branch` nodes using **message type names** as branch labels instead of semantic choice labels. This causes the generated `BranchLabel` enum to contain message type names, resulting in non-exhaustive pattern match errors.

## Root Cause

In `rust/choreography/src/compiler/projection.rs`, the `merge_local_types` function handles merging two Receive operations from the same sender with different messages by creating a Branch:

```rust
// Lines 725-733
// Different messages - create a Branch with both options
Ok(LocalType::Branch {
    from: from1.clone(),
    branches: vec![
        (msg1.name.clone(), *cont1.clone()),  // ❌ BUG: message name as label
        (msg2.name.clone(), *cont2.clone()),  // ❌ BUG: message name as label
    ],
})
```

**Problem:** Branch labels should be **semantic choice labels** (e.g., "finalize", "cancel"), not **message wrapper type names** (e.g., "CommitCeremony", "AbortCeremony").

## Impact

### User-Reported Example

```choreo
case choose Initiator of
  finalize ->
    Initiator -> Guardian1 : CommitCeremony(...)
  cancel ->
    Initiator -> Guardian1 : AbortCeremony(...)
```

**Expected BranchLabel:**
```rust
pub enum BranchLabel {
    finalize,
    cancel,
}
```

**Actual BranchLabel (BUGGY):**
```rust
pub enum BranchLabel {
    AbortCeremony,    // ❌ Message type - should NOT be here
    CommitCeremony,   // ❌ Message type - should NOT be here
    cancel,           // ✅ Correct branch label
    finalize,         // ✅ Correct branch label
}
```

This causes **non-exhaustive pattern match errors** because code generated for the choice expects only 2 variants but the enum has 4.

## Regression Tests

Three regression tests have been added to `rust/choreography/tests/runner_codegen_tests.rs`:

### 1. `test_branch_label_excludes_message_type_names_simple`

Tests the simple case (which does NOT trigger the bug). Demonstrates that straightforward Select/Branch projection works correctly.

**Result:** ✅ PASS - Shows the bug is specific to merge operations

### 2. `test_merge_creates_branch_with_message_names_bug`

Directly tests the `merge_local_types` function with two Receive operations having different messages.

**Result:** ✅ CONFIRMS BUG

**Output:**
```
Merged branches:
  - CommitCeremony
  - AbortCeremony

BUG CONFIRMED: merge_local_types created Branch with message type names as labels.
Expected: Branch labels should be semantic choice labels
Actual: Branch labels are message type names: ["CommitCeremony", "AbortCeremony"]
```

### 3. `test_message_names_pollute_branch_label_enum`

Integration test showing the full impact - buggy Branch nodes pollute the generated `BranchLabel` enum.

**Result:** ✅ CONFIRMS BUG

**Output:**
```
Generated BranchLabel enum (BUGGY):
pub enum BranchLabel { AbortCeremony , CommitCeremony }

⚠️  BUG CONFIRMED: BranchLabel enum incorrectly contains message type names.
```

## Running the Tests

```bash
cd rust/choreography

# Run all regression tests
cargo test --test runner_codegen_tests -- --nocapture

# Run specific bug confirmation tests
cargo test --test runner_codegen_tests test_merge_creates_branch_with_message_names_bug -- --nocapture
cargo test --test runner_codegen_tests test_message_names_pollute_branch_label_enum -- --nocapture
```

## Fix Strategy

The merge logic should NOT create Branch nodes using message names as labels. Possible fixes:

1. **Don't create Branch nodes during merge** - If the receives are on parallel paths, they shouldn't be merged into a Branch
2. **Preserve original semantic labels** - Track choice labels through projection and use them instead of message names
3. **Error on ambiguous protocols** - Raise an error if the protocol structure requires merging incompatible receives

The correct fix depends on the intended semantics of the choreography DSL for parallel/merged operations.

## Related Code

- Bug location: `rust/choreography/src/compiler/projection.rs:725-733`
- Also affected: Lines 749-750 (similar pattern in another merge case)
- Label collection: `rust/choreography/src/compiler/runner.rs:1035-1060` (collect_branch_labels)
- Enum generation: `rust/choreography/src/compiler/runner.rs:1062-1116` (generate_branch_label_enum)

## Fix Implementation

The bug was fixed by implementing label-aware merging for choice continuations:

1. **Modified `merge_choice_continuations`** (line 596): Now preserves branch labels from the Choice construct and bundles them with projected local types.

2. **Added `LabeledLocalType` struct**: Pairs a `LocalType` with its choice label (`Ident`).

3. **Added `merge_labeled_local_types` function**: Label-aware merge that uses semantic choice labels when creating Branch nodes, not message type names.

4. **Updated `merge_local_types` function**: Now returns an error when attempting to merge Receives with different messages without label information, making the bug structurally impossible.

The fix ensures that:
- Choice labels flow through the merge process
- Branch nodes use semantic labels ("finalize", "cancel") not message names ("CommitCeremony", "AbortCeremony")
- The unlabeled merge function errors on ambiguous operations, forcing use of labeled merging for choices
- BranchLabel enum contains only semantic choice labels

## Test Results

All regression tests pass:
- `test_branch_label_excludes_message_type_names_simple`: Verifies simple case works correctly
- `test_merge_rejects_different_receives_without_labels`: Verifies merge correctly errors without labels
- `test_merge_fix_prevents_branch_label_pollution`: Integration test verifying fix prevents enum pollution

Full test suite: 64 tests passed, 0 failed
