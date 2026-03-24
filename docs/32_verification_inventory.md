# Verification Inventory

This page is the authoritative inventory for verification counts.
Only counts that are stable enough to check automatically are tracked here.

When one of these values changes legitimately:

1. update the underlying source of truth,
2. refresh this page,
3. rerun `just check-verification-inventory`.

| Metric | Value | Source |
|---|---:|---|
| Lean core-library files | 631 | `lean/CODE_MAP.md` total row |
| Lean core-library lines | 129,638 | `lean/CODE_MAP.md` total row |
| Ownership contract gate commands | 6 | `just check-ownership-contracts` |
| Aura-derived boundary checks | 6 | `just check-aura-borrowed-lints` |
| Explicit failure/timeout observable event kinds | 5 | `rust/machine/src/vm/vm_config.rs` (`ObsEvent`) |
| Macro UI pass fixtures | 2 | `rust/macros/tests/macro_ui.rs` |
| Macro UI compile-fail fixtures | 6 | `rust/macros/tests/macro_ui.rs` |
