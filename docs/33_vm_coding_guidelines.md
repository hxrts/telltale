# VM Coding Guidelines (Parity-Oriented)

## Rule 1: Encoding Parity Is Default

- Keep Lean and Rust data/policy encodings aligned by default.
- If you diverge, document it as a justified break before merge.

## Rule 2: Abstraction Is Allowed Only Behind Stable Surfaces

- Internal refactors are allowed when externally observable behavior and encoding stay the same.
- Avoid introducing abstraction layers that hide parity-relevant behavior.

## Rule 3: Deterministic Defaults

- Optional hooks require deterministic defaults.
- New config fields must define explicit defaults and schema impact.

## Rule 4: Executable/Proof Separation

- Executable VM paths may not rely on proof placeholders or stubs.
- Keep proof-only assumptions isolated and clearly named.

## Rule 5: Test Gating

- Add differential or conformance tests for any behavior change.
- Prefer tests that expose observable trace/fault differences.
