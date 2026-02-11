# VM Parity Failure Runbook

Use this when a parity/conformance check fails locally or in CI.

## Quick Triage

1. Run parity checker: `./scripts/check-parity-ledger.sh`.
2. Run canonical parity suite: `./scripts/check-vm-parity-suite.sh`.
3. Run VM parity tests: `cargo test -p telltale-vm --test flow_policy_serialization`.
4. Run targeted Lean VM build: `cd lean && lake build Runtime.VM.Model.Knowledge Runtime.VM.Semantics.ExecOwnership`.

## Determine Failure Class

- Encoding mismatch: enum/variant shape mismatch.
- Runtime behavior mismatch: trace/fault divergence.
- Unjustified break: mismatch exists without active ledger coverage.

## Resolution Path

1. If unintentional: align Lean/Rust code and update tests.
2. If intentional: add deviation ledger entry + justification template (with owner + revisit date).
3. Re-run affected test and conformance lanes.

## Evidence to Attach

- failing command output,
- changed parity matrix row,
- test(s) proving final behavior,
- deviation entry id (if applicable).
