#!/usr/bin/env bash
# Keep authoritative durability artifacts on the machine/runtime side and out
# of helper-generated and viewer-only surfaces.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

if ! command -v rg >/dev/null 2>&1; then
  echo "error: ripgrep (rg) is required" >&2
  exit 2
fi

fail=0

check_no_hits() {
  local pattern="$1"
  shift
  local paths=("$@")
  local hits
  hits="$(rg -n "$pattern" "${paths[@]}" || true)"
  if [[ -n "$hits" ]]; then
    echo "durability boundary violation for pattern: $pattern" >&2
    echo "$hits" >&2
    fail=1
  fi
}

check_has_hits() {
  local pattern="$1"
  local path="$2"
  if ! rg -q "$pattern" "$path"; then
    echo "expected to find '$pattern' in $path" >&2
    fail=1
  fi
}

check_no_hits 'PersistedDurabilityArtifact|PersistedDurabilityPayload|AgreementWalArtifact|DurableRecoveryMetadata|EvidenceOutcomeCacheArtifact' \
  rust/simulator/src/generated.rs rust/viewer/src rust/ui/src rust/web/src
check_has_hits 'telltale_machine::model::durability' docs/901_api_reference.md
check_has_hits 'wal_sync' docs/802_rust_lean_parity.md
check_has_hits 'walSyncMetadata' lean/Runtime/ProtocolMachine/Model/Durability.lean
check_has_hits 'durableRecoveryDecision_gate_crossing_requires_recovered_agreement' lean/Runtime/Proofs/ProtocolMachine/Durability.lean
check_has_hits 'On-disk checkpoint and replay bundles now use the typed' docs/501_simulation_overview.md
check_has_hits 'Simulator reports and viewer projections should consume typed durable artifacts' docs/501_simulation_overview.md

if [[ "$fail" -ne 0 ]]; then
  exit 1
fi

echo "durable-boundaries: clean"
