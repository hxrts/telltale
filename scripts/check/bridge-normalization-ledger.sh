#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${ROOT_DIR}"

errors=()

cargo test -p telltale-bridge --lib bridge_normalization_contract_ -- --nocapture >/dev/null

mapfile -t injected_keys < <(
  sed -n 's/.*inject_field_if_missing([^,]*, "\([^"]*\)".*/\1/p' \
    rust/bridge/src/protocol_machine_runner_json_parsing.rs | sort -u
)
if [[ "${#injected_keys[@]}" -ne 1 || "${injected_keys[0]}" != "schema_version" ]]; then
  errors+=(
    "protocol_machine_runner_json_parsing.rs: schema-compatibility backfill must only inject schema_version, found [${injected_keys[*]:-}]"
  )
fi

if ! rg -q "## Bridge Normalization Trust Surface" docs/32_testing_verification_inventory.md; then
  errors+=(
    "docs/32_testing_verification_inventory.md: missing 'Bridge Normalization Trust Surface' section"
  )
fi

for needle in \
  "semantic-audit tick normalization" \
  "runner JSON schema backfill"
do
  if ! rg -q "${needle}" docs/32_testing_verification_inventory.md; then
    errors+=(
      "docs/32_testing_verification_inventory.md: missing bridge normalization ledger row for '${needle}'"
    )
  fi
done

for needle in \
  "irreducible trusted comparison logic" \
  "compatibility-only, removable by schema tightening"
do
  if ! rg -q "${needle}" docs/32_testing_verification_inventory.md; then
    errors+=(
      "docs/32_testing_verification_inventory.md: missing bridge normalization classification '${needle}'"
    )
  fi
done

if rg -q "session-status ordering" docs/32_testing_verification_inventory.md; then
  errors+=(
    "docs/32_testing_verification_inventory.md: session-status ordering should no longer be listed as trusted normalization"
  )
fi

if rg -q "fn normalized_session_statuses" rust/bridge/src/protocol_machine_runner.rs; then
  errors+=(
    "rust/bridge/src/protocol_machine_runner.rs: session-status comparison must be exact; normalized_session_statuses should not exist"
  )
fi

if ! rg -q "sortedSessionStatusesJson" lean/Runtime/Tests/ProtocolMachineRunner.lean; then
  errors+=(
    "lean/Runtime/Tests/ProtocolMachineRunner.lean: missing canonical source-side session-status ordering helper"
  )
fi

if [[ "${#errors[@]}" -gt 0 ]]; then
  printf 'bridge-normalization-ledger: found %d issue(s)\n' "${#errors[@]}" >&2
  for err in "${errors[@]}"; do
    printf '  - %s\n' "${err}" >&2
  done
  exit 1
fi

echo "bridge-normalization-ledger: ok"
