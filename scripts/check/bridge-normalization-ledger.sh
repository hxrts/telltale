#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${ROOT_DIR}"

STRICT_TMPDIR="${ROOT_DIR}/.tmp/bridge-normalization"
mkdir -p "${STRICT_TMPDIR}"

if [[ -n "${TMPDIR:-}" && ! -d "${TMPDIR}" ]]; then
  export TMPDIR="${STRICT_TMPDIR}"
else
  export TMPDIR="${TMPDIR:-${STRICT_TMPDIR}}"
fi

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

if ! rg -q '#\[cfg\(test\)\]\s*fn inject_field_if_missing' -U \
  rust/bridge/src/protocol_machine_runner_json_parsing.rs; then
  errors+=(
    "rust/bridge/src/protocol_machine_runner_json_parsing.rs: schema backfill helper must be test-only"
  )
fi

if ! rg -q '#\[cfg\(test\)\]\s*fn backfill_protocol_machine_run_output_schema_versions' -U \
  rust/bridge/src/protocol_machine_runner_json_parsing.rs; then
  errors+=(
    "rust/bridge/src/protocol_machine_runner_json_parsing.rs: schema-version backfill must be test-only"
  )
fi

if ! rg -q '#\[cfg\(test\)\]\s*pub\(super\) fn parse_protocol_machine_run_output_with_schema_backfill' -U \
  rust/bridge/src/protocol_machine_runner_json_parsing.rs; then
  errors+=(
    "rust/bridge/src/protocol_machine_runner_json_parsing.rs: compatibility parser must be test-only"
  )
fi

if ! rg -q "parse_protocol_machine_run_output_strict" rust/bridge/src/protocol_machine_runner.rs; then
  errors+=(
    "rust/bridge/src/protocol_machine_runner.rs: strict runner path must use parse_protocol_machine_run_output_strict"
  )
fi

if ! rg -q "## Bridge Normalization Trust Surface" docs/806_verification_inventory.md; then
  errors+=(
    "docs/806_verification_inventory.md: missing 'Bridge Normalization Trust Surface' section"
  )
fi

for needle in \
  "semantic-audit tick normalization"
do
  if ! rg -q "${needle}" docs/806_verification_inventory.md; then
    errors+=(
      "docs/806_verification_inventory.md: missing bridge normalization ledger row for '${needle}'"
    )
  fi
done

for needle in \
  "irreducible trusted comparison logic"
do
  if ! rg -q "${needle}" docs/806_verification_inventory.md; then
    errors+=(
      "docs/806_verification_inventory.md: missing bridge normalization classification '${needle}'"
    )
  fi
done

if rg -q '^\| runner JSON schema backfill \|' docs/806_verification_inventory.md; then
  errors+=(
    "docs/806_verification_inventory.md: compatibility-only schema backfill must stay outside the trusted bridge ledger"
  )
fi

if rg -q "session-status ordering" docs/806_verification_inventory.md; then
  errors+=(
    "docs/806_verification_inventory.md: session-status ordering should no longer be listed as trusted normalization"
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
