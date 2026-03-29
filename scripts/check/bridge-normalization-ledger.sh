#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${ROOT_DIR}"

errors=()

extract_struct_fields() {
  local file="$1"
  local struct="$2"
  awk -v struct="$struct" '
    $0 ~ "pub struct " struct { in_struct=1; next }
    in_struct && /^[[:space:]]*}/ { exit }
    in_struct && /^[[:space:]]*pub[[:space:]]+[A-Za-z0-9_]+:/ {
      field=$2
      sub(/:/, "", field)
      print field
    }
  ' "$file"
}

compare_field_set() {
  local name="$1"
  shift
  local actual=("$@")
  local expected_var="${name}_expected[@]"
  local expected=("${!expected_var}")

  local actual_sorted expected_sorted
  actual_sorted="$(printf '%s\n' "${actual[@]}" | sort)"
  expected_sorted="$(printf '%s\n' "${expected[@]}" | sort)"
  if [[ "${actual_sorted}" != "${expected_sorted}" ]]; then
    errors+=("${name}: expected field set [${expected[*]}] but found [${actual[*]}]")
  fi
}

trace_fields_expected=(
  schema_version
  kind
  tick
  session
  sender
  receiver
  label
  role
  target
  permitted
  epoch
  ghost
  from
  to
  predicate_ref
  witness_ref
  output_digest
  passed
  reason
)

session_status_fields_expected=(
  schema_version
  sid
  terminal
)

mapfile -t trace_fields < <(
  extract_struct_fields rust/bridge/src/protocol_machine_runner.rs ProtocolMachineTraceEvent
)
mapfile -t session_status_fields < <(
  extract_struct_fields rust/bridge/src/protocol_machine_runner.rs ProtocolMachineSessionStatus
)

compare_field_set trace_fields "${trace_fields[@]}"
compare_field_set session_status_fields "${session_status_fields[@]}"

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
  "session-status ordering" \
  "runner JSON schema backfill"
do
  if ! rg -q "${needle}" docs/32_testing_verification_inventory.md; then
    errors+=(
      "docs/32_testing_verification_inventory.md: missing bridge normalization ledger row for '${needle}'"
    )
  fi
done

if [[ "${#errors[@]}" -gt 0 ]]; then
  printf 'bridge-normalization-ledger: found %d issue(s)\n' "${#errors[@]}" >&2
  for err in "${errors[@]}"; do
    printf '  - %s\n' "${err}" >&2
  done
  exit 1
fi

echo "bridge-normalization-ledger: ok"
