#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${ROOT_DIR}"

require_command() {
  command -v "$1" >/dev/null 2>&1 || {
    echo "error: $1 is required" >&2
    exit 2
  }
}

require_command python3
require_command rg

tmpdir="$(mktemp -d)"
restore_entries=()

cleanup() {
  local entry path backup
  for entry in "${restore_entries[@]}"; do
    path="${entry%%:*}"
    backup="${entry#*:}"
    if [[ -f "${backup}" ]]; then
      cp "${backup}" "${path}"
    fi
  done
  rm -f rust/runtime/src/__phase10_package_resource_probe.rs
  rm -rf "${tmpdir}"
}
trap cleanup EXIT

backup_file() {
  local path="$1"
  local backup="${tmpdir}/$(echo "${path}" | tr '/.' '__')"
  cp "${path}" "${backup}"
  restore_entries+=("${path}:${backup}")
  echo "${backup}"
}

restore_now() {
  local path="$1"
  local backup="$2"
  cp "${backup}" "${path}"
}

replace_once() {
  local path="$1"
  local old="$2"
  local new="$3"
  python3 - "$path" "$old" "$new" <<'PY'
from pathlib import Path
import sys

path = Path(sys.argv[1])
old = sys.argv[2]
new = sys.argv[3]
text = path.read_text()
if old not in text:
    raise SystemExit(f"missing mutation target in {path}: {old}")
path.write_text(text.replace(old, new, 1))
PY
}

assert_gate_fails() {
  local label="$1"
  local expected="$2"
  shift 2
  local output="${tmpdir}/$(echo "${label}" | tr ' /' '__').log"
  if "$@" >"${output}" 2>&1; then
    echo "error: expected ${label} to fail closed" >&2
    cat "${output}" >&2
    exit 1
  fi
  if ! grep -Fq "${expected}" "${output}"; then
    echo "error: ${label} failed, but not with the expected diagnostic" >&2
    echo "expected substring: ${expected}" >&2
    cat "${output}" >&2
    exit 1
  fi
}

# Mutation ledger:
# - bridge normalization ledger drift should be rejected by bridge-normalization-ledger.sh
# - verification inventory metric drift should be rejected by verification-inventory.sh
# - release package registry drift should be rejected by release-recovery.sh
# - package resource escapes should be rejected by package-resource-audit.sh

doc_backup="$(backup_file docs/32_testing_verification_inventory.md)"
replace_once \
  docs/32_testing_verification_inventory.md \
  "semantic-audit tick normalization" \
  "semantic-audit tick mutation"
assert_gate_fails \
  "bridge normalization ledger mutation" \
  "missing bridge normalization ledger row for 'semantic-audit tick normalization'" \
  ./scripts/check/bridge-normalization-ledger.sh
restore_now docs/32_testing_verification_inventory.md "${doc_backup}"

replace_once \
  docs/32_testing_verification_inventory.md \
  "| Handler contract boundary assurance suites | 1 |" \
  "| Handler contract boundary assurance suites | 999 |"
assert_gate_fails \
  "verification inventory metric mutation" \
  'metric `Handler contract boundary assurance suites` documents 999 but actual is 1' \
  ./scripts/check/verification-inventory.sh
restore_now docs/32_testing_verification_inventory.md "${doc_backup}"

cat > rust/runtime/src/__phase10_package_resource_probe.rs <<'EOF'
const _: &str = include_str!("../Cargo.toml");
EOF
assert_gate_fails \
  "package resource escape mutation" \
  "telltale-runtime: package resource embed escapes crate root" \
  ./scripts/check/package-resource-audit.sh
rm -f rust/runtime/src/__phase10_package_resource_probe.rs

release_packages_backup="$(backup_file scripts/lib/release-packages.sh)"
replace_once \
  scripts/lib/release-packages.sh \
  $'RELEASE_PACKAGES=(\n' \
  $'RELEASE_PACKAGES=(\n  "telltale-phase10-missing"\n'
assert_gate_fails \
  "release package registry mutation" \
  "unknown package: telltale-phase10-missing" \
  ./scripts/check/release-recovery.sh
restore_now scripts/lib/release-packages.sh "${release_packages_backup}"

echo "fail-closed-mutations: ok"
