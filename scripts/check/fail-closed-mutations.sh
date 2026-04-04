#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${ROOT_DIR}"
mkdir -p "${ROOT_DIR}/.tmp"

require_command() {
  command -v "$1" >/dev/null 2>&1 || {
    echo "error: $1 is required" >&2
    exit 2
  }
}

require_command python3
require_command rg

tmpdir="$(mktemp -d "${ROOT_DIR}/.tmp/fail-closed-mutations.XXXXXX")"
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
# - source-derived capability/authority docs drift should be rejected by docs-as-contract.sh
# - verification inventory metric drift should be rejected by verification-inventory.sh
# - package manifest resource drift should be rejected by package-artifacts.sh
# - release package registry drift should be rejected by release-recovery.sh
# - package resource escapes should be rejected by package-resource-audit.sh

doc_backup="$(backup_file docs/902_verification_inventory.md)"
replace_once \
  docs/902_verification_inventory.md \
  "semantic-audit tick normalization" \
  "semantic-audit tick mutation"
assert_gate_fails \
  "bridge normalization ledger mutation" \
  "missing bridge normalization ledger row for 'semantic-audit tick normalization'" \
  ./scripts/check/bridge-normalization-ledger.sh
restore_now docs/902_verification_inventory.md "${doc_backup}"

admission_doc_backup="$(backup_file docs/702_capability_admission.md)"
replace_once \
  docs/702_capability_admission.md \
  '| `protocol_envelope_bridge` |' \
  '| `phase16_mutation_boundary` |'
assert_gate_fails \
  "capability admission docs row mutation" \
  "missing expected docs row:" \
  ./scripts/check/docs-as-contract.sh
restore_now docs/702_capability_admission.md "${admission_doc_backup}"

authority_doc_backup="$(backup_file docs/703_authority_language_surface.md)"
replace_once \
  docs/703_authority_language_surface.md \
  '| `par` with observational binding |' \
  '| `phase16_parallel_mutation` |'
assert_gate_fails \
  "authority language docs row mutation" \
  "missing expected docs row:" \
  ./scripts/check/docs-as-contract.sh
restore_now docs/703_authority_language_surface.md "${authority_doc_backup}"

replace_once \
  docs/902_verification_inventory.md \
  "| Handler contract boundary assurance suites | 2 |" \
  "| Handler contract boundary assurance suites | 999 |"
assert_gate_fails \
  "verification inventory metric mutation" \
  'metric `Handler contract boundary assurance suites` documents 999 but actual is 2' \
  ./scripts/check/verification-inventory.sh
restore_now docs/902_verification_inventory.md "${doc_backup}"

cat > rust/runtime/src/__phase10_package_resource_probe.rs <<'EOF'
const _: &str = include_str!("../Cargo.toml");
EOF
assert_gate_fails \
  "package resource escape mutation" \
  "telltale-runtime: package resource embed escapes crate root" \
  ./scripts/check/package-resource-audit.sh
rm -f rust/runtime/src/__phase10_package_resource_probe.rs

runtime_manifest_backup="$(backup_file rust/runtime/Cargo.toml)"
replace_once \
  rust/runtime/Cargo.toml \
  'readme = "../../README.md"' \
  'readme = "../../PHASE16_MISSING_README.md"'
assert_gate_fails \
  "package manifest readme mutation" \
  "error: telltale-runtime: manifest readme path missing: ../../PHASE16_MISSING_README.md" \
  ./scripts/check/package-artifacts.sh
restore_now rust/runtime/Cargo.toml "${runtime_manifest_backup}"

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
