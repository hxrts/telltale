#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${ROOT_DIR}"

source "${ROOT_DIR}/scripts/lib/release-packages.sh"

require_command() {
  command -v "$1" >/dev/null 2>&1 || {
    echo "error: $1 is required" >&2
    exit 2
  }
}

require_command rg

errors=()

audit_dir() {
  local package="$1"
  local manifest
  manifest="$(manifest_path "${package}")"
  dirname "${manifest}"
}

for package in "${RELEASE_PACKAGES[@]}"; do
  crate_dir="$(audit_dir "${package}")"
  if [[ ! -d "${crate_dir}" ]]; then
    continue
  fi

  while IFS= read -r match; do
    errors+=("${package}: package resource embed escapes crate root via ${match}")
  done < <(
    rg -n 'include_(str|bytes)!\("(\.\./|..\\\\)' \
      "${crate_dir}/src" "${crate_dir}/examples" "${crate_dir}/benches" "${crate_dir}/build.rs" \
      2>/dev/null || true
  )

  while IFS= read -r match; do
    errors+=("${package}: package runtime file lookup escapes crate root via ${match}")
  done < <(
    rg -n -U 'env!\("CARGO_MANIFEST_DIR"\)(.|\n){0,200}\.join\("(\.\./|..\\\\)' \
      "${crate_dir}/src" "${crate_dir}/examples" "${crate_dir}/benches" "${crate_dir}/build.rs" \
      2>/dev/null || true
  )

  while IFS= read -r match; do
    errors+=("${package}: package runtime file lookup escapes crate root via ${match}")
  done < <(
    rg -n -U 'Path(Buf)?::from\(env!\("CARGO_MANIFEST_DIR"\)\)(.|\n){0,200}\.join\("(\.\./|..\\\\)' \
      "${crate_dir}/src" "${crate_dir}/examples" "${crate_dir}/benches" "${crate_dir}/build.rs" \
      2>/dev/null || true
  )
done

if [[ "${#errors[@]}" -gt 0 ]]; then
  printf 'package-resource-audit: found %d issue(s)\n' "${#errors[@]}" >&2
  for err in "${errors[@]}"; do
    printf '  - %s\n' "${err}" >&2
  done
  exit 1
fi

echo "package-resource-audit: ok"
