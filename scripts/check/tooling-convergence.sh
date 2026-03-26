#!/usr/bin/env bash
# Check that examples, docs, and tooling stay aligned with the canonical public
# protocol-machine and generated-effect surfaces.
set -euo pipefail

cd "$(dirname "$0")/../.."

MANIFEST="rust/machine/tests/support/tooling_convergence_manifest.rs"

# ── Helpers ───────────────────────────────────────────────────────────

fail() {
  echo "tooling-convergence: $1" >&2
  exit 1
}

# Assert that a ripgrep pattern has zero matches in the given paths
check_no_match() {
  local pattern="$1"
  shift
  if rg -n "$pattern" "$@" -g '!target' >/tmp/telltale_tooling_convergence.$$ 2>/dev/null; then
    cat /tmp/telltale_tooling_convergence.$$ >&2
    rm -f /tmp/telltale_tooling_convergence.$$
    fail "found forbidden pattern: $pattern"
  fi
  rm -f /tmp/telltale_tooling_convergence.$$
}

normalize_manifest_path() {
  local path="$1"
  case "${path}" in
    ../../../*)
      echo "${path#../../../}"
      ;;
    ../../choreography/*)
      echo "rust/choreography/${path#../../choreography/}"
      ;;
    ../../runtime/*)
      echo "rust/runtime/${path#../../runtime/}"
      ;;
    ../examples/*)
      echo "rust/machine/examples/${path#../examples/}"
      ;;
    ../benches/*)
      echo "rust/machine/benches/${path#../benches/}"
      ;;
    *)
      fail "unsupported manifest path mapping: ${path}"
      ;;
  esac
}

parse_manifest_expectations() {
  awk '
    /const REQUIRED_PATTERNS/ { section = "required"; next }
    /const FORBIDDEN_PATTERNS/ { section = "forbidden"; next }
    section != "" {
      if ($0 ~ /^[[:space:]]*];/) {
        section = ""
        pending_pattern = 0
        next
      }
      if ($0 ~ /path:[[:space:]]*"/) {
        line = $0
        sub(/^.*path:[[:space:]]*"/, "", line)
        sub(/".*$/, "", line)
        path = line
        next
      }
      if ($0 ~ /pattern:[[:space:]]*"/) {
        line = $0
        sub(/^.*pattern:[[:space:]]*"/, "", line)
        sub(/".*$/, "", line)
        printf "%s\t%s\t%s\n", section, path, line
        path = ""
        next
      }
      if ($0 ~ /pattern:[[:space:]]*$/) {
        pending_pattern = 1
        next
      }
      if (pending_pattern && $0 ~ /^[[:space:]]*"/) {
        line = $0
        sub(/^[[:space:]]*"/, "", line)
        sub(/".*$/, "", line)
        printf "%s\t%s\t%s\n", section, path, line
        path = ""
        pending_pattern = 0
      }
    }
  ' "${MANIFEST}"
}

check_manifest_expectations() {
  local violations=0
  local kind=""
  local path=""
  local pattern=""

  while IFS=$'\t' read -r kind path pattern; do
    [[ -n "${kind}" ]] || continue

    local resolved_path
    resolved_path="$(normalize_manifest_path "${path}")"
    if [[ ! -f "${resolved_path}" ]]; then
      fail "manifest path does not exist: ${path} -> ${resolved_path}"
    fi

    if [[ "${kind}" == "required" ]]; then
      if ! grep -Fq -- "${pattern}" "${resolved_path}"; then
        echo "${path}: missing required pattern \`${pattern}\`" >&2
        violations=1
      fi
    else
      if grep -Fn -- "${pattern}" "${resolved_path}" >/tmp/telltale_tooling_convergence.$$ 2>/dev/null; then
        cat /tmp/telltale_tooling_convergence.$$ >&2
        echo "${path}: found forbidden pattern \`${pattern}\`" >&2
        violations=1
      fi
      rm -f /tmp/telltale_tooling_convergence.$$
    fi
  done < <(parse_manifest_expectations)

  if (( violations )); then
    fail "manifest-backed tooling/docs convergence checks failed"
  fi
}

check_manifest_expectations

# ── Deprecated Scaffold Flags ────────────────────────────────────────

check_no_match 'effect-scaffold out=' Justfile
check_no_match '--name' Justfile rust/runtime/src/bin/effect_scaffold.rs

# ── Retired Protocol Machine Constructors ──────────────────────────────────────────

check_no_match '\bThreadedVM\b' rust/machine/examples rust/machine/benches
check_no_match '\bVM::new\b' rust/machine/examples rust/machine/benches
check_no_match '\bVMConfig\b' rust/machine/examples rust/machine/benches
check_no_match 'load_choreography\(' rust/machine/examples rust/machine/benches

# ── Stale Justfile Description ───────────────────────────────────────

check_no_match 'EffectHandler stubs plus simulator harness test templates' Justfile

# ── Legacy Public Teaching Surfaces ──────────────────────────────────

check_no_match 'Program::new\(' \
  docs/02_getting_started.md \
  docs/03_architecture.md \
  docs/08_extensions.md \
  docs/09_effect_handlers.md \
  docs/28_examples.md \
  docs/29_wasm_guide.md

check_no_match 'compose race\b' docs examples
check_no_match 'compose fallback\b' docs examples
check_no_match 'compose quorum\(' docs examples

echo "tooling-convergence: ok"
