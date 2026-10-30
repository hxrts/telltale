#!/usr/bin/env bash
# Actual Just recipe with controlled tool commands; no installation/build.
set -euo pipefail
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
# The optional CLI must match the bindings in both maintained lock domains.
# Reading each exact package record does not resolve dependencies or install tools.
for lock in "$root/Cargo.lock" "$root/examples/wasm/Cargo.lock"; do
  locked=$(awk '
    /^\[\[package\]\]$/ { selected=0 }
    /^name = "wasm-bindgen"$/ { selected=1 }
    selected && /^version = / { gsub(/"/, "", $3); print $3 }
  ' "$lock")
  [[ "$locked" == 0.2.118 ]] || {
    printf 'frontend setup: expected wasm-bindgen 0.2.118 in %s, got %s\n' "$lock" "$locked" >&2
    exit 1
  }
done
real_just=$(command -v just)
real_bash=$(command -v bash)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
# Narrow structural check of the removed shell-entry producers; not Nix execution.
if grep -Eq '^[[:space:]]*cargo[[:space:]]+install[[:space:]]' "$root/flake.nix"; then
  echo 'frontend setup: shell entry still directly installs Cargo tools' >&2
  exit 1
fi
mkdir "$scratch/bin" "$scratch/lean"
# The real Justfile reads this pin for all recipes; no Lean command is run.
printf 'controlled-no-Lean-execution\n' > "$scratch/lean/lean-toolchain"
ln -s "$real_bash" "$scratch/bin/bash"
cat > "$scratch/bin/cargo" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
printf '%s\n' "$*" >> "$SETUP_LOG"
if [[ ${FAIL_INSTALL:-} == "${2:-}" ]]; then printf 'original install failure\n' >&2; exit 41; fi
SH
chmod +x "$scratch/bin/cargo"
export SETUP_LOG="$scratch/calls" TOOL_VERSION='wasm-bindgen 0.2.118' FAIL_INSTALL='' QUERY_STATUS=0
# Keep only controlled commands and baseline OS tools visible to setup.
export PATH="$scratch/bin:/usr/bin:/bin"
for mode in missing current outdated lookalike dx-failure wasm-failure query-failure; do
  rm -f "$scratch/bin/dx" "$scratch/bin/wasm-bindgen"
  : > "$SETUP_LOG"
  TOOL_VERSION='wasm-bindgen 0.2.118'; FAIL_INSTALL=''; QUERY_STATUS=0
  if [[ $mode != missing && $mode != dx-failure ]]; then
    printf '#!/bin/sh\nexit 0\n' > "$scratch/bin/dx"
    chmod +x "$scratch/bin/dx"
    cat > "$scratch/bin/wasm-bindgen" <<'SH'
#!/usr/bin/env bash
printf '%s\n' "$TOOL_VERSION"
if (( QUERY_STATUS != 0 )); then printf 'original version failure\n' >&2; exit "$QUERY_STATUS"; fi
SH
    chmod +x "$scratch/bin/wasm-bindgen"
  fi
  case $mode in
    outdated|wasm-failure) TOOL_VERSION='wasm-bindgen 0.2.117' ;;
    lookalike) TOOL_VERSION='wasm-bindgen 0.2.1180' ;;
    dx-failure) FAIL_INSTALL=dioxus-cli ;;
    query-failure) QUERY_STATUS=43 ;;
  esac
  [[ $mode != wasm-failure ]] || FAIL_INSTALL=wasm-bindgen-cli
  status=0
  "$real_just" --justfile "$root/justfile" --working-directory "$scratch" setup-frontend-tools > "$scratch/stdout" 2> "$scratch/stderr" || status=$?
  case $mode in
    missing) expected=0; printf 'install dioxus-cli\ninstall wasm-bindgen-cli --version 0.2.118\n' > "$scratch/expected" ;;
    current) expected=0; : > "$scratch/expected" ;;
    outdated|lookalike) expected=0; printf 'install wasm-bindgen-cli --version 0.2.118\n' > "$scratch/expected" ;;
    dx-failure) expected=41; printf 'install dioxus-cli\n' > "$scratch/expected" ;;
    wasm-failure) expected=41; printf 'install wasm-bindgen-cli --version 0.2.118\n' > "$scratch/expected" ;;
    query-failure) expected=43; : > "$scratch/expected" ;;
  esac
  [[ $status == "$expected" ]] || { cat "$scratch/stderr" >&2; exit 1; }
  cmp "$scratch/expected" "$SETUP_LOG"
  case $mode in *failure) grep -Fq 'original' "$scratch/stderr" ;; esac
  printf 'explicit frontend setup: %s passed\n' "$mode"
done
