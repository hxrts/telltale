#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${repo_root}"

if [ -n "${IN_NIX_SHELL:-}" ] && [ -n "${TOOLKIT_ROOT:-}" ] && command -v toolkit-xtask >/dev/null 2>&1; then
  exec "$@"
fi

toolkit_root="${repo_root}/../toolkit"
if [ -d "${toolkit_root}" ]; then
  if [ "${1:-}" = "toolkit-xtask" ]; then
    if [ "${2:-}" = "--help" ] || [ "${2:-}" = "-h" ] || [ "${2:-}" = "help" ]; then
      echo "toolkit-xtask: usage: check|parity|show-config|fmt|fmt-check|clippy|dylint"
      exit 0
    fi
    shift
    export TOOLKIT_ROOT="${toolkit_root}"
    exec cargo run --manifest-path "${toolkit_root}/xtask/Cargo.toml" -- "$@"
  fi
  exec nix develop --override-input toolkit "path:${toolkit_root}" --command "$@"
fi

exec nix develop --command "$@"
