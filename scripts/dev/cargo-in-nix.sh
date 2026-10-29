#!/usr/bin/env bash
# Keep Cargo-home plugins on the explicitly selected compiler.
set -euo pipefail
: "${TELLTALE_NIX_CARGO_BIN:?enter the Telltale Nix shell}"
: "${TELLTALE_NIX_CLIPPY_BIN:?enter the Telltale Nix shell}"
# Opt out per invocation without removing a caller's unrelated wrapper.
if [[ ( ${TELLTALE_NO_SCCACHE:-0} == 1 || ${CARGO_INCREMENTAL:-0} == 1 ) &&
      ${RUSTC_WRAPPER:-} == *sccache ]]; then
  unset RUSTC_WRAPPER
fi
if [[ ${1:-} == clippy ]]; then
  exec "$TELLTALE_NIX_CLIPPY_BIN" "$@"
fi
if [[ ${1:-} == fmt ]]; then
  : "${TELLTALE_NIX_FMT_BIN:?enter the Telltale Nix shell}"
  exec "$TELLTALE_NIX_FMT_BIN" "$@"
fi
exec "$TELLTALE_NIX_CARGO_BIN" "$@"
