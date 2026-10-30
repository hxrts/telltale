#!/usr/bin/env bash
# The shared toolkit owns cache-key projection and selected-tool dispatch.
set -euo pipefail
: "${TELLTALE_NIX_CARGO_BIN:?enter the Telltale Nix shell}"
: "${TELLTALE_NIX_CLIPPY_BIN:?enter the Telltale Nix shell}"
: "${TELLTALE_NIX_SCCACHE_BIN:?enter the Telltale Nix shell}"
: "${TOOLKIT_CARGO_DISPATCH_BIN:?enter the Telltale Nix shell}"
[[ $TOOLKIT_CARGO_DISPATCH_BIN == /* ]] || exit 2
bypass=0
[[ ${TELLTALE_NO_SCCACHE:-0} != 1 && ${CARGO_INCREMENTAL:-0} != 1 ]] || bypass=1
if [[ ${1:-} == fmt ]]; then
 : "${TELLTALE_NIX_FMT_BIN:?enter the Telltale Nix shell}"
 exec "$TOOLKIT_CARGO_DISPATCH_BIN" --cargo "$TELLTALE_NIX_CARGO_BIN" --clippy "$TELLTALE_NIX_CLIPPY_BIN" --selected-cache "$TELLTALE_NIX_SCCACHE_BIN" --cache-bypass "$bypass" --fmt "$TELLTALE_NIX_FMT_BIN" -- "$@"
fi
exec "$TOOLKIT_CARGO_DISPATCH_BIN" --cargo "$TELLTALE_NIX_CARGO_BIN" --clippy "$TELLTALE_NIX_CLIPPY_BIN" --selected-cache "$TELLTALE_NIX_SCCACHE_BIN" --cache-bypass "$bypass" -- "$@"
