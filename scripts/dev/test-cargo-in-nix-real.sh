#!/usr/bin/env bash
# Telltale adapter; the shared fixture owns the original native child lifecycle.
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
export CACHE_FIXTURE_PREFIX=TELLTALE
exec bash "$here/test-cargo-cache-real.sh" "$@"
