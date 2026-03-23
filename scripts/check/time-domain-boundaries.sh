#!/usr/bin/env bash
# Run telltale-lint-checks time-domain check on VM, simulator, and bridge sources.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

cargo run -q -p telltale-lint-checks -- time-domain rust/vm/src rust/simulator/src rust/lean-bridge/src
