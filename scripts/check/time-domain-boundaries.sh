#!/usr/bin/env bash
# Run telltale-lint-checks time-domain check on protocol machine, simulator, and bridge sources.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

cargo run -q -p telltale-lint-checks -- time-domain rust/protocol-machine/src rust/simulator/src rust/lean-bridge/src
