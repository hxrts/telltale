#!/usr/bin/env bash
# Run telltale-lints time-domain check on protocol machine, simulator, and bridge sources.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

cargo run -q -p telltale-lints -- time-domain rust/machine/src rust/simulator/src rust/bridge/src
