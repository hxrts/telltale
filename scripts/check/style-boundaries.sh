#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

cargo run -q -p telltale-lint-checks -- style rust/vm/src rust/simulator/src rust/lean-bridge/src rust/types/src rust/transport/src
