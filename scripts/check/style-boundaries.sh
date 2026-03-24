#!/usr/bin/env bash
# Run telltale-lints style check across core Rust crate sources.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

cargo run -q -p telltale-lints -- style rust/machine/src rust/simulator/src rust/bridge/src rust/types/src rust/transport/src
