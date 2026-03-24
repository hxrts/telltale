#!/usr/bin/env bash
# Run telltale-lints session-ingress check on the protocol machine crate source.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

cargo run -q -p telltale-lints -- session-ingress rust/machine/src
