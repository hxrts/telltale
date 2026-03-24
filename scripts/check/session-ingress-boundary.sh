#!/usr/bin/env bash
# Run telltale-lint-checks session-ingress check on the protocol machine crate source.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

cargo run -q -p telltale-lint-checks -- session-ingress rust/protocol-machine/src
