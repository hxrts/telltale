#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
LEAN_DIR="${ROOT_DIR}/lean"
LEAN_THREADS="${LEAN_NUM_THREADS:-3}"

cd "${ROOT_DIR}"

./scripts/bootstrap/ensure-lean-prebuilt.sh

if ! command -v lake >/dev/null 2>&1; then
  echo "error: lake is required on PATH for strict Lean bridge verification" >&2
  exit 2
fi

echo "build strict Lean verification binaries"
LEAN_NUM_THREADS="${LEAN_THREADS}" lake --dir "${LEAN_DIR}" build telltale_validator protocol_machine_runner

echo "run strict projection validator corpus"
TELLTALE_REQUIRE_LEAN_VALIDATOR=1 \
  cargo test -p telltale-bridge --test projection_runner_tests -- --nocapture

echo "run strict protocol-bundle verification corpus"
TELLTALE_REQUIRE_PROTOCOL_MACHINE_RUNNER=1 \
  cargo test -p telltale-bridge --test invariant_verification -- --nocapture

echo "lean-bridge-strict: ok"
