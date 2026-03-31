#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
LEAN_DIR="${ROOT_DIR}/lean"
LEAN_THREADS="${LEAN_NUM_THREADS:-3}"
STRICT_TMPDIR="${ROOT_DIR}/.tmp/lean-bridge-strict"

cd "${ROOT_DIR}"

mkdir -p "${STRICT_TMPDIR}"

if [[ -n "${TMPDIR:-}" && ! -d "${TMPDIR}" ]]; then
  export TMPDIR="${STRICT_TMPDIR}"
else
  export TMPDIR="${TMPDIR:-${STRICT_TMPDIR}}"
fi

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

echo "run strict bridge property corpus"
TELLTALE_REQUIRE_PROTOCOL_MACHINE_RUNNER=1 \
  cargo test -p telltale-bridge --test property_tests -- --nocapture

echo "run strict reconfiguration correspondence corpus"
TELLTALE_REQUIRE_PROTOCOL_MACHINE_RUNNER=1 \
  cargo test -p telltale-bridge --test protocol_bundle_admission_contracts -- --nocapture

echo "run strict protocol-machine trace validation corpus"
TELLTALE_REQUIRE_PROTOCOL_MACHINE_RUNNER=1 \
TELLTALE_REQUIRE_PROTOCOL_MACHINE_TRACE_VALIDATION=1 \
  cargo test -p telltale-bridge --test lean_trace_validation -- --nocapture

echo "run strict simulator trace validation corpus"
TELLTALE_REQUIRE_PROTOCOL_MACHINE_RUNNER=1 \
TELLTALE_REQUIRE_SIMULATION_TRACE_VALIDATION=1 \
  cargo test -p telltale-simulator --test lean_reference_parity -- --nocapture

echo "run strict protocol-machine correspondence corpus"
TELLTALE_REQUIRE_PROTOCOL_MACHINE_RUNNER=1 \
  cargo test -p telltale-bridge --test protocol_machine_correspondence_tests -- --nocapture

echo "run strict protocol-machine differential-step corpus"
TELLTALE_REQUIRE_PROTOCOL_MACHINE_RUNNER=1 \
  cargo test -p telltale-bridge --test protocol_machine_differential_steps -- --nocapture

echo "run strict capability-model correspondence corpus"
TELLTALE_REQUIRE_PROTOCOL_MACHINE_RUNNER=1 \
  cargo test -p telltale-bridge --test capability_model_correspondence -- --nocapture

echo "lean-bridge-strict: ok"
