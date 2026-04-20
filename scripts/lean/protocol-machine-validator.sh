#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
LEAN_DIR="${ROOT_DIR}/lean"
STRICT_TMPDIR="${ROOT_DIR}/.tmp/protocol-machine-validator"

mkdir -p "${STRICT_TMPDIR}"
export TMPDIR="${STRICT_TMPDIR}"
export TMP="${STRICT_TMPDIR}"
export TEMP="${STRICT_TMPDIR}"

cd "${LEAN_DIR}"
exec lake env lean --run Runtime/Tests/ProtocolMachineValidator.lean "$@"
