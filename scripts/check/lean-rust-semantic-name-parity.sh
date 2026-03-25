#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${ROOT_DIR}"

LEAN_SEMANTIC_CORE="${ROOT_DIR}/lean/Runtime/ProtocolMachine/Model/SemanticObjects/Core.lean"
LEAN_PROTOCOL_MACHINE_API="${ROOT_DIR}/lean/Runtime/ProtocolMachine/API.lean"
RUST_MACHINE_SEMANTIC_OBJECTS="${ROOT_DIR}/rust/machine/src/semantic_objects.rs"
RUST_MACHINE_LIB="${ROOT_DIR}/rust/machine/src/lib.rs"
RUST_BRIDGE_SEMANTIC_OBJECTS="${ROOT_DIR}/rust/bridge/src/semantic_objects.rs"

required_surfaces=(
  "${LEAN_SEMANTIC_CORE}"
  "${LEAN_PROTOCOL_MACHINE_API}"
  "${RUST_MACHINE_SEMANTIC_OBJECTS}"
  "${RUST_MACHINE_LIB}"
  "${RUST_BRIDGE_SEMANTIC_OBJECTS}"
  "${ROOT_DIR}/lean/Runtime/ProtocolMachine/Runtime/Runner.lean"
  "${ROOT_DIR}/rust/bridge/src/protocol_machine_runner.rs"
  "${ROOT_DIR}/rust/bridge/src/protocol_machine_trace.rs"
)

for path in "${required_surfaces[@]}"; do
  if [[ ! -f "${path}" ]]; then
    echo "[semantic-name-parity] missing required surface: ${path}" >&2
    exit 1
  fi
done

required_types=(
  "OperationInstance"
  "OutstandingEffect"
  "SemanticHandoff"
  "AuthoritativeRead"
  "ObservedRead"
  "MaterializationProof"
  "CanonicalHandle"
  "ProgressContract"
  "ProgressTransition"
  "ProtocolMachineSemanticObjects"
)

check_type_surface() {
  local label="$1"
  local file="$2"
  local missing=()

  for name in "${required_types[@]}"; do
    if ! rg -q "\\b${name}\\b" "${file}"; then
      missing+=("${name}")
    fi
  done

  if (( ${#missing[@]} > 0 )); then
    echo "[semantic-name-parity] ${label} is missing canonical names:" >&2
    printf '  - %s\n' "${missing[@]}" >&2
    exit 1
  fi
}

check_type_surface "Lean semantic-object core" "${LEAN_SEMANTIC_CORE}"
check_type_surface "Rust machine semantic objects" "${RUST_MACHINE_SEMANTIC_OBJECTS}"
check_type_surface "Rust bridge semantic objects" "${RUST_BRIDGE_SEMANTIC_OBJECTS}"

if ! rg -q '\bProtocolMachine\b' "${LEAN_PROTOCOL_MACHINE_API}"; then
  echo "[semantic-name-parity] Lean protocol-machine API is missing ProtocolMachine" >&2
  exit 1
fi

if ! rg -q '\bProtocolMachine\b' "${RUST_MACHINE_LIB}"; then
  echo "[semantic-name-parity] Rust machine lib is missing ProtocolMachine" >&2
  exit 1
fi

if ! rg -q '^pub const SEMANTIC_OBJECTS_SCHEMA_VERSION' "${RUST_MACHINE_SEMANTIC_OBJECTS}"; then
  echo "[semantic-name-parity] rust machine semantic objects missing schema version marker" >&2
  exit 1
fi

if ! rg -q '^pub const SEMANTIC_OBJECTS_SCHEMA_VERSION' "${RUST_BRIDGE_SEMANTIC_OBJECTS}"; then
  echo "[semantic-name-parity] rust bridge semantic objects missing schema version marker" >&2
  exit 1
fi

if ! rg -q 'Region remains a choreography/topology identifier outside the protocol-machine semantic-object family' \
  "${ROOT_DIR}/docs/19_rust_lean_parity.md"; then
  echo "[semantic-name-parity] docs/19_rust_lean_parity.md is missing the Region boundary note" >&2
  exit 1
fi

echo "[semantic-name-parity] Lean and Rust protocol-machine semantic-object names are aligned"
