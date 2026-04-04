#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${ROOT_DIR}"

LEAN_SEMANTIC_CORE="${ROOT_DIR}/lean/Runtime/ProtocolMachine/Model/SemanticObjects/Core.lean"
LEAN_AGREEMENT_CORE="${ROOT_DIR}/lean/Runtime/ProtocolMachine/Model/SemanticObjects/AgreementCore.lean"
LEAN_SEMANTIC_OBJECTS_BARREL="${ROOT_DIR}/lean/Runtime/ProtocolMachine/Model/SemanticObjects.lean"
LEAN_PROTOCOL_MACHINE_API="${ROOT_DIR}/lean/Runtime/ProtocolMachine/API.lean"
RUST_MACHINE_SEMANTIC_OBJECTS="${ROOT_DIR}/rust/machine/src/semantic_objects.rs"
RUST_MACHINE_LIB="${ROOT_DIR}/rust/machine/src/lib.rs"
RUST_BRIDGE_SEMANTIC_OBJECTS="${ROOT_DIR}/rust/bridge/src/semantic_objects.rs"

required_surfaces=(
  "${LEAN_SEMANTIC_CORE}"
  "${LEAN_AGREEMENT_CORE}"
  "${LEAN_SEMANTIC_OBJECTS_BARREL}"
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
  "OwnershipScope"
  "DelegationStatus"
  "OperationInstance"
  "OutstandingEffect"
  "SemanticHandoff"
  "AuthoritativeRead"
  "ObservedRead"
  "MaterializationProof"
  "CanonicalHandle"
  "PublicationEvent"
  "Region"
  "ProgressContract"
  "ProgressTransition"
  "OperationVisibility"
  "AgreementLevel"
  "AgreementRule"
  "AgreementEvidenceKind"
  "FinalizationOutcome"
  "PrestateBinding"
  "AgreementProfile"
  "AgreementContract"
  "AgreementEvidence"
  "AgreementState"
  "ProtocolMachineSemanticObjects"
)

agreement_types=(
  "OperationVisibility"
  "AgreementLevel"
  "FinalizationOutcome"
  "PrestateBinding"
  "AgreementProfile"
  "AgreementContract"
  "AgreementEvidence"
  "AgreementState"
)

check_type_surface() {
  local label="$1"
  local file="$2"
  shift 2
  local names=("$@")
  local missing=()

  for name in "${names[@]}"; do
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

check_type_surface "Lean semantic-object core" "${LEAN_SEMANTIC_CORE}" "${required_types[@]}"
check_type_surface "Lean agreement semantic-object core" "${LEAN_AGREEMENT_CORE}" "${agreement_types[@]}"
check_type_surface "Rust machine semantic objects" "${RUST_MACHINE_SEMANTIC_OBJECTS}" "${required_types[@]}"
check_type_surface "Rust bridge semantic objects" "${RUST_BRIDGE_SEMANTIC_OBJECTS}" "${required_types[@]}"

if ! rg -q '\bProtocolMachine\b' "${LEAN_PROTOCOL_MACHINE_API}"; then
  echo "[semantic-name-parity] Lean protocol-machine API is missing ProtocolMachine" >&2
  exit 1
fi

if ! rg -q '\bProtocolMachine\b' "${RUST_MACHINE_LIB}"; then
  echo "[semantic-name-parity] Rust machine lib is missing ProtocolMachine" >&2
  exit 1
fi

for module_name in model runtime semantics; do
  if ! rg -q "^pub mod ${module_name} \\{" "${RUST_MACHINE_LIB}"; then
    echo "[semantic-name-parity] Rust machine lib is missing canonical public module '${module_name}'" >&2
    exit 1
  fi
done

removed_public_modules=(
  "protocol_machine"
  "guest_runtime"
  "host_runtime"
)

for module_name in "${removed_public_modules[@]}"; do
  if rg -q "^pub mod ${module_name} \\{" "${RUST_MACHINE_LIB}"; then
    echo "[semantic-name-parity] Rust machine lib still exposes removed public module '${module_name}'" >&2
    exit 1
  fi
done

removed_names=(
  "NestedVMHandler"
  "WasmVM"
  "ExternalHandler"
  "ProtocolMachineRunStatus"
  "ProtocolMachineStepResult"
)

for name in "${removed_names[@]}"; do
  if rg -q "\\b${name}\\b" "${RUST_MACHINE_LIB}" "${ROOT_DIR}/rust/machine/src/nested.rs" \
    "${ROOT_DIR}/rust/machine/src/wasm.rs" "${ROOT_DIR}/docs/105_code_organization.md" \
    "${ROOT_DIR}/docs/901_api_reference.md"; then
    echo "[semantic-name-parity] removed runtime name '${name}' is still present" >&2
    exit 1
  fi
done

if rg -q 'TELLTALE_VM_TIMEOUT_MS' "${ROOT_DIR}/rust/bridge/src/protocol_machine_runner.rs"; then
  echo "[semantic-name-parity] old VM timeout env var name is still present" >&2
  exit 1
fi

if ! rg -q '^pub const SEMANTIC_OBJECTS_SCHEMA_VERSION' "${RUST_MACHINE_SEMANTIC_OBJECTS}"; then
  echo "[semantic-name-parity] rust machine semantic objects missing schema version marker" >&2
  exit 1
fi

if ! rg -q 'pub use telltale_machine::model::semantic_objects::\{' "${RUST_BRIDGE_SEMANTIC_OBJECTS}"; then
  echo "[semantic-name-parity] rust bridge semantic objects must reuse the machine semantic-object family" >&2
  exit 1
fi

for duplicate in "pub struct OperationInstance" "pub struct OutstandingEffect" "pub struct SemanticHandoff" \
  "pub struct AuthoritativeRead" "pub struct ObservedRead" "pub struct MaterializationProof" \
  "pub struct CanonicalHandle" "pub struct ProgressContract"; do
  if rg -q "${duplicate}" "${RUST_BRIDGE_SEMANTIC_OBJECTS}"; then
    echo "[semantic-name-parity] rust bridge semantic objects still define duplicate canonical types" >&2
    exit 1
  fi
done

if ! rg -q '`Region` is now part of the canonical protocol-machine semantic-object family' \
  "${ROOT_DIR}/docs/802_rust_lean_parity.md"; then
  echo "[semantic-name-parity] docs/802_rust_lean_parity.md is missing the Region semantic-core note" >&2
  exit 1
fi

for doc_path in "${ROOT_DIR}/docs/105_code_organization.md" "${ROOT_DIR}/docs/901_api_reference.md"; do
  if ! rg -q 'telltale_machine::model' "${doc_path}" || \
     ! rg -q 'telltale_machine::runtime' "${doc_path}" || \
     ! rg -q 'telltale_machine::semantics' "${doc_path}"; then
    echo "[semantic-name-parity] ${doc_path} is missing canonical Rust module references" >&2
    exit 1
  fi
done

echo "[semantic-name-parity] Lean and Rust protocol-machine semantic-object names are aligned"
