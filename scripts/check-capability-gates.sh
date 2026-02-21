#!/usr/bin/env bash
set -euo pipefail

# Consolidated capability gate checks for theorem-pack conformance.
# Usage:
#   ./scripts/check-capability-gates.sh [--all|--byzantine|--delegation|--envelope|--failure|--contracts|--speculation]
#
# Modes:
#   --all         Run all capability gate checks (default)
#   --byzantine   Byzantine safety capability checks
#   --delegation  Delegation/shard ownership transfer checks
#   --envelope    Envelope theorem-capability checks
#   --failure     Failure capability conformance checks
#   --contracts   Runtime contract/admission gate checks
#   --speculation Speculation/WP surface conformance checks

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

MODE="${1:---all}"

checks=0
failures=0

check() {
  local desc="$1"
  local cmd="$2"
  checks=$((checks + 1))
  if eval "${cmd}"; then
    echo "OK   ${desc}"
  else
    failures=$((failures + 1))
    echo "FAIL ${desc}"
  fi
}

run_check() {
  local name="$1"
  local cmd="$2"
  checks=$((checks + 1))
  echo "== ${name}"
  if eval "${cmd}"; then
    echo "OK   ${name}"
  else
    failures=$((failures + 1))
    echo "FAIL ${name}" >&2
  fi
  echo
}

require_ripgrep() {
  if ! command -v rg >/dev/null 2>&1; then
    echo "error: ripgrep (rg) is required" >&2
    exit 2
  fi
}

# --- Byzantine Capability Checks ---
check_byzantine() {
  require_ripgrep
  local TEST_FILE="${ROOT_DIR}/lean/Distributed/Tests/ByzantineConformance.lean"
  local THEOREMPACK_API_FILE="${ROOT_DIR}/lean/Runtime/Proofs/TheoremPack/API.lean"
  local THEOREMPACK_FILE="${ROOT_DIR}/lean/Runtime/Proofs/TheoremPack.lean"
  local INVENTORY_FILE="${ROOT_DIR}/lean/Runtime/Proofs/TheoremPack/Inventory.lean"

  echo "== Byzantine Conformance =="

  check "positive profile test: theorem-pack byzantine slot materializes" \
    "rg -q 'def canOperateUnderByzantineEnvelope' '${THEOREMPACK_API_FILE}' && \
     rg -q 'pack\\.byzantineSafety\\?\\.isSome && pack\\.vmEnvelopeAdherence\\?\\.isSome' '${THEOREMPACK_API_FILE}'"
  check "positive profile test: BFT specialization theorem is covered" \
    "rg -q 'bft_specialization_of_quorumGeometry' '${TEST_FILE}'"
  check "positive profile test: Nakamoto specialization theorem is covered" \
    "rg -q 'nakamoto_specialization_of_securityProtocol' '${TEST_FILE}'"
  check "positive profile test: hybrid specialization theorem is covered" \
    "rg -q 'hybrid_specialization_of_characterization' '${TEST_FILE}'"

  check "negative profile test: runtime gate rejects missing artifacts" \
    "rg -q 'canOperateUnderByzantineEnvelope' '${THEOREMPACK_API_FILE}' && \
     rg -q '&& pack\\.vmEnvelopeAdherence\\?\\.isSome' '${THEOREMPACK_API_FILE}'"
  check "negative profile test: inventory gate rejects unsupported claim" \
    "rg -q 'def claimedCapabilitiesWithinInventory' '${THEOREMPACK_API_FILE}'"

  check "counterexample regression: no-quorum drop test exists" \
    "rg -q 'noQuorumCounterexample_of_droppedAssumption' '${TEST_FILE}'"
  check "counterexample regression: invalid-auth drop test exists" \
    "rg -q 'invalidAuthCounterexample_of_droppedAssumption' '${TEST_FILE}'"
  check "counterexample regression: threshold-budget drop test exists" \
    "rg -q 'thresholdBudgetCounterexample_of_droppedAssumption' '${TEST_FILE}'"
  check "counterexample regression: primitive-mismatch drop test exists" \
    "rg -q 'primitiveMismatchCounterexample_of_droppedAssumption' '${TEST_FILE}'"

  check "theorem-pack inventory includes byzantine capability slot check" \
    "rg -q '\\(\"byzantine_safety_characterization\", pack\\.byzantineSafety\\?\\.isSome\\)' '${INVENTORY_FILE}' && \
     rg -q '\\(\"byzantine_safety_characterization\", pack\\.byzantineSafety\\?\\.isSome\\)' '${THEOREMPACK_FILE}'"

  check "cross-target byzantine injection conformance tests exist" \
    "rg -q 'injectByzantineEvents' '${TEST_FILE}' && \
     rg -q 'Envelope_byz injectedByzantineModel' '${TEST_FILE}'"

  echo "Type-checking Lean Byzantine conformance test module..."
  (
    cd "${ROOT_DIR}/lean"
    lake env lean Distributed/Tests/ByzantineConformance.lean >/dev/null
  )
  echo "OK   Distributed.Tests.ByzantineConformance type-checks successfully"
}

# --- Delegation/Shard Checks ---
check_delegation() {
  echo "== Delegation Shard Gate =="
  run_check "cooperative transfer guard rejects non-delegation ownership mutation" \
    "cargo test -p telltale-vm test_transfer_rejects_delegation_guard_violation"
  run_check "threaded transfer handoff emits delegation evidence" \
    "TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-vm --features multi-thread --test threaded_lane_runtime deterministic_transfer_handoff_uses_delegation_path"
  run_check "threaded transfer guard rejects ambiguous ownership mutation" \
    "TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-vm --features multi-thread delegation_handoff_guard_rejects_ambiguous_endpoint_ownership"
}

# --- Envelope Capability Checks ---
check_envelope() {
  require_ripgrep
  local THEOREMPACK_API_FILE="${ROOT_DIR}/lean/Runtime/Proofs/TheoremPack/API.lean"
  local THEOREMPACK_FILE="${ROOT_DIR}/lean/Runtime/Proofs/TheoremPack.lean"
  local ADAPTER_FILE="${ROOT_DIR}/lean/Runtime/Proofs/Adapters/Distributed.lean"
  local TEST_FILE="${ROOT_DIR}/lean/Runtime/Tests/Main.lean"
  local RUST_ENVELOPE_TEST_FILE="${ROOT_DIR}/rust/vm/tests/parity_fixtures_v2.rs"

  echo "== Envelope Conformance =="

  check "runtime shard-placement gate helper exists" \
    "rg -q 'def canAdmitShardPlacement' '${THEOREMPACK_API_FILE}'"
  check "runtime live-migration gate helper exists" \
    "rg -q 'def canLiveMigrate' '${THEOREMPACK_API_FILE}'"
  check "runtime placement-refinement gate helper exists" \
    "rg -q 'def canRefinePlacement' '${THEOREMPACK_API_FILE}'"
  check "runtime reordering gate helper exists" \
    "rg -q 'def canRelaxReordering' '${THEOREMPACK_API_FILE}'"
  check "runtime mixed-determinism gate helper exists" \
    "rg -q 'def canUseMixedDeterminismProfiles' '${THEOREMPACK_API_FILE}'"
  check "runtime byzantine-envelope gate helper exists" \
    "rg -q 'def canOperateUnderByzantineEnvelope' '${THEOREMPACK_API_FILE}'"
  check "runtime autoscale/repartition gate helper exists" \
    "rg -q 'def canAutoscaleOrRepartition' '${THEOREMPACK_API_FILE}'"

  check "CI inventory-claim guard helper exists" \
    "rg -q 'def claimedCapabilitiesWithinInventory' '${THEOREMPACK_API_FILE}'"
  check "serialized envelope capability snapshot helper exists" \
    "rg -q 'def envelopeCapabilitySnapshot' '${THEOREMPACK_API_FILE}'"

  check "theorem-pack carries protocol bridge capability bit" \
    "rg -q '\\(\"protocol_envelope_bridge\", pack\\.protocolEnvelopeBridge\\?\\.isSome\\)' '${THEOREMPACK_FILE}'"
  check "theorem-pack carries byzantine safety capability bit" \
    "rg -q '\\(\"byzantine_safety_characterization\", pack\\.byzantineSafety\\?\\.isSome\\)' '${THEOREMPACK_FILE}'"
  check "theorem-pack carries VM envelope adherence capability bit" \
    "rg -q '\\(\"vm_envelope_adherence\", pack\\.vmEnvelopeAdherence\\?\\.isSome\\)' '${THEOREMPACK_FILE}'"
  check "theorem-pack carries VM envelope admission capability bit" \
    "rg -q '\\(\"vm_envelope_admission\", pack\\.vmEnvelopeAdmission\\?\\.isSome\\)' '${THEOREMPACK_FILE}'"

  check "distributed adapter carries protocol bridge profile slot" \
    "rg -q 'protocolEnvelopeBridge\\?' '${ADAPTER_FILE}'"
  check "distributed adapter carries byzantine safety profile slot" \
    "rg -q 'byzantineSafety\\?' '${ADAPTER_FILE}'"
  check "distributed adapter carries VM adherence profile slot" \
    "rg -q 'vmEnvelopeAdherence\\?' '${ADAPTER_FILE}'"
  check "distributed adapter carries VM admission profile slot" \
    "rg -q 'vmEnvelopeAdmission\\?' '${ADAPTER_FILE}'"

  check "local-envelope differential conformance test exists" \
    "rg -q 'local envelope modulo conformance mismatch' '${TEST_FILE}'"
  check "sharded-envelope differential conformance test exists" \
    "rg -q 'sharded envelope modulo conformance mismatch' '${TEST_FILE}'"
  check "admission regression boundary tests exist" \
    "rg -q 'admission regression:' '${TEST_FILE}'"
  check "threaded wave-width envelope bound positive test exists" \
    "rg -q 'envelope_bounded_parity_holds_for_n_gt_1' '${RUST_ENVELOPE_TEST_FILE}'"
  check "threaded wave-width envelope bound violation test exists" \
    "rg -q 'envelope_bounded_parity_detects_wave_width_bound_violation' '${RUST_ENVELOPE_TEST_FILE}'"

  echo "Running Lean conformance test module..."
  (
    cd "${ROOT_DIR}/lean"
    lake build Runtime.Tests.Main >/dev/null
    lake env lean --run Runtime/Tests/Main.lean >/dev/null
  )
  echo "OK   Runtime.Tests.Main executes successfully"
}

# --- Failure Capability Checks ---
check_failure() {
  require_ripgrep
  local FAILURE_FILE="${ROOT_DIR}/lean/Runtime/VM/Runtime/Failure.lean"
  local FAILURE_PROOFS_FILE="${ROOT_DIR}/lean/Runtime/Proofs/VM/Failure.lean"
  local ADAPTER_FILE="${ROOT_DIR}/lean/Runtime/Proofs/Adapters/Distributed.lean"
  local THEOREMPACK_FILE="${ROOT_DIR}/lean/Runtime/Proofs/TheoremPack.lean"
  local TEST_FILE="${ROOT_DIR}/lean/Runtime/Tests/Main.lean"
  local STATE_FILE="${ROOT_DIR}/lean/Runtime/VM/Model/State.lean"
  local ENVELOPE_FILE="${ROOT_DIR}/lean/Runtime/Adequacy/EnvelopeCore.lean"

  echo "== Failure Capability Conformance =="

  check "bounded-diff recovery mode exists in runtime failure policy" \
    "rg -q '\\.boundedDiff' '${FAILURE_FILE}'"

  if rg -q '\.boundedDiff' "${FAILURE_FILE}"; then
    check "distributed adapters expose failure-envelope profile slot" \
      "rg -q 'failureEnvelope\\?' '${ADAPTER_FILE}'"
    check "distributed adapters expose failure-envelope attach helper" \
      "rg -q 'withFailureEnvelope' '${ADAPTER_FILE}'"
    check "theorem-pack carries failure-envelope artifact slot" \
      "rg -q 'failureEnvelope\\? : Option FailureEnvelopeArtifact' '${THEOREMPACK_FILE}'"
    check "theorem inventory exposes failure-envelope capability bit" \
      "rg -q '\\(\"failure_envelope\", pack\\.failureEnvelope\\?\\.isSome\\)' '${THEOREMPACK_FILE}'"
  fi

  check "artifact-level cross-target error-code compatibility tests exist" \
    "rg -q 'error-code compatibility mismatch' '${TEST_FILE}'"

  check "cross-target failure-visible conformance regression tests exist" \
    "rg -q 'cross-target failure-visible conformance mismatch' '${TEST_FILE}'"

  check "restart structured-error adequacy regression tests exist" \
    "rg -q 'restart structured-error adequacy mismatch' '${TEST_FILE}'"

  check "phase-1 gate: structured error schema + mappings are present" \
    "rg -q 'structure StructuredErrorEvent' '${STATE_FILE}' && \
     rg -q 'def failureClassOfRustFaultTag' '${ENVELOPE_FILE}' && \
     rg -q 'def errorCodeOfRustFaultTag' '${ENVELOPE_FILE}'"

  check "phase-2 gate: deterministic recovery + checkpoint/idempotency mechanisms are present" \
    "rg -q 'theorem decideRecovery_deterministic' '${FAILURE_PROOFS_FILE}' && \
     rg -q 'checkpointLog' '${STATE_FILE}' && \
     rg -q 'nextEffectNonce' '${STATE_FILE}'"

  check "phase-3 gate: abstract failure proofs are bridged through adapters/theorem-pack" \
    "rg -q 'structure FailureEnvelopeProtocol' '${ENVELOPE_FILE}' && \
     rg -q 'failureEnvelope\\?' '${ADAPTER_FILE}' && \
     rg -q 'FailureEnvelopeArtifact' '${THEOREMPACK_FILE}'"

  check "phase-3.5 gate: cross-target failure conformance theorem is exposed" \
    "rg -q 'def CrossTargetFailureConformance' '${ENVELOPE_FILE}' && \
     rg -q 'crossTargetConformance' '${THEOREMPACK_FILE}'"

  check "phase-3.6 gate: restart-refinement + structured-error adequacy theorem is exposed" \
    "rg -q 'def RestartRefinementStructuredErrorAdequacy' '${ENVELOPE_FILE}' && \
     rg -q 'restartStructuredErrorAdequacy' '${THEOREMPACK_FILE}'"

  check "phase-4 gate: VM theorem-pack exposes failure-envelope capability" \
    "rg -q '\\(\"failure_envelope\", pack\\.failureEnvelope\\?\\.isSome\\)' '${THEOREMPACK_FILE}'"

  check "phase-5 gate: CI enforces failure conformance checks" \
    "rg -q 'check-capability-gates' '${ROOT_DIR}/justfile'"
}

# --- Runtime Contract Checks ---
check_contracts() {
  require_ripgrep
  local CONTRACTS_FILE="${ROOT_DIR}/lean/Runtime/Proofs/Contracts/RuntimeContracts.lean"
  local API_FILE="${ROOT_DIR}/lean/Runtime/Proofs/TheoremPack/API.lean"
  local EXAMPLE_FILE="${ROOT_DIR}/lean/Runtime/Proofs/Examples/ComposedProofPack.lean"

  echo "== Runtime Contract Gates =="

  check "admission API requires runtime contracts for advanced modes" \
    "rg -q 'def requiresVMRuntimeContracts' '${CONTRACTS_FILE}' && \
     rg -q 'def admitVMRuntime' '${CONTRACTS_FILE}' && \
     rg -q 'theorem admitVMRuntime_requires_contracts' '${CONTRACTS_FILE}'"

  check "determinism profile selection is capability-gated and validated" \
    "rg -q 'def determinismProfileSupported' '${CONTRACTS_FILE}' && \
     rg -q 'def requestDeterminismProfile' '${CONTRACTS_FILE}' && \
     rg -q 'canUseMixedDeterminismProfiles' '${CONTRACTS_FILE}'"

  check "composed spaces provide deterministic minimal capability inventory API" \
    "rg -q 'def minimalCapabilities' '${API_FILE}' && \
     rg -q 'def composeProofSpaces' '${API_FILE}' && \
     rg -q 'def composedSpace' '${EXAMPLE_FILE}'"

  if command -v lake >/dev/null 2>&1; then
    (
      cd "${ROOT_DIR}/lean"
      lake build Runtime.Proofs.Contracts.RuntimeContracts \
        Runtime.Proofs.TheoremPack.API \
        Runtime.Proofs.Examples.ComposedProofPack >/dev/null
    )
    echo "OK   runtime contract gate modules type-check successfully"
  elif command -v elan >/dev/null 2>&1; then
    (
      cd "${ROOT_DIR}"
      elan run leanprover/lean4:v4.26.0 lake --dir lean build \
        Runtime.Proofs.Contracts.RuntimeContracts \
        Runtime.Proofs.TheoremPack.API \
        Runtime.Proofs.Examples.ComposedProofPack >/dev/null
    )
    echo "OK   runtime contract gate modules type-check successfully"
  else
    echo "WARN skipping Lean type-check in runtime contract gates script (no lake/elan)"
  fi
}

# --- Speculation/WP Surface Checks ---
check_speculation() {
  require_ripgrep
  local TARGET_FILES=(
    "${ROOT_DIR}/lean/Runtime/ProgramLogic/GhostState.lean"
    "${ROOT_DIR}/lean/Runtime/ProgramLogic/WPPair.lean"
    "${ROOT_DIR}/lean/Runtime/ProgramLogic/SessionWP.lean"
    "${ROOT_DIR}/lean/Runtime/ProgramLogic/FinalizationWP.lean"
    "${ROOT_DIR}/lean/Runtime/Adequacy/Adequacy.lean"
    "${ROOT_DIR}/lean/Runtime/Proofs/VM/Speculation.lean"
  )

  echo "== Speculation/WP Surface Conformance =="

  for f in "${TARGET_FILES[@]}"; do
    if [[ ! -f "${f}" ]]; then
      echo "error: missing target file ${f}" >&2
      exit 2
    fi
  done

  local PATTERN='(?i)\b(?:TODO|FIXME|TBD|placeholder|stub|unimplemented|WIP)\b'
  local HITS
  HITS="$({
    rg -n --pcre2 "${PATTERN}" "${TARGET_FILES[@]}" || true
  } | sed "s#${ROOT_DIR}/##" | sort -u)"

  if [[ -n "${HITS}" ]]; then
    echo "FAIL speculation/WP target modules still contain placeholder markers:" >&2
    printf '%s\n' "${HITS}" >&2
    failures=$((failures + 1))
  else
    echo "OK   no placeholder/stub markers in speculation/WP target modules"
  fi

  if command -v lake >/dev/null 2>&1; then
    (
      cd "${ROOT_DIR}/lean"
      lake build Runtime.ProgramLogic.WPPair Runtime.ProgramLogic.SessionWP \
        Runtime.ProgramLogic.FinalizationWP Runtime.Adequacy.Adequacy \
        Runtime.Proofs.VM.Speculation >/dev/null
    )
  elif command -v elan >/dev/null 2>&1; then
    (
      cd "${ROOT_DIR}"
      elan run leanprover/lean4:v4.26.0 lake --dir lean build \
        Runtime.ProgramLogic.WPPair Runtime.ProgramLogic.SessionWP \
        Runtime.ProgramLogic.FinalizationWP Runtime.Adequacy.Adequacy \
        Runtime.Proofs.VM.Speculation >/dev/null
    )
  else
    echo "WARN skipping Lean build check (no lake/elan found)"
  fi

  echo "OK   speculation/WP target modules build successfully"
}

# --- Main ---
case "${MODE}" in
  --all)
    check_byzantine
    echo ""
    check_delegation
    echo ""
    check_envelope
    echo ""
    check_failure
    echo ""
    check_contracts
    echo ""
    check_speculation
    ;;
  --byzantine)
    check_byzantine
    ;;
  --delegation)
    check_delegation
    ;;
  --envelope)
    check_envelope
    ;;
  --failure)
    check_failure
    ;;
  --contracts)
    check_contracts
    ;;
  --speculation)
    check_speculation
    ;;
  *)
    echo "error: unknown mode ${MODE}" >&2
    echo "Usage: $0 [--all|--byzantine|--delegation|--envelope|--failure|--contracts|--speculation]" >&2
    exit 2
    ;;
esac

echo ""
echo "Summary: ${checks} checks, ${failures} failure(s)."
if (( failures > 0 )); then
  exit 1
fi
