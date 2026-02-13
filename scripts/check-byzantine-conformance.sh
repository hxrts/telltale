#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TEST_FILE="${ROOT_DIR}/lean/Distributed/Tests/ByzantineConformance.lean"
THEOREMPACK_API_FILE="${ROOT_DIR}/lean/Runtime/Proofs/TheoremPack/API.lean"
THEOREMPACK_FILE="${ROOT_DIR}/lean/Runtime/Proofs/TheoremPack.lean"
INVENTORY_FILE="${ROOT_DIR}/lean/Runtime/Proofs/TheoremPack/Inventory.lean"

if ! command -v rg >/dev/null 2>&1; then
  echo "error: ripgrep (rg) is required" >&2
  exit 2
fi

errors=0
checks=0

check() {
  local desc="$1"
  local cmd="$2"
  checks=$((checks + 1))
  if eval "${cmd}"; then
    echo "OK   ${desc}"
  else
    errors=$((errors + 1))
    echo "FAIL ${desc}"
  fi
}

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

echo ""
echo "Summary: ${checks} checks, ${errors} failure(s)."
if (( errors > 0 )); then
  exit 1
fi
