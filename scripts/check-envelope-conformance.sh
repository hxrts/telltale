#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
THEOREMPACK_API_FILE="${ROOT_DIR}/lean/Runtime/Proofs/TheoremPack/API.lean"
THEOREMPACK_FILE="${ROOT_DIR}/lean/Runtime/Proofs/TheoremPack.lean"
ADAPTER_FILE="${ROOT_DIR}/lean/Runtime/Proofs/Adapters/Distributed.lean"
TEST_FILE="${ROOT_DIR}/lean/Runtime/Tests/Main.lean"

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

echo "Running Lean conformance test module..."
(
  cd "${ROOT_DIR}/lean"
  lake build Runtime.Tests.Main >/dev/null
  lake env lean --run Runtime/Tests/Main.lean >/dev/null
)
echo "OK   Runtime.Tests.Main executes successfully"

echo ""
echo "Summary: ${checks} checks, ${errors} failure(s)."
if (( errors > 0 )); then
  exit 1
fi
