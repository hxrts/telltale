#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RELEASE_FILE="${ROOT_DIR}/lean/Runtime/Proofs/TheoremPack/ReleaseConformance.lean"
API_FILE="${ROOT_DIR}/lean/Runtime/Proofs/TheoremPack/API.lean"
INVENTORY_FILE="${ROOT_DIR}/lean/Runtime/Proofs/TheoremPack/Inventory.lean"
TEST_FILE="${ROOT_DIR}/lean/Runtime/Tests/Main.lean"
JUSTFILE="${ROOT_DIR}/justfile"
REPORT_FILE="${ROOT_DIR}/artifacts/release_conformance_report.json"

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

echo "== Release Conformance =="

check "optimization envelope classes are defined" \
  "rg -q 'inductive RuntimeTransformationEnvelopeClass' '${RELEASE_FILE}' && \
   rg -q 'def transformationClassEligible' '${RELEASE_FILE}'"

check "effect-bisim bridge theorem for transformation classes exists" \
  "rg -q 'theorem transformationClass_preserves_observer_behavior' '${RELEASE_FILE}'"

check "certified replay conformance helpers exist" \
  "rg -q 'structure CertifiedReplayEquivalenceClass' '${RELEASE_FILE}' && \
   rg -q 'def replayConformsToCertifiedClass' '${RELEASE_FILE}' && \
   rg -q 'def replayConformsToClasses' '${RELEASE_FILE}'"

check "failure-envelope cross-target witness gate exists" \
  "rg -q 'def hasFailureEnvelopeCrossTargetWitness' '${RELEASE_FILE}'"

check "restart/structured-error adequacy witness gate exists" \
  "rg -q 'def hasRestartStructuredErrorAdequacyWitness' '${RELEASE_FILE}'"

check "single-thread, multi-thread, and sharded evidence gates exist" \
  "rg -q 'def hasSingleThreadEvidence' '${RELEASE_FILE}' && \
   rg -q 'def hasMultiThreadEvidence' '${RELEASE_FILE}' && \
   rg -q 'def hasShardedEvidence' '${RELEASE_FILE}'"

check "release report and release build gate are defined" \
  "rg -q 'def releaseConformanceReportVersion' '${RELEASE_FILE}' && \
   rg -q 'structure ReleaseConformanceReport' '${RELEASE_FILE}' && \
   rg -q 'def buildReleaseConformanceReport' '${RELEASE_FILE}' && \
   rg -q 'def releaseBuildGate' '${RELEASE_FILE}'"

check "theorem-pack API exports release conformance helpers" \
  "rg -q 'abbrev releaseConformanceReport' '${API_FILE}' && \
   rg -q 'abbrev releaseBuildGate' '${API_FILE}' && \
   rg -q 'abbrev hasFailureEnvelopeCrossTargetWitness' '${API_FILE}'"

check "Lean runtime tests cover certified replay conformance" \
  "rg -q 'replay conformance mismatch against certified equivalence class' '${TEST_FILE}'"

check "Justfile includes release conformance check target" \
  "rg -q '^check-release-conformance:' '${JUSTFILE}' && \
   rg -q 'just check-release-conformance' '${JUSTFILE}'"

if command -v lake >/dev/null 2>&1; then
  echo "Type-checking release-conformance Lean modules..."
  (
    cd "${ROOT_DIR}/lean"
    lake build Runtime.Proofs.TheoremPack.ReleaseConformance Runtime.Tests.Main >/dev/null
  )
  echo "OK   release-conformance Lean modules type-check successfully"
elif command -v elan >/dev/null 2>&1; then
  echo "Type-checking release-conformance Lean modules via elan..."
  (
    cd "${ROOT_DIR}"
    elan run leanprover/lean4:v4.26.0 lake --dir lean build \
      Runtime.Proofs.TheoremPack.ReleaseConformance Runtime.Tests.Main >/dev/null
  )
  echo "OK   release-conformance Lean modules type-check successfully"
else
  echo "WARN skipping Lean type-check in release-conformance script (no lake/elan)"
fi

mkdir -p "$(dirname "${REPORT_FILE}")"
mapfile -t inventory_keys < <(
  rg -o '\("([^"]+)", pack\.[^)]+\.isSome\)' "${INVENTORY_FILE}" \
    | sed -E 's/^\("([^"]+)".*/\1/'
)

{
  echo "{"
  echo "  \"version\": \"v2.release.conformance.v1\","
  echo "  \"report_kind\": \"theorem_pack_inventory_keyset\","
  echo "  \"inventory_keys\": ["
  for i in "${!inventory_keys[@]}"; do
    sep=","
    if [[ "${i}" -eq "$((${#inventory_keys[@]} - 1))" ]]; then
      sep=""
    fi
    printf '    "%s"%s\n' "${inventory_keys[$i]}" "${sep}"
  done
  echo "  ]"
  echo "}"
} > "${REPORT_FILE}"
echo "OK   release conformance report exported: ${REPORT_FILE}"

if [[ "${TT_RELEASE_TAGGED:-0}" == "1" ]]; then
  check "release-tagged mode enforces failure capability lane" \
    "${ROOT_DIR}/scripts/check-capability-gates.sh --failure >/dev/null"
  check "release-tagged mode enforces envelope conformance lane" \
    "${ROOT_DIR}/scripts/check-capability-gates.sh --envelope >/dev/null"
fi

echo ""
echo "Summary: ${checks} checks, ${errors} failure(s)."
if (( errors > 0 )); then
  exit 1
fi
