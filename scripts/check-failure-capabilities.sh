#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
FAILURE_FILE="${ROOT_DIR}/lean/Runtime/VM/Runtime/Failure.lean"
ADAPTER_FILE="${ROOT_DIR}/lean/Runtime/Proofs/Adapters/Distributed.lean"
THEOREMPACK_FILE="${ROOT_DIR}/lean/Runtime/Proofs/TheoremPack.lean"
TEST_FILE="${ROOT_DIR}/lean/Runtime/Tests/Main.lean"
STATE_FILE="${ROOT_DIR}/lean/Runtime/VM/Model/State.lean"
ENVELOPE_FILE="${ROOT_DIR}/lean/Runtime/Adequacy/EnvelopeCore.lean"

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
  "rg -q 'theorem decideRecovery_deterministic' '${FAILURE_FILE}' && \
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
  "rg -q 'just check-failure-capabilities' '${ROOT_DIR}/Justfile'"

echo ""
echo "Summary: ${checks} checks, ${errors} failure(s)."

if (( errors > 0 )); then
  exit 1
fi
