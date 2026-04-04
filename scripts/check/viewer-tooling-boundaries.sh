#!/usr/bin/env bash
# Keep portable viewer crates free of browser/runtime shell leakage and keep
# the shared crate split documented.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

if ! command -v rg >/dev/null 2>&1; then
  echo "error: ripgrep (rg) is required" >&2
  exit 2
fi

fail=0

check_no_hits() {
  local pattern="$1"
  shift
  local paths=("$@")
  local hits
  hits="$(rg -n "$pattern" "${paths[@]}" || true)"
  if [[ -n "$hits" ]]; then
    echo "viewer boundary violation for pattern: $pattern" >&2
    echo "$hits" >&2
    fail=1
  fi
}

check_has_hits() {
  local pattern="$1"
  local path="$2"
  if ! rg -q "$pattern" "$path"; then
    echo "expected to find '$pattern' in $path" >&2
    fail=1
  fi
}

check_no_hits 'web_sys|js_sys|wasm_bindgen|wasm_bindgen_futures' rust/viewer/src rust/ui/src
check_no_hits 'dioxus' rust/viewer/src
check_no_hits 'ScenarioBranchPatch|ScenarioPatchOperation' rust/ui/src rust/web/src
check_no_hits 'ViewerCommand::CreateBranch|ViewerCommand::UpdateBranch|ViewerCommand::DeleteBranch' rust/ui/src rust/web/src
check_no_hits 'SemanticComparisonResult \{|TheoremAwareCounterexample \{|MinimizationResult \{' rust/ui/src rust/web/src
check_no_hits 'EffectTraceArtifact \{|DeterministicSweepReport \{|ExperimentSuiteReport \{' rust/ui/src rust/web/src
check_has_hits 'telltale-viewer' docs/505_simulation_viewer.md
check_has_hits 'telltale-ui' docs/505_simulation_viewer.md
check_has_hits 'telltale-web' docs/505_simulation_viewer.md
check_has_hits 'Observed' docs/506_simulation_viewer_webapp.md
check_has_hits 'semantic comparison' docs/505_simulation_viewer.md
check_has_hits 'counterexample' docs/505_simulation_viewer.md
check_has_hits 'sweep' docs/506_simulation_viewer_webapp.md
check_has_hits 'effect' docs/506_simulation_viewer_webapp.md
check_has_hits 'downstream' docs/506_simulation_viewer_webapp.md

if [[ "$fail" -ne 0 ]]; then
  exit 1
fi

echo "viewer-tooling-boundaries: clean"
