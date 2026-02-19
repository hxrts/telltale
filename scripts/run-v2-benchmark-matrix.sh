#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_DIR="${ROOT_DIR}/artifacts/v2/benchmark_matrix"
DISJOINT_OUT="${OUT_DIR}/disjoint.json"
CONTENDED_OUT="${OUT_DIR}/contended.json"
CONTENDED_M1_OUT="${OUT_DIR}/contended_m1_stress.json"
SUMMARY_OUT="${OUT_DIR}/summary.json"

mkdir -p "${OUT_DIR}"

echo "== V2 Benchmark Matrix =="
echo "-> disjoint workload"
cargo run -p telltale-vm --example v2_baseline_capture --features multi-thread -- \
  --workload disjoint \
  --output "${DISJOINT_OUT}"

echo "-> contended workload"
cargo run -p telltale-vm --example v2_baseline_capture --features multi-thread -- \
  --workload contended \
  --output "${CONTENDED_OUT}"

echo "-> contended M1-stress reference workload"
cargo run -p telltale-vm --example v2_baseline_capture --features multi-thread -- \
  --workload contended \
  --tuning-profile m1_stress_reference \
  --output "${CONTENDED_M1_OUT}"

python3 - "${DISJOINT_OUT}" "${CONTENDED_OUT}" "${CONTENDED_M1_OUT}" "${SUMMARY_OUT}" <<'PY'
import json
import sys
from pathlib import Path

disjoint_path = Path(sys.argv[1])
contended_path = Path(sys.argv[2])
contended_m1_path = Path(sys.argv[3])
summary_path = Path(sys.argv[4])

disjoint = json.loads(disjoint_path.read_text(encoding="utf-8"))
contended = json.loads(contended_path.read_text(encoding="utf-8"))
contended_m1 = json.loads(contended_m1_path.read_text(encoding="utf-8"))


def summarize(run: dict) -> dict:
    c = run["canonical"]
    t = run["threaded"]
    throughput_ratio = (t["throughput_steps_per_sec"] / c["throughput_steps_per_sec"]) if c["throughput_steps_per_sec"] else 0.0
    p99_regression = (
        ((t["p99_step_latency_us"] - c["p99_step_latency_us"]) / c["p99_step_latency_us"]) * 100.0
        if c["p99_step_latency_us"]
        else 0.0
    )
    return {
        "workload": run["workload"],
        "throughput_ratio_threaded_vs_canonical": throughput_ratio,
        "p99_latency_regression_percent": p99_regression,
        "threaded_lock_contention_events_per_1k_steps": t["lock_contention_events_per_1k_steps"],
        "threaded_mutex_lock_contention_events_per_1k_steps": t["mutex_lock_contention_events_per_1k_steps"],
        "threaded_planner_conflict_events_per_1k_steps": t["planner_conflict_events_per_1k_steps"],
        "canonical_mean_wave_width": c["mean_wave_width"],
        "threaded_mean_wave_width": t["mean_wave_width"],
        "threaded_max_wave_width": t["max_wave_width"],
    }


summary = {
    "schema_version": 1,
    "disjoint": summarize(disjoint),
    "contended": summarize(contended),
    "contended_m1_stress_reference": summarize(contended_m1),
    "lock_contention_reduction_vs_m1_stress_percent": (
        (
            contended_m1["threaded"]["lock_contention_events_per_1k_steps"]
            - contended["threaded"]["lock_contention_events_per_1k_steps"]
        )
        / contended_m1["threaded"]["lock_contention_events_per_1k_steps"]
        * 100.0
        if contended_m1["threaded"]["lock_contention_events_per_1k_steps"] > 0.0
        else 0.0
    ),
}
summary_path.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
print(json.dumps(summary, indent=2))
PY

echo "OK   wrote:"
echo "  - ${DISJOINT_OUT}"
echo "  - ${CONTENDED_OUT}"
echo "  - ${CONTENDED_M1_OUT}"
echo "  - ${SUMMARY_OUT}"
