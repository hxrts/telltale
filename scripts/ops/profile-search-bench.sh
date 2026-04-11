#!/usr/bin/env bash
set -euo pipefail

if ! command -v samply >/dev/null 2>&1; then
  echo "error: samply is required but not installed in this shell" >&2
  exit 1
fi

if [[ $# -lt 2 ]]; then
  echo "usage: $0 <bench-target> <bench-filter> [--features <cargo-features>] [--profile <cargo-profile>]" >&2
  exit 1
fi

bench_target="$1"
bench_filter="$2"
shift 2

cargo_profile="perf-cpu"
features=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --features)
      features="${2:-}"
      shift 2
      ;;
    --profile)
      cargo_profile="${2:-}"
      shift 2
      ;;
    *)
      echo "error: unknown argument: $1" >&2
      exit 1
      ;;
  esac
done

cmd=(cargo bench -p telltale-search --profile "$cargo_profile" --bench "$bench_target")
if [[ -n "$features" ]]; then
  cmd+=(--features "$features")
fi
cmd+=(-- "$bench_filter")

echo "profiling: ${cmd[*]}" >&2
exec samply record "${cmd[@]}"
