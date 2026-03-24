#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"

if find lean/Runtime/ProtocolMachine -type f -name '*Lemmas.lean' | grep -q .; then
  echo "proof-only lemma modules remain under lean/Runtime/ProtocolMachine" >&2
  find lean/Runtime/ProtocolMachine -type f -name '*Lemmas.lean' >&2
  exit 1
fi

if rg -n '^\s*import Runtime\.Proofs' lean/Runtime/ProtocolMachine -g '*.lean' >/dev/null; then
  echo "protocol-machine implementation imports proof modules" >&2
  rg -n '^\s*import Runtime\.Proofs' lean/Runtime/ProtocolMachine -g '*.lean' >&2
  exit 1
fi

if rg -n '^\s*theorem(\s|$)' lean/Runtime/ProtocolMachine -g '*.lean' >/dev/null; then
  echo "theorem declarations remain under lean/Runtime/ProtocolMachine" >&2
  rg -n '^\s*theorem(\s|$)' lean/Runtime/ProtocolMachine -g '*.lean' >&2
  exit 1
fi
