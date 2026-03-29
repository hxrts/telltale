#!/usr/bin/env bash
set -euo pipefail

cargo test --test docs_contract_tests -- --nocapture
echo "docs-as-contract: ok"
