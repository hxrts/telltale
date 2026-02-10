#!/usr/bin/env bash
set -euo pipefail

# Strict Lean-core conformance lane (cooperative + threaded).

cargo test -p telltale-vm --test conformance_lean
cargo test -p telltale-vm --test equivalence_lean
cargo test -p telltale-vm --test lean_vm_equivalence
cargo test -p telltale-vm --test trace_corpus
cargo test -p telltale-vm --test strict_tick_equality

cargo test -p telltale-vm --test differential_step_corpus
cargo test -p telltale-vm --test strict_value_rejection
cargo test -p telltale-vm --test instruction_fault_snapshots
cargo test -p telltale-vm --test schedule_robustness
cargo test -p telltale-vm --test serialization_strict_lean
cargo test -p telltale-vm --test bytecode_mutation_conformance

TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-vm --features multi-thread --test threaded_feature_contract
TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-vm --features multi-thread --test threaded_equivalence
TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-vm --features multi-thread --test threaded_lane_runtime
TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-vm --features multi-thread --test differential_step_corpus
TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-vm --features multi-thread --test schedule_robustness
