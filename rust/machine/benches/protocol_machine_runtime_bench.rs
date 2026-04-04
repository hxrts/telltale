//! Criterion benchmark harness for protocol machine runtime.
#![allow(missing_docs)]

#[path = "protocol_machine_bench_common.rs"]
mod common;
#[path = "protocol_machine_bench_runtime.rs"]
mod runtime;
#[path = "protocol_machine_bench_verification.rs"]
mod verification;

use criterion::{criterion_group, criterion_main, Criterion};

fn bench_vm_run(c: &mut Criterion) {
    runtime::bench_runtime(c);
    verification::bench_verification_and_allocations(c);
}

criterion_group!(benches, bench_vm_run);
criterion_main!(benches);
