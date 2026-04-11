#![allow(missing_docs)]

mod support;

use criterion::{black_box, criterion_group, criterion_main, Criterion};

use support::{
    chain_domain, export_full_state_artifact, export_observation_artifact, fan_in_domain,
    invariant_check_frontier, run_machine_only, run_serial,
};

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("runtime_machine_only_chain_256", |b| {
        b.iter(|| run_machine_only(black_box(chain_domain(256)), 0, 256))
    });

    c.bench_function("runtime_executor_serial_chain_256", |b| {
        b.iter(|| run_serial(black_box(chain_domain(256)), 0, 256))
    });

    c.bench_function("runtime_observation_export_chain_256", |b| {
        b.iter(|| export_observation_artifact(black_box(chain_domain(256)), 0, 256))
    });

    c.bench_function("runtime_full_state_export_chain_256", |b| {
        b.iter(|| export_full_state_artifact(black_box(chain_domain(256)), 0, 256))
    });

    c.bench_function("runtime_invariant_check_frontier_512", |b| {
        b.iter(|| invariant_check_frontier(black_box(fan_in_domain(512)), 0, 513, 1))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
