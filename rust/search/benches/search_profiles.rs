#![allow(missing_docs)]

mod support;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use telltale_search::EpsilonMilli;

use support::{
    capture_rebuild_metrics, capture_selector_serial_metrics, capture_serial_metrics, chain_domain,
    duplicate_pressure_domain, fan_in_domain, grid_domain, grid_goal, print_case_metrics,
    run_rebuild_heavy_serial, run_selector_serial, run_serial, selector_candidate_domain,
};

const REBUILD_STEPS_PER_PHASE: u64 = 24;
const REBUILD_SCHEDULE: [EpsilonMilli; 4] = [
    EpsilonMilli(2_500),
    EpsilonMilli(2_000),
    EpsilonMilli(1_500),
    EpsilonMilli::one(),
];

fn emit_case_metrics() {
    print_case_metrics(
        "serial_chain_256",
        &capture_serial_metrics(chain_domain(256), 0, 256),
    );
    print_case_metrics(
        "serial_fan_in_128",
        &capture_serial_metrics(fan_in_domain(128), 0, 129),
    );
    print_case_metrics(
        "serial_duplicate_pressure_64x32",
        &capture_serial_metrics(duplicate_pressure_domain(64, 32), 0, 97),
    );
    let (selector_domain, selector_candidates) = selector_candidate_domain(128);
    print_case_metrics(
        "serial_selector_candidates_128",
        &capture_selector_serial_metrics(selector_domain, 0, selector_candidates),
    );
    print_case_metrics(
        "serial_grid_rebuild_heavy_32x32",
        &capture_rebuild_metrics(
            grid_domain(32, 32, 3),
            0,
            grid_goal(32, 32),
            REBUILD_STEPS_PER_PHASE,
            &REBUILD_SCHEDULE,
        ),
    );
    #[cfg(feature = "multi-thread")]
    print_case_metrics(
        "threaded_exact_single_lane_grid_32x32",
        &support::capture_threaded_exact_single_lane_metrics(
            grid_domain(32, 32, 3),
            0,
            grid_goal(32, 32),
        ),
    );
}

fn criterion_benchmark(c: &mut Criterion) {
    emit_case_metrics();

    c.bench_function("serial_chain_256", |b| {
        b.iter(|| run_serial(black_box(chain_domain(256)), 0, 256))
    });
    c.bench_function("serial_fan_in_128", |b| {
        b.iter(|| run_serial(black_box(fan_in_domain(128)), 0, 129))
    });
    c.bench_function("serial_duplicate_pressure_64x32", |b| {
        b.iter(|| run_serial(black_box(duplicate_pressure_domain(64, 32)), 0, 97))
    });
    c.bench_function("serial_selector_candidates_128", |b| {
        b.iter(|| {
            let (domain, candidates) = selector_candidate_domain(128);
            run_selector_serial(black_box(domain), 0, black_box(candidates))
        })
    });
    c.bench_function("serial_grid_rebuild_heavy_32x32", |b| {
        b.iter(|| {
            run_rebuild_heavy_serial(
                black_box(grid_domain(32, 32, 3)),
                0,
                grid_goal(32, 32),
                REBUILD_STEPS_PER_PHASE,
                &REBUILD_SCHEDULE,
            )
        })
    });
    #[cfg(feature = "multi-thread")]
    c.bench_function("threaded_exact_single_lane_grid_32x32", |b| {
        b.iter(|| {
            support::run_threaded_exact_single_lane(
                black_box(grid_domain(32, 32, 3)),
                0,
                grid_goal(32, 32),
            )
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
