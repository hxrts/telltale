#![allow(missing_docs)]

mod support;

use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};
use telltale_search::{EpsilonMilli, SearchMachine};

use support::{
    duplicate_pressure_domain, fan_in_domain, grid_domain, grid_goal, prepare_frontier_machine,
};

fn criterion_benchmark(c: &mut Criterion) {
    let next_batch_machine = prepare_frontier_machine(fan_in_domain(512), 0, 513, 1);
    c.bench_function("phase_next_batch_frontier_512", |b| {
        b.iter(|| {
            black_box(
                next_batch_machine
                    .next_batch()
                    .expect("prepared frontier should have a batch"),
            )
        })
    });

    let expand_machine = prepare_frontier_machine(fan_in_domain(512), 0, 513, 1);
    let expand_batch = expand_machine
        .next_batch()
        .expect("prepared frontier should have a batch");
    c.bench_function("phase_expand_batch_frontier_512", |b| {
        b.iter(|| {
            expand_machine
                .expand_batch(black_box(&expand_batch))
                .expect("expand batch benchmark")
        })
    });

    let normalize_machine = prepare_frontier_machine(duplicate_pressure_domain(64, 32), 0, 97, 1);
    let normalize_batch = normalize_machine
        .next_batch()
        .expect("prepared duplicate-pressure frontier should have a batch");
    let normalize_proposals = normalize_machine
        .expand_batch(&normalize_batch)
        .expect("normalize proposal seed");
    c.bench_function("phase_normalize_proposals_duplicate_pressure_64x32", |b| {
        b.iter_batched(
            || normalize_proposals.clone(),
            |mut proposals| {
                normalize_machine.normalize_proposals(black_box(&mut proposals));
                black_box(proposals)
            },
            BatchSize::SmallInput,
        )
    });

    c.bench_function("phase_commit_proposals_duplicate_pressure_64x32", |b| {
        b.iter_batched(
            || {
                let mut machine =
                    prepare_frontier_machine(duplicate_pressure_domain(64, 32), 0, 97, 1);
                let batch = machine
                    .next_batch()
                    .expect("prepared duplicate-pressure frontier should have a batch");
                let mut proposals = machine.expand_batch(&batch).expect("commit proposal seed");
                machine.activate_batch(&batch);
                machine.normalize_proposals(&mut proposals);
                (machine, proposals)
            },
            |(mut machine, proposals)| {
                black_box(machine.commit_proposals(black_box(&proposals)));
            },
            BatchSize::SmallInput,
        )
    });

    c.bench_function("phase_decrease_epsilon_and_rebuild_grid_32x32", |b| {
        b.iter_batched(
            || {
                let mut machine = SearchMachine::new(
                    grid_domain(32, 32, 3),
                    1,
                    0,
                    grid_goal(32, 32),
                    EpsilonMilli(3_000),
                );
                for _ in 0..32 {
                    if !machine.step_once().expect("rebuild warmup step") {
                        break;
                    }
                }
                if machine.state().open.is_empty() {
                    let _ = machine.step_once().expect("rebuild warmup step");
                }
                machine
            },
            |mut machine| {
                machine.decrease_epsilon_and_rebuild(EpsilonMilli(1_500));
                black_box(machine);
            },
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
