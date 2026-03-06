#![allow(missing_docs)]

use criterion::{black_box, Criterion};
use telltale_types::ValType;
use telltale_vm::vm::RunStatus;
use telltale_vm::VM;

use crate::common::{
    capped_retention_config, observable_choice_config, replay_nullifier_config, replay_off_config,
    replay_sequence_config, run_choice_workload, run_many_paused_scheduler_workload,
    run_repeated_load_reuse, run_send_recv_workload, run_short_lived_session_churn,
    run_yield_workload, send_recv_image, typed_send_recv_image, validation_off_config,
    validation_strict_schema_config, validation_structural_config, yield_image, BenchHandler,
};

pub(crate) fn bench_runtime(c: &mut Criterion) {
    let handler = BenchHandler;
    let image_small = yield_image(8, 64);
    let image_wide = yield_image(32, 32);
    let send_recv = send_recv_image("A", "B", "msg");
    let typed_send_recv = typed_send_recv_image("A", "B", "msg", Some(ValType::Unit));

    emit_runtime_snapshots(&image_small, &image_wide, &send_recv);

    c.bench_function("vm_run_yield_small", |b| {
        b.iter(|| {
            let mut vm = VM::new(telltale_vm::VMConfig {
                observability_retention: capped_retention_config(),
                ..telltale_vm::VMConfig::strict_minimal()
            });
            vm.load_choreography(black_box(&image_small))
                .expect("load choreography");
            let status = vm.run(&handler, 10_000).expect("run vm");
            assert!(matches!(status, RunStatus::AllDone));
            black_box((vm.trace().len(), vm.memory_usage()));
        })
    });

    c.bench_function("vm_run_yield_wide", |b| {
        b.iter(|| {
            let mut vm = VM::new(telltale_vm::VMConfig {
                observability_retention: capped_retention_config(),
                ..telltale_vm::VMConfig::strict_large_fanout()
            });
            vm.load_choreography(black_box(&image_wide))
                .expect("load choreography");
            let status = vm.run(&handler, 20_000).expect("run vm");
            assert!(matches!(status, RunStatus::AllDone));
            black_box((vm.trace().len(), vm.memory_usage()));
        })
    });

    c.bench_function("vm_short_lived_session_churn", |b| {
        b.iter(|| black_box(run_short_lived_session_churn(black_box(32))))
    });

    c.bench_function("vm_repeated_load_reuse", |b| {
        b.iter(|| black_box(run_repeated_load_reuse(black_box(32))))
    });

    c.bench_function("vm_send_recv_replay_off", |b| {
        b.iter(|| {
            black_box(run_send_recv_workload(
                &send_recv,
                replay_off_config(),
                black_box(32),
            ))
        })
    });

    c.bench_function("vm_send_recv_replay_sequence", |b| {
        b.iter(|| {
            black_box(run_send_recv_workload(
                &send_recv,
                replay_sequence_config(),
                black_box(32),
            ))
        })
    });

    c.bench_function("vm_send_recv_replay_nullifier", |b| {
        b.iter(|| {
            black_box(run_send_recv_workload(
                &send_recv,
                replay_nullifier_config(),
                black_box(32),
            ))
        })
    });

    c.bench_function("vm_send_recv_validation_off", |b| {
        b.iter(|| {
            black_box(run_send_recv_workload(
                &typed_send_recv,
                validation_off_config(),
                black_box(32),
            ))
        })
    });

    c.bench_function("vm_send_recv_validation_structural", |b| {
        b.iter(|| {
            black_box(run_send_recv_workload(
                &typed_send_recv,
                validation_structural_config(),
                black_box(32),
            ))
        })
    });

    c.bench_function("vm_send_recv_validation_strict_schema", |b| {
        b.iter(|| {
            black_box(run_send_recv_workload(
                &typed_send_recv,
                validation_strict_schema_config(),
                black_box(32),
            ))
        })
    });

    c.bench_function("vm_choice_heavy", |b| {
        b.iter(|| {
            black_box(run_choice_workload(
                observable_choice_config(),
                black_box(32),
            ))
        })
    });

    c.bench_function("vm_scheduler_many_paused", |b| {
        b.iter(|| {
            black_box(run_many_paused_scheduler_workload(
                black_box(256),
                black_box(8),
            ))
        })
    });
}

fn emit_runtime_snapshots(
    image_small: &telltale_vm::loader::CodeImage,
    image_wide: &telltale_vm::loader::CodeImage,
    send_recv: &telltale_vm::loader::CodeImage,
) {
    eprintln!(
        "vm benchmark snapshot small: {:?}",
        run_yield_workload(image_small, 10_000)
    );
    eprintln!(
        "vm benchmark snapshot wide: {:?}",
        run_yield_workload(image_wide, 20_000)
    );
    eprintln!(
        "vm benchmark snapshot churn: {:?}",
        run_short_lived_session_churn(32)
    );
    eprintln!(
        "vm benchmark snapshot repeated_load_reuse: {:?}",
        run_repeated_load_reuse(32)
    );
    eprintln!(
        "vm benchmark snapshot replay_off: {:?}",
        run_send_recv_workload(send_recv, replay_off_config(), 32)
    );
    eprintln!(
        "vm benchmark snapshot replay_sequence: {:?}",
        run_send_recv_workload(send_recv, replay_sequence_config(), 32)
    );
    eprintln!(
        "vm benchmark snapshot replay_nullifier: {:?}",
        run_send_recv_workload(send_recv, replay_nullifier_config(), 32)
    );
    eprintln!(
        "vm benchmark snapshot choice_heavy: {:?}",
        run_choice_workload(observable_choice_config(), 32)
    );
    eprintln!(
        "vm benchmark snapshot scheduler_many_paused: {:?}",
        run_many_paused_scheduler_workload(256, 8)
    );
}
