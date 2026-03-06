#![allow(missing_docs)]

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use std::collections::BTreeMap;

use telltale_types::{GlobalType, Label, LocalTypeR, ValType};
use telltale_vm::coroutine::Value;
use telltale_vm::effect::EffectHandler;
use telltale_vm::loader::CodeImage;
use telltale_vm::vm::{
    ObservabilityRetentionConfig, ObservabilityRetentionMode, PayloadValidationMode, RunStatus,
};
use telltale_vm::{CommunicationReplayMode, Instr, VMConfig, VmMemoryUsage, VM};

struct BenchHandler;

impl EffectHandler for BenchHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> Result<Value, String> {
        Ok(Value::Unit)
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<Value>,
        _payload: &Value,
    ) -> Result<(), String> {
        Ok(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[Value],
    ) -> Result<String, String> {
        labels
            .first()
            .cloned()
            .ok_or_else(|| "no labels to choose from".to_string())
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
        Ok(())
    }
}

fn yield_image(num_roles: usize, yields_per_role: usize) -> CodeImage {
    let mut programs = BTreeMap::new();
    let mut local_types = BTreeMap::new();

    for idx in 0..num_roles {
        let role = format!("R{idx}");
        let mut code = Vec::with_capacity(yields_per_role + 1);
        for _ in 0..yields_per_role {
            code.push(Instr::Yield);
        }
        code.push(Instr::Halt);

        programs.insert(role.clone(), code);
        local_types.insert(role, LocalTypeR::End);
    }

    CodeImage {
        programs,
        global_type: GlobalType::End,
        local_types,
    }
}

fn send_recv_image(sender: &str, receiver: &str, label: &str) -> CodeImage {
    typed_send_recv_image(sender, receiver, label, None)
}

fn choice_image(sender: &str, receiver: &str, labels: &[&str]) -> CodeImage {
    let send_branches: Vec<_> = labels
        .iter()
        .map(|label| (Label::new(*label), None, LocalTypeR::End))
        .collect();
    let recv_branches: Vec<_> = labels
        .iter()
        .map(|label| (Label::new(*label), None, LocalTypeR::End))
        .collect();

    let mut local_types = BTreeMap::new();
    local_types.insert(
        sender.to_string(),
        LocalTypeR::send_choice(receiver, send_branches),
    );
    local_types.insert(
        receiver.to_string(),
        LocalTypeR::recv_choice(sender, recv_branches),
    );

    let global = GlobalType::comm(
        sender,
        receiver,
        labels
            .iter()
            .map(|label| (Label::new(*label), GlobalType::End))
            .collect(),
    );
    CodeImage::from_local_types(&local_types, &global)
}

fn typed_send_recv_image(
    sender: &str,
    receiver: &str,
    label: &str,
    expected: Option<ValType>,
) -> CodeImage {
    let mut local_types = BTreeMap::new();
    local_types.insert(
        sender.to_string(),
        LocalTypeR::Send {
            partner: receiver.into(),
            branches: vec![(Label::new(label), expected.clone(), LocalTypeR::End)],
        },
    );
    local_types.insert(
        receiver.to_string(),
        LocalTypeR::Recv {
            partner: sender.into(),
            branches: vec![(Label::new(label), expected, LocalTypeR::End)],
        },
    );

    let global = GlobalType::send(sender, receiver, Label::new(label), GlobalType::End);
    CodeImage::from_local_types(&local_types, &global)
}

fn capped_retention_config() -> ObservabilityRetentionConfig {
    ObservabilityRetentionConfig {
        mode: ObservabilityRetentionMode::Capped,
        capacity: 256,
    }
}

fn run_yield_workload(image: &CodeImage, max_rounds: usize) -> VmMemoryUsage {
    let mut vm = VM::new(VMConfig {
        observability_retention: capped_retention_config(),
        ..VMConfig::strict_minimal()
    });
    vm.load_choreography(image).expect("load choreography");
    let status = vm.run(&BenchHandler, max_rounds).expect("run vm");
    assert!(matches!(status, RunStatus::AllDone));
    vm.memory_usage()
}

fn run_short_lived_session_churn(iterations: usize) -> VmMemoryUsage {
    let image = yield_image(4, 8);
    let mut last_usage = VmMemoryUsage::default();

    for _ in 0..iterations {
        let mut vm = VM::new(VMConfig {
            observability_retention: capped_retention_config(),
            ..VMConfig::strict_churn()
        });
        let sid = vm.load_choreography(&image).expect("load choreography");
        let status = vm.run(&BenchHandler, 10_000).expect("run vm");
        assert!(matches!(status, RunStatus::AllDone));
        vm.sessions_mut().close(sid).expect("close session");
        let coro_ids: Vec<usize> = vm
            .session_coroutines(sid)
            .iter()
            .map(|coro| coro.id)
            .collect();
        for coro_id in coro_ids {
            vm.coroutine_mut(coro_id).expect("coroutine exists").status =
                telltale_vm::CoroStatus::Done;
        }
        let _ = vm.reap_closed_sessions();
        last_usage = vm.memory_usage();
    }

    last_usage
}

fn run_repeated_load_reuse(iterations: usize) -> VmMemoryUsage {
    let image = yield_image(16, 16);
    let mut vm = VM::new(VMConfig {
        observability_retention: capped_retention_config(),
        ..VMConfig::strict_large_fanout()
    });

    for _ in 0..iterations {
        vm.load_choreography(&image).expect("load choreography");
    }

    vm.memory_usage()
}

fn run_send_recv_workload(image: &CodeImage, config: VMConfig, iterations: usize) -> VmMemoryUsage {
    let mut vm = VM::new(config);

    for _ in 0..iterations {
        vm.load_choreography(image).expect("load choreography");
    }

    let status = vm.run(&BenchHandler, 100_000).expect("run vm");
    assert!(matches!(status, RunStatus::AllDone));
    vm.memory_usage()
}

fn run_choice_workload(config: VMConfig, iterations: usize) -> VmMemoryUsage {
    let image = choice_image("A", "B", &["left", "right", "other"]);
    run_send_recv_workload(&image, config, iterations)
}

fn bench_vm_run(c: &mut Criterion) {
    let handler = BenchHandler;
    let image_small = yield_image(8, 64);
    let image_wide = yield_image(32, 32);
    let send_recv = send_recv_image("A", "B", "msg");
    let typed_send_recv = typed_send_recv_image("A", "B", "msg", Some(ValType::Unit));

    eprintln!(
        "vm benchmark snapshot small: {:?}",
        run_yield_workload(&image_small, 10_000)
    );
    eprintln!(
        "vm benchmark snapshot wide: {:?}",
        run_yield_workload(&image_wide, 20_000)
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
        run_send_recv_workload(
            &send_recv,
            VMConfig {
                observability_retention: capped_retention_config(),
                communication_replay_mode: CommunicationReplayMode::Off,
                payload_validation_mode: PayloadValidationMode::Structural,
                ..VMConfig::strict_minimal()
            },
            32,
        )
    );
    eprintln!(
        "vm benchmark snapshot replay_sequence: {:?}",
        run_send_recv_workload(
            &send_recv,
            VMConfig {
                observability_retention: capped_retention_config(),
                communication_replay_mode: CommunicationReplayMode::Sequence,
                payload_validation_mode: PayloadValidationMode::Structural,
                ..VMConfig::strict_minimal()
            },
            32,
        )
    );
    eprintln!(
        "vm benchmark snapshot replay_nullifier: {:?}",
        run_send_recv_workload(
            &send_recv,
            VMConfig {
                observability_retention: capped_retention_config(),
                communication_replay_mode: CommunicationReplayMode::Nullifier,
                payload_validation_mode: PayloadValidationMode::Structural,
                ..VMConfig::strict_verified()
            },
            32,
        )
    );
    eprintln!(
        "vm benchmark snapshot choice_heavy: {:?}",
        run_choice_workload(
            VMConfig {
                observability_retention: capped_retention_config(),
                ..VMConfig::strict_observable()
            },
            32,
        )
    );

    c.bench_function("vm_run_yield_small", |b| {
        b.iter(|| {
            let mut vm = VM::new(VMConfig {
                observability_retention: capped_retention_config(),
                ..VMConfig::strict_minimal()
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
            let mut vm = VM::new(VMConfig {
                observability_retention: capped_retention_config(),
                ..VMConfig::strict_large_fanout()
            });
            vm.load_choreography(black_box(&image_wide))
                .expect("load choreography");
            let status = vm.run(&handler, 20_000).expect("run vm");
            assert!(matches!(status, RunStatus::AllDone));
            black_box((vm.trace().len(), vm.memory_usage()));
        })
    });

    c.bench_function("vm_short_lived_session_churn", |b| {
        b.iter(|| {
            let usage = run_short_lived_session_churn(black_box(32));
            black_box(usage);
        })
    });

    c.bench_function("vm_repeated_load_reuse", |b| {
        b.iter(|| {
            let usage = run_repeated_load_reuse(black_box(32));
            black_box(usage);
        })
    });

    c.bench_function("vm_send_recv_replay_off", |b| {
        b.iter(|| {
            let usage = run_send_recv_workload(
                &send_recv,
                VMConfig {
                    observability_retention: capped_retention_config(),
                    communication_replay_mode: CommunicationReplayMode::Off,
                    payload_validation_mode: PayloadValidationMode::Structural,
                    ..VMConfig::strict_minimal()
                },
                black_box(32),
            );
            black_box(usage);
        })
    });

    c.bench_function("vm_send_recv_replay_sequence", |b| {
        b.iter(|| {
            let usage = run_send_recv_workload(
                &send_recv,
                VMConfig {
                    observability_retention: capped_retention_config(),
                    communication_replay_mode: CommunicationReplayMode::Sequence,
                    payload_validation_mode: PayloadValidationMode::Structural,
                    ..VMConfig::strict_minimal()
                },
                black_box(32),
            );
            black_box(usage);
        })
    });

    c.bench_function("vm_send_recv_replay_nullifier", |b| {
        b.iter(|| {
            let usage = run_send_recv_workload(
                &send_recv,
                VMConfig {
                    observability_retention: capped_retention_config(),
                    communication_replay_mode: CommunicationReplayMode::Nullifier,
                    payload_validation_mode: PayloadValidationMode::Structural,
                    ..VMConfig::strict_verified()
                },
                black_box(32),
            );
            black_box(usage);
        })
    });

    c.bench_function("vm_send_recv_validation_off", |b| {
        b.iter(|| {
            let usage = run_send_recv_workload(
                &typed_send_recv,
                VMConfig {
                    observability_retention: capped_retention_config(),
                    communication_replay_mode: CommunicationReplayMode::Off,
                    payload_validation_mode: PayloadValidationMode::Off,
                    ..VMConfig::strict_minimal()
                },
                black_box(32),
            );
            black_box(usage);
        })
    });

    c.bench_function("vm_send_recv_validation_structural", |b| {
        b.iter(|| {
            let usage = run_send_recv_workload(
                &typed_send_recv,
                VMConfig {
                    observability_retention: capped_retention_config(),
                    communication_replay_mode: CommunicationReplayMode::Off,
                    payload_validation_mode: PayloadValidationMode::Structural,
                    ..VMConfig::strict_minimal()
                },
                black_box(32),
            );
            black_box(usage);
        })
    });

    c.bench_function("vm_send_recv_validation_strict_schema", |b| {
        b.iter(|| {
            let usage = run_send_recv_workload(
                &typed_send_recv,
                VMConfig {
                    observability_retention: capped_retention_config(),
                    communication_replay_mode: CommunicationReplayMode::Off,
                    payload_validation_mode: PayloadValidationMode::StrictSchema,
                    ..VMConfig::strict_verified()
                },
                black_box(32),
            );
            black_box(usage);
        })
    });

    c.bench_function("vm_choice_heavy", |b| {
        b.iter(|| {
            let usage = run_choice_workload(
                VMConfig {
                    observability_retention: capped_retention_config(),
                    ..VMConfig::strict_observable()
                },
                black_box(32),
            );
            black_box(usage);
        })
    });
}

criterion_group!(benches, bench_vm_run);
criterion_main!(benches);
