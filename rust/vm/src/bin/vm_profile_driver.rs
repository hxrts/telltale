#![allow(missing_docs)]

use std::collections::BTreeMap;
use std::env;
use std::hint::black_box;

use telltale_types::{GlobalType, Label, LocalTypeR, ValType};
use telltale_vm::effect::EffectHandler;
use telltale_vm::loader::CodeImage;
use telltale_vm::vm::{
    ObservabilityRetentionConfig, ObservabilityRetentionMode, PayloadValidationMode,
};
use telltale_vm::{CommunicationReplayMode, Instr, VMConfig, VM};

struct ProfileHandler;

impl EffectHandler for ProfileHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[telltale_vm::coroutine::Value],
    ) -> Result<telltale_vm::coroutine::Value, String> {
        Ok(telltale_vm::coroutine::Value::Unit)
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<telltale_vm::coroutine::Value>,
        _payload: &telltale_vm::coroutine::Value,
    ) -> Result<(), String> {
        Ok(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[telltale_vm::coroutine::Value],
    ) -> Result<String, String> {
        labels
            .first()
            .cloned()
            .ok_or_else(|| "no labels to choose from".to_string())
    }

    fn step(
        &self,
        _role: &str,
        _state: &mut Vec<telltale_vm::coroutine::Value>,
    ) -> Result<(), String> {
        Ok(())
    }
}

fn main() {
    let mut args = env::args().skip(1);
    let workload = args.next().unwrap_or_else(|| usage_and_exit());
    let iterations = args
        .next()
        .map(|raw| raw.parse::<usize>().unwrap_or_else(|_| usage_and_exit()))
        .unwrap_or(256);

    let checksum = match workload.as_str() {
        "scheduler-many-paused" => profile_scheduler_many_paused(iterations),
        "scheduler-many-paused-run-only" => profile_scheduler_many_paused_run_only(iterations),
        "repeated-load-reuse" => profile_repeated_load_reuse(iterations),
        "send-recv-replay-nullifier" => profile_send_recv_replay_nullifier(iterations),
        "repeated-open-same-image" => profile_repeated_open_same_image(iterations),
        _ => usage_and_exit(),
    };

    println!("profile checksum: {checksum}");
}

fn usage_and_exit() -> ! {
    eprintln!(
        "usage: cargo run -p telltale-vm --release --bin vm_profile_driver -- \\\n\
         <scheduler-many-paused|scheduler-many-paused-run-only|repeated-load-reuse|send-recv-replay-nullifier|repeated-open-same-image> [iterations]"
    );
    std::process::exit(2);
}

fn capped_retention_config() -> ObservabilityRetentionConfig {
    ObservabilityRetentionConfig {
        mode: ObservabilityRetentionMode::Capped,
        capacity: 256,
    }
}

fn profile_scheduler_many_paused(iterations: usize) -> usize {
    let handler = ProfileHandler;
    let mut checksum = 0usize;
    for _ in 0..iterations {
        let image = yield_image(256, 8);
        let mut vm = VM::new(VMConfig {
            observability_retention: capped_retention_config(),
            ..VMConfig::strict_large_fanout()
        });
        vm.load_choreography(&image).expect("load choreography");
        for idx in 1..256 {
            vm.pause_role(&format!("R{idx}"));
        }
        let status = vm.run(&handler, 10_000).expect("run vm");
        checksum ^= black_box(vm.trace().len())
            ^ black_box(matches!(status, telltale_vm::vm::RunStatus::Stuck) as usize);
    }
    checksum
}

fn profile_repeated_load_reuse(iterations: usize) -> usize {
    let image = yield_image(16, 16);
    let mut config = VMConfig {
        observability_retention: capped_retention_config(),
        ..VMConfig::strict_large_fanout()
    };
    config.max_sessions = config.max_sessions.max(iterations.saturating_add(16));
    config.max_coroutines = config
        .max_coroutines
        .max(iterations.saturating_mul(16).saturating_add(16));
    let mut vm = VM::new(config);
    for _ in 0..iterations {
        vm.load_choreography(&image).expect("load choreography");
    }
    black_box(vm.memory_usage().retained_bytes.total)
}

fn profile_scheduler_many_paused_run_only(yields_per_role: usize) -> usize {
    let handler = ProfileHandler;
    let max_rounds = yields_per_role.max(1);
    let image = looping_yield_image(256);
    let mut vm = VM::new(VMConfig {
        observability_retention: capped_retention_config(),
        ..VMConfig::strict_large_fanout()
    });
    vm.load_choreography(&image).expect("load choreography");
    for idx in 1..256 {
        vm.pause_role(&format!("R{idx}"));
    }
    let status = vm.run(&handler, max_rounds).expect("run vm");
    black_box(vm.trace().len())
        ^ black_box(matches!(status, telltale_vm::vm::RunStatus::MaxRoundsExceeded) as usize)
}

fn profile_send_recv_replay_nullifier(iterations: usize) -> usize {
    let handler = ProfileHandler;
    let image = typed_send_recv_image("A", "B", "msg", Some(ValType::Unit));
    let mut vm = VM::new(VMConfig {
        observability_retention: capped_retention_config(),
        communication_replay_mode: CommunicationReplayMode::Nullifier,
        payload_validation_mode: PayloadValidationMode::Structural,
        ..VMConfig::strict_verified()
    });
    for _ in 0..iterations {
        vm.load_choreography(&image).expect("load choreography");
    }
    let status = vm.run(&handler, 100_000).expect("run vm");
    black_box(vm.trace().len())
        ^ black_box(matches!(status, telltale_vm::vm::RunStatus::AllDone) as usize)
}

fn profile_repeated_open_same_image(iterations: usize) -> usize {
    let image = yield_image(16, 16);
    let mut config = VMConfig {
        observability_retention: capped_retention_config(),
        ..VMConfig::strict_large_fanout()
    };
    config.max_sessions = config.max_sessions.max(iterations.saturating_add(16));
    config.max_coroutines = config
        .max_coroutines
        .max(iterations.saturating_mul(16).saturating_add(16));
    let mut vm = VM::new(config);
    let mut checksum = 0usize;
    for _ in 0..iterations {
        let (_, profile) = vm
            .load_choreography_profiled(&image)
            .expect("load choreography");
        checksum ^= black_box(profile.open_session_ns as usize)
            ^ black_box(profile.intern_and_open_event_ns as usize)
            ^ black_box(profile.spawn_coroutines_ns as usize);
    }
    checksum
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

fn looping_yield_image(num_roles: usize) -> CodeImage {
    let mut programs = BTreeMap::new();
    let mut local_types = BTreeMap::new();

    for idx in 0..num_roles {
        let role = format!("R{idx}");
        programs.insert(role.clone(), vec![Instr::Yield, Instr::Jump { target: 0 }]);
        local_types.insert(role, LocalTypeR::End);
    }

    CodeImage {
        programs,
        global_type: GlobalType::End,
        local_types,
    }
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
