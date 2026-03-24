#![allow(missing_docs)]

use std::alloc::{GlobalAlloc, Layout, System};
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering};

use telltale_types::{GlobalType, Label, LocalTypeR, ValType};
use telltale_vm::buffer::BufferConfig;
use telltale_vm::coroutine::Value;
use telltale_vm::effect::{
    EffectFailure, EffectHandler, EffectOutcome, EffectRequest, EffectRequestBody, EffectResponse,
    SendDecision,
};
use telltale_vm::instr::Endpoint;
use telltale_vm::loader::CodeImage;
use telltale_vm::session::SessionStore;
use telltale_vm::{
    CommunicationReplayMode, Instr, ObservabilityRetentionConfig, ObservabilityRetentionMode,
    PayloadValidationMode, ProtocolMachine, ProtocolMachineConfig, ProtocolMachineMemoryUsage,
    ProtocolMachineRunStatus,
};

pub(crate) struct CountingAllocator;

pub(crate) static ALLOC_CALLS: AtomicUsize = AtomicUsize::new(0);

#[global_allocator]
static GLOBAL_ALLOCATOR: CountingAllocator = CountingAllocator;

unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOC_CALLS.fetch_add(1, Ordering::Relaxed);
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        ALLOC_CALLS.fetch_add(1, Ordering::Relaxed);
        unsafe { System.realloc(ptr, layout, new_size) }
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        ALLOC_CALLS.fetch_add(1, Ordering::Relaxed);
        unsafe { System.alloc_zeroed(layout) }
    }
}

pub(crate) fn count_allocations<F, T>(f: F) -> (T, usize)
where
    F: FnOnce() -> T,
{
    let before = ALLOC_CALLS.load(Ordering::Relaxed);
    let value = f();
    let after = ALLOC_CALLS.load(Ordering::Relaxed);
    (value, after.saturating_sub(before))
}

pub(crate) struct BenchHandler;

impl EffectHandler for BenchHandler {
    fn handle_effect(&self, request: EffectRequest) -> EffectOutcome {
        match request.body {
            EffectRequestBody::SendDecision { payload, .. } => {
                EffectOutcome::success(EffectResponse::SendDecision {
                    decision: SendDecision::Deliver(payload.unwrap_or(Value::Unit)),
                })
            }
            EffectRequestBody::Receive { state, .. } => {
                EffectOutcome::success(EffectResponse::Receive { state })
            }
            EffectRequestBody::Choose { labels, .. } => match labels.first().cloned() {
                Some(label) => EffectOutcome::success(EffectResponse::Choose { label }),
                None => EffectOutcome::failure(EffectFailure::invalid_input(
                    "labels should contain at least one branch",
                )),
            },
            EffectRequestBody::InvokeStep { state, .. } => {
                EffectOutcome::success(EffectResponse::InvokeStep { state })
            }
            EffectRequestBody::Acquire { .. } => EffectOutcome::success(EffectResponse::Acquire {
                evidence: Value::Bool(true),
            }),
            EffectRequestBody::Release { .. } => EffectOutcome::success(EffectResponse::Release),
            EffectRequestBody::TopologyEvents { .. } => {
                EffectOutcome::success(EffectResponse::TopologyEvents { events: Vec::new() })
            }
            EffectRequestBody::OutputConditionHint { .. } => {
                EffectOutcome::success(EffectResponse::OutputConditionHint { hint: None })
            }
        }
    }

    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> telltale_vm::effect::EffectResult<Value> {
        telltale_vm::effect::EffectResult::success(Value::Unit)
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<Value>,
        _payload: &Value,
    ) -> telltale_vm::effect::EffectResult<()> {
        telltale_vm::effect::EffectResult::success(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[Value],
    ) -> telltale_vm::effect::EffectResult<String> {
        telltale_vm::effect::EffectResult::success(
            labels
                .first()
                .cloned()
                .expect("labels should contain at least one branch"),
        )
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> telltale_vm::effect::EffectResult<()> {
        telltale_vm::effect::EffectResult::success(())
    }
}

pub(crate) fn yield_image(num_roles: usize, yields_per_role: usize) -> CodeImage {
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

pub(crate) fn send_recv_image(sender: &str, receiver: &str, label: &str) -> CodeImage {
    typed_send_recv_image(sender, receiver, label, None)
}

pub(crate) fn choice_image(sender: &str, receiver: &str, labels: &[&str]) -> CodeImage {
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

pub(crate) fn typed_send_recv_image(
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

pub(crate) fn capped_retention_config() -> ObservabilityRetentionConfig {
    ObservabilityRetentionConfig {
        mode: ObservabilityRetentionMode::Capped,
        capacity: 256,
    }
}

pub(crate) fn replay_off_config() -> ProtocolMachineConfig {
    ProtocolMachineConfig {
        observability_retention: capped_retention_config(),
        communication_replay_mode: CommunicationReplayMode::Off,
        payload_validation_mode: PayloadValidationMode::Structural,
        ..ProtocolMachineConfig::strict_minimal()
    }
}

pub(crate) fn replay_sequence_config() -> ProtocolMachineConfig {
    ProtocolMachineConfig {
        observability_retention: capped_retention_config(),
        communication_replay_mode: CommunicationReplayMode::Sequence,
        payload_validation_mode: PayloadValidationMode::Structural,
        ..ProtocolMachineConfig::strict_minimal()
    }
}

pub(crate) fn replay_nullifier_config() -> ProtocolMachineConfig {
    ProtocolMachineConfig {
        observability_retention: capped_retention_config(),
        communication_replay_mode: CommunicationReplayMode::Nullifier,
        payload_validation_mode: PayloadValidationMode::Structural,
        ..ProtocolMachineConfig::strict_verified()
    }
}

pub(crate) fn validation_off_config() -> ProtocolMachineConfig {
    ProtocolMachineConfig {
        observability_retention: capped_retention_config(),
        communication_replay_mode: CommunicationReplayMode::Off,
        payload_validation_mode: PayloadValidationMode::Off,
        ..ProtocolMachineConfig::strict_minimal()
    }
}

pub(crate) fn validation_structural_config() -> ProtocolMachineConfig {
    ProtocolMachineConfig {
        observability_retention: capped_retention_config(),
        communication_replay_mode: CommunicationReplayMode::Off,
        payload_validation_mode: PayloadValidationMode::Structural,
        ..ProtocolMachineConfig::strict_minimal()
    }
}

pub(crate) fn validation_strict_schema_config() -> ProtocolMachineConfig {
    ProtocolMachineConfig {
        observability_retention: capped_retention_config(),
        communication_replay_mode: CommunicationReplayMode::Off,
        payload_validation_mode: PayloadValidationMode::StrictSchema,
        ..ProtocolMachineConfig::strict_verified()
    }
}

pub(crate) fn observable_choice_config() -> ProtocolMachineConfig {
    ProtocolMachineConfig {
        observability_retention: capped_retention_config(),
        ..ProtocolMachineConfig::strict_observable()
    }
}

pub(crate) fn run_yield_workload(
    image: &CodeImage,
    max_rounds: usize,
) -> ProtocolMachineMemoryUsage {
    let mut vm = ProtocolMachine::new(ProtocolMachineConfig {
        observability_retention: capped_retention_config(),
        ..ProtocolMachineConfig::strict_minimal()
    });
    let _owned = vm
        .load_choreography_owned(image, "bench/yield")
        .expect("load choreography");
    let status = vm.run(&BenchHandler, max_rounds).expect("run vm");
    assert!(matches!(status, ProtocolMachineRunStatus::AllDone));
    vm.memory_usage()
}

pub(crate) fn run_short_lived_session_churn(iterations: usize) -> ProtocolMachineMemoryUsage {
    let image = yield_image(4, 8);
    let mut last_usage = ProtocolMachineMemoryUsage::default();

    for idx in 0..iterations {
        let mut vm = ProtocolMachine::new(ProtocolMachineConfig {
            observability_retention: capped_retention_config(),
            ..ProtocolMachineConfig::strict_churn()
        });
        let owned = vm
            .load_choreography_owned(&image, format!("bench/churn/{idx}"))
            .expect("load choreography");
        let sid = owned.session_id();
        let status = vm.run(&BenchHandler, 10_000).expect("run vm");
        assert!(matches!(status, ProtocolMachineRunStatus::AllDone));
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

pub(crate) fn run_repeated_load_reuse(iterations: usize) -> ProtocolMachineMemoryUsage {
    let image = yield_image(16, 16);
    let mut vm = ProtocolMachine::new(ProtocolMachineConfig {
        observability_retention: capped_retention_config(),
        ..ProtocolMachineConfig::strict_large_fanout()
    });

    for idx in 0..iterations {
        let _owned = vm
            .load_choreography_owned(&image, format!("bench/reuse/{idx}"))
            .expect("load choreography");
    }

    vm.memory_usage()
}

pub(crate) fn run_repeated_open_same_image(
    iterations: usize,
    num_roles: usize,
    yields_per_role: usize,
) -> ProtocolMachineMemoryUsage {
    let image = yield_image(num_roles, yields_per_role);
    let mut config = ProtocolMachineConfig {
        observability_retention: capped_retention_config(),
        ..ProtocolMachineConfig::strict_large_fanout()
    };
    config.max_coroutines = config
        .max_coroutines
        .max(iterations.saturating_mul(num_roles).saturating_add(16));
    let mut vm = ProtocolMachine::new(config);
    for idx in 0..iterations {
        let _owned = vm
            .load_choreography_owned(&image, format!("bench/open/{idx}"))
            .expect("load choreography");
    }
    vm.memory_usage()
}

pub(crate) fn run_repeated_open_wide_roles(
    iterations: usize,
    num_roles: usize,
) -> ProtocolMachineMemoryUsage {
    run_repeated_open_same_image(iterations, num_roles, 1)
}

pub(crate) fn run_send_recv_workload(
    image: &CodeImage,
    config: ProtocolMachineConfig,
    iterations: usize,
) -> ProtocolMachineMemoryUsage {
    let mut vm = ProtocolMachine::new(config);

    for idx in 0..iterations {
        let _owned = vm
            .load_choreography_owned(image, format!("bench/send_recv/{idx}"))
            .expect("load choreography");
    }

    let status = vm.run(&BenchHandler, 100_000).expect("run vm");
    assert!(matches!(status, ProtocolMachineRunStatus::AllDone));
    vm.memory_usage()
}

pub(crate) fn run_choice_workload(
    config: ProtocolMachineConfig,
    iterations: usize,
) -> ProtocolMachineMemoryUsage {
    let image = choice_image("A", "B", &["left", "right", "other"]);
    run_send_recv_workload(&image, config, iterations)
}

pub(crate) fn run_many_paused_scheduler_workload(
    num_roles: usize,
    yields_per_role: usize,
) -> ProtocolMachineMemoryUsage {
    let mut vm = setup_many_paused_scheduler_vm(num_roles, yields_per_role);
    let status = vm.run(&BenchHandler, 10_000).expect("run vm");
    assert!(matches!(status, ProtocolMachineRunStatus::Stuck));
    vm.memory_usage()
}

pub(crate) fn setup_many_paused_scheduler_vm(
    num_roles: usize,
    yields_per_role: usize,
) -> ProtocolMachine {
    let image = yield_image(num_roles, yields_per_role);
    let mut vm = ProtocolMachine::new(ProtocolMachineConfig {
        observability_retention: capped_retention_config(),
        ..ProtocolMachineConfig::strict_large_fanout()
    });
    let _owned = vm
        .load_choreography_owned(&image, "bench/many_paused")
        .expect("load choreography");
    for idx in 1..num_roles {
        vm.pause_role(&format!("R{idx}"));
    }
    vm
}

pub(crate) fn run_pause_resume_churn_workload(
    num_roles: usize,
    iterations: usize,
) -> ProtocolMachineMemoryUsage {
    let image = yield_image(num_roles, 4);
    let mut vm = ProtocolMachine::new(ProtocolMachineConfig {
        observability_retention: capped_retention_config(),
        ..ProtocolMachineConfig::strict_large_fanout()
    });
    let _owned = vm
        .load_choreography_owned(&image, "bench/pause_resume")
        .expect("load choreography");
    for idx in 1..num_roles {
        vm.pause_role(&format!("R{idx}"));
    }
    for _ in 0..iterations {
        vm.resume_role("R1");
        vm.pause_role("R1");
    }
    vm.memory_usage()
}

pub(crate) fn session_open_allocation_count(num_roles: usize) -> usize {
    let roles: Vec<String> = (0..num_roles).map(|idx| format!("R{idx}")).collect();
    let local_types: BTreeMap<String, LocalTypeR> = roles
        .iter()
        .cloned()
        .map(|role| (role, LocalTypeR::End))
        .collect();
    let (_, allocations) = count_allocations(|| {
        let mut store = SessionStore::new();
        store.open_with_sid(0, roles, &BufferConfig::default(), &local_types)
    });
    allocations
}

pub(crate) fn choreography_load_allocation_count(
    num_roles: usize,
    yields_per_role: usize,
) -> usize {
    let image = yield_image(num_roles, yields_per_role);
    let (_, allocations) = count_allocations(|| {
        let mut vm = ProtocolMachine::new(ProtocolMachineConfig::strict_large_fanout());
        let _owned = vm
            .load_choreography_owned(&image, "bench/alloc")
            .expect("load choreography");
        vm
    });
    allocations
}

pub(crate) fn signing_fixture() -> (Value, telltale_vm::Signature) {
    let endpoint = Endpoint {
        sid: 7,
        role: "A".to_string(),
    };
    let payload = Value::Prod(Box::new(Value::Nat(7)), Box::new(Value::Bool(true)));
    let key = telltale_vm::verification::signing_key_for_endpoint(&endpoint);
    let signature = telltale_vm::sign_value(&payload, &key);
    (payload, signature)
}
