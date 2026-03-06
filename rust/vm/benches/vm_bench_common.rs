#![allow(missing_docs)]

use std::alloc::{GlobalAlloc, Layout, System};
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering};

use telltale_types::{GlobalType, Label, LocalTypeR, ValType};
use telltale_vm::buffer::BufferConfig;
use telltale_vm::coroutine::Value;
use telltale_vm::effect::EffectHandler;
use telltale_vm::instr::Endpoint;
use telltale_vm::loader::CodeImage;
use telltale_vm::session::SessionStore;
use telltale_vm::vm::{
    ObservabilityRetentionConfig, ObservabilityRetentionMode, PayloadValidationMode, RunStatus,
};
use telltale_vm::{CommunicationReplayMode, Instr, VMConfig, VmMemoryUsage, VM};

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

pub(crate) fn replay_off_config() -> VMConfig {
    VMConfig {
        observability_retention: capped_retention_config(),
        communication_replay_mode: CommunicationReplayMode::Off,
        payload_validation_mode: PayloadValidationMode::Structural,
        ..VMConfig::strict_minimal()
    }
}

pub(crate) fn replay_sequence_config() -> VMConfig {
    VMConfig {
        observability_retention: capped_retention_config(),
        communication_replay_mode: CommunicationReplayMode::Sequence,
        payload_validation_mode: PayloadValidationMode::Structural,
        ..VMConfig::strict_minimal()
    }
}

pub(crate) fn replay_nullifier_config() -> VMConfig {
    VMConfig {
        observability_retention: capped_retention_config(),
        communication_replay_mode: CommunicationReplayMode::Nullifier,
        payload_validation_mode: PayloadValidationMode::Structural,
        ..VMConfig::strict_verified()
    }
}

pub(crate) fn validation_off_config() -> VMConfig {
    VMConfig {
        observability_retention: capped_retention_config(),
        communication_replay_mode: CommunicationReplayMode::Off,
        payload_validation_mode: PayloadValidationMode::Off,
        ..VMConfig::strict_minimal()
    }
}

pub(crate) fn validation_structural_config() -> VMConfig {
    VMConfig {
        observability_retention: capped_retention_config(),
        communication_replay_mode: CommunicationReplayMode::Off,
        payload_validation_mode: PayloadValidationMode::Structural,
        ..VMConfig::strict_minimal()
    }
}

pub(crate) fn validation_strict_schema_config() -> VMConfig {
    VMConfig {
        observability_retention: capped_retention_config(),
        communication_replay_mode: CommunicationReplayMode::Off,
        payload_validation_mode: PayloadValidationMode::StrictSchema,
        ..VMConfig::strict_verified()
    }
}

pub(crate) fn observable_choice_config() -> VMConfig {
    VMConfig {
        observability_retention: capped_retention_config(),
        ..VMConfig::strict_observable()
    }
}

pub(crate) fn run_yield_workload(image: &CodeImage, max_rounds: usize) -> VmMemoryUsage {
    let mut vm = VM::new(VMConfig {
        observability_retention: capped_retention_config(),
        ..VMConfig::strict_minimal()
    });
    vm.load_choreography(image).expect("load choreography");
    let status = vm.run(&BenchHandler, max_rounds).expect("run vm");
    assert!(matches!(status, RunStatus::AllDone));
    vm.memory_usage()
}

pub(crate) fn run_short_lived_session_churn(iterations: usize) -> VmMemoryUsage {
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

pub(crate) fn run_repeated_load_reuse(iterations: usize) -> VmMemoryUsage {
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

pub(crate) fn run_send_recv_workload(
    image: &CodeImage,
    config: VMConfig,
    iterations: usize,
) -> VmMemoryUsage {
    let mut vm = VM::new(config);

    for _ in 0..iterations {
        vm.load_choreography(image).expect("load choreography");
    }

    let status = vm.run(&BenchHandler, 100_000).expect("run vm");
    assert!(matches!(status, RunStatus::AllDone));
    vm.memory_usage()
}

pub(crate) fn run_choice_workload(config: VMConfig, iterations: usize) -> VmMemoryUsage {
    let image = choice_image("A", "B", &["left", "right", "other"]);
    run_send_recv_workload(&image, config, iterations)
}

pub(crate) fn run_many_paused_scheduler_workload(
    num_roles: usize,
    yields_per_role: usize,
) -> VmMemoryUsage {
    let image = yield_image(num_roles, yields_per_role);
    let mut vm = VM::new(VMConfig {
        observability_retention: capped_retention_config(),
        ..VMConfig::strict_large_fanout()
    });
    vm.load_choreography(&image).expect("load choreography");
    for idx in 1..num_roles {
        vm.pause_role(&format!("R{idx}"));
    }
    let status = vm.run(&BenchHandler, 10_000).expect("run vm");
    assert!(matches!(status, RunStatus::Stuck));
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
        let mut vm = VM::new(VMConfig::strict_large_fanout());
        vm.load_choreography(&image).expect("load choreography");
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
    let signature = telltale_vm::signValue(&payload, &key);
    (payload, signature)
}
