//! Shared test infrastructure for VM conformance tests.

use std::collections::BTreeMap;
use std::sync::Mutex;

use proptest::prelude::*;
use telltale_types::{FixedQ32, GlobalType, Label, LocalTypeR};
use telltale_vm::buffer::{BackpressurePolicy, BufferConfig, BufferMode};
use telltale_vm::coroutine::Value;
use telltale_vm::effect::EffectHandler;
use telltale_vm::loader::CodeImage;
use telltale_vm::vm::{ObsEvent, StepResult, VMError, VM};

/// Deterministic seed for reproducibility.
pub const SEED: [u8; 32] = [
    0x56, 0x4D, 0x43, 0x6F, 0x6E, 0x66, 0x6F, 0x72, // "VMConfor"
    0x6D, 0x61, 0x6E, 0x63, 0x65, 0x54, 0x65, 0x73, // "manceTes"
    0x74, 0x53, 0x75, 0x69, 0x74, 0x65, 0x56, 0x31, // "tSuiteV1"
    0x52, 0x75, 0x73, 0x74, 0x56, 0x4D, 0x30, 0x31, // "RustVM01"
];

// ============================================================================
// Handlers
// ============================================================================

/// Returns `Value::Int(42)` on send, no-op on recv/step.
pub struct PassthroughHandler;

impl EffectHandler for PassthroughHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> Result<Value, String> {
        Ok(Value::Int(42))
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
            .ok_or_else(|| "no labels available".into())
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
        Ok(())
    }
}

/// Records all (role, partner, label) triples for send/recv/step calls.
pub struct RecordingHandler {
    pub sends: Mutex<Vec<(String, String, String)>>,
    pub recvs: Mutex<Vec<(String, String, String)>>,
    pub steps: Mutex<Vec<String>>,
}

impl RecordingHandler {
    pub fn new() -> Self {
        Self {
            sends: Mutex::new(Vec::new()),
            recvs: Mutex::new(Vec::new()),
            steps: Mutex::new(Vec::new()),
        }
    }
}

impl EffectHandler for RecordingHandler {
    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        _state: &[Value],
    ) -> Result<Value, String> {
        self.sends
            .lock()
            .expect("recording handler lock poisoned")
            .push((role.into(), partner.into(), label.into()));
        Ok(Value::Int(42))
    }

    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        _state: &mut Vec<Value>,
        _payload: &Value,
    ) -> Result<(), String> {
        self.recvs
            .lock()
            .expect("recording handler lock poisoned")
            .push((role.into(), partner.into(), label.into()));
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
            .ok_or_else(|| "no labels available".into())
    }

    fn step(&self, role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
        self.steps
            .lock()
            .expect("recording handler lock poisoned")
            .push(role.into());
        Ok(())
    }
}

/// Returns `Err(...)` from send/recv/step.
pub struct FailingHandler {
    pub message: String,
}

impl FailingHandler {
    pub fn new(msg: &str) -> Self {
        Self {
            message: msg.into(),
        }
    }
}

impl EffectHandler for FailingHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> Result<Value, String> {
        Err(self.message.clone())
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<Value>,
        _payload: &Value,
    ) -> Result<(), String> {
        Err(self.message.clone())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        _labels: &[String],
        _state: &[Value],
    ) -> Result<String, String> {
        Err(self.message.clone())
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
        Err(self.message.clone())
    }
}

// ============================================================================
// Builders
// ============================================================================

/// Simple A→B:label, then End.
pub fn simple_send_recv_image(sender: &str, receiver: &str, label: &str) -> CodeImage {
    let mut local_types = BTreeMap::new();
    local_types.insert(
        sender.to_string(),
        LocalTypeR::Send {
            partner: receiver.into(),
            branches: vec![(Label::new(label), None, LocalTypeR::End)],
        },
    );
    local_types.insert(
        receiver.to_string(),
        LocalTypeR::Recv {
            partner: sender.into(),
            branches: vec![(Label::new(label), None, LocalTypeR::End)],
        },
    );

    let global = GlobalType::send(sender, receiver, Label::new(label), GlobalType::End);
    CodeImage::from_local_types(&local_types, &global)
}

/// Recursive mu loop: A→B:label, B→A:label, repeat.
pub fn recursive_send_recv_image(sender: &str, receiver: &str, label: &str) -> CodeImage {
    let mut local_types = BTreeMap::new();
    local_types.insert(
        sender.to_string(),
        LocalTypeR::mu(
            "loop",
            LocalTypeR::Send {
                partner: receiver.into(),
                branches: vec![(
                    Label::new(label),
                    None,
                    LocalTypeR::Recv {
                        partner: receiver.into(),
                        branches: vec![(Label::new(label), None, LocalTypeR::var("loop"))],
                    },
                )],
            },
        ),
    );
    local_types.insert(
        receiver.to_string(),
        LocalTypeR::mu(
            "loop",
            LocalTypeR::Recv {
                partner: sender.into(),
                branches: vec![(
                    Label::new(label),
                    None,
                    LocalTypeR::Send {
                        partner: sender.into(),
                        branches: vec![(Label::new(label), None, LocalTypeR::var("loop"))],
                    },
                )],
            },
        ),
    );

    let global = GlobalType::mu(
        "loop",
        GlobalType::send(
            sender,
            receiver,
            Label::new(label),
            GlobalType::send(receiver, sender, Label::new(label), GlobalType::var("loop")),
        ),
    );
    CodeImage::from_local_types(&local_types, &global)
}

/// Multi-branch choice: sender chooses among labels, receiver offers.
pub fn choice_image(sender: &str, receiver: &str, labels: &[&str]) -> CodeImage {
    let send_branches: Vec<_> = labels
        .iter()
        .map(|l| (Label::new(*l), None, LocalTypeR::End))
        .collect();
    let recv_branches: Vec<_> = labels
        .iter()
        .map(|l| (Label::new(*l), None, LocalTypeR::End))
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

    let global_branches: Vec<_> = labels
        .iter()
        .map(|l| (Label::new(*l), GlobalType::End))
        .collect();
    let global = GlobalType::comm(sender, receiver, global_branches);

    CodeImage::from_local_types(&local_types, &global)
}

/// Step a VM to completion, collecting the trace.
pub fn run_to_completion(
    vm: &mut VM,
    handler: &dyn EffectHandler,
    max_steps: usize,
) -> Result<Vec<ObsEvent>, VMError> {
    for _ in 0..max_steps {
        match vm.step(handler)? {
            StepResult::AllDone | StepResult::Stuck => break,
            StepResult::Continue => {}
        }
    }
    Ok(vm.trace().to_vec())
}

// ============================================================================
// Proptest Strategies
// ============================================================================

pub fn label_strategy() -> impl Strategy<Value = Label> {
    prop_oneof![
        Just(Label::new("msg")),
        Just(Label::new("ack")),
        Just(Label::new("data")),
        Just(Label::new("req")),
        Just(Label::new("resp")),
        Just(Label::new("yes")),
        Just(Label::new("no")),
        Just(Label::new("done")),
    ]
}

pub fn role_pair_strategy() -> impl Strategy<Value = (String, String)> {
    let roles = ["A", "B", "C", "D"];
    (0..roles.len(), 0..roles.len())
        .prop_filter("distinct roles", |(a, b)| a != b)
        .prop_map(move |(a, b)| (roles[a].to_string(), roles[b].to_string()))
}

pub fn value_strategy() -> impl Strategy<Value = Value> {
    prop_oneof![
        Just(Value::Unit),
        any::<i64>().prop_map(Value::Int),
        // FixedQ32 has 32 integer bits, so restrict i64 range to fit
        (-2_147_483_648_i64..2_147_483_647_i64)
            .prop_map(|i| FixedQ32::try_from_i64(i).expect("i32-range i64 should map to FixedQ32"))
            .prop_map(Value::Real),
        any::<bool>().prop_map(Value::Bool),
        Just(Value::Label("msg".into())),
    ]
}

pub fn well_formed_global_strategy(depth: usize) -> BoxedStrategy<GlobalType> {
    if depth == 0 {
        Just(GlobalType::End).boxed()
    } else {
        prop_oneof![
            Just(GlobalType::End),
            // Simple send
            role_pair_strategy().prop_flat_map(move |(s, r)| {
                label_strategy().prop_flat_map(move |l| {
                    let s = s.clone();
                    let r = r.clone();
                    well_formed_global_strategy(depth - 1)
                        .prop_map(move |cont| GlobalType::send(&s, &r, l.clone(), cont))
                })
            }),
            // Binary choice
            role_pair_strategy().prop_flat_map(move |(s, r)| {
                (
                    well_formed_global_strategy(depth - 1),
                    well_formed_global_strategy(depth - 1),
                )
                    .prop_map(move |(c1, c2)| {
                        GlobalType::comm(
                            &s,
                            &r,
                            vec![(Label::new("yes"), c1), (Label::new("no"), c2)],
                        )
                    })
            }),
            // Guarded recursion
            role_pair_strategy().prop_map(|(s, r)| {
                GlobalType::mu(
                    "t",
                    GlobalType::comm(
                        &s,
                        &r,
                        vec![
                            (Label::new("continue"), GlobalType::var("t")),
                            (Label::new("stop"), GlobalType::End),
                        ],
                    ),
                )
            }),
        ]
        .boxed()
    }
}

pub fn buffer_config_strategy() -> impl Strategy<Value = BufferConfig> {
    prop_oneof![
        Just(BufferConfig {
            mode: BufferMode::Fifo,
            initial_capacity: 4,
            policy: BackpressurePolicy::Block,
        }),
        Just(BufferConfig {
            mode: BufferMode::Fifo,
            initial_capacity: 4,
            policy: BackpressurePolicy::Drop,
        }),
        Just(BufferConfig {
            mode: BufferMode::Fifo,
            initial_capacity: 4,
            policy: BackpressurePolicy::Error,
        }),
        Just(BufferConfig {
            mode: BufferMode::Fifo,
            initial_capacity: 4,
            policy: BackpressurePolicy::Resize { max_capacity: 64 },
        }),
        Just(BufferConfig {
            mode: BufferMode::LatestValue,
            initial_capacity: 1,
            policy: BackpressurePolicy::Block,
        }),
    ]
}

/// Project a well-formed GlobalType and compile to CodeImage.
/// Returns None if projection fails.
pub fn code_image_from_global(global: &GlobalType) -> Option<CodeImage> {
    let projected: BTreeMap<String, LocalTypeR> = telltale_theory::projection::project_all(global)
        .ok()?
        .into_iter()
        .collect();
    Some(CodeImage::from_local_types(&projected, global))
}
