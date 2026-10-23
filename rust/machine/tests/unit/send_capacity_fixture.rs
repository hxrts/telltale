// Exact existing full-queue fixture helpers shared by the actual backend owners.
fn full_queue_config() -> ProtocolMachineConfig {
    use crate::buffer::{BackpressurePolicy, BufferConfig, BufferMode};
    ProtocolMachineConfig {
        buffer_config: BufferConfig {
            mode: BufferMode::Fifo,
            initial_capacity: 1,
            policy: BackpressurePolicy::Block,
        },
        observability_retention: crate::ObservabilityRetentionConfig {
            mode: crate::ObservabilityRetentionMode::Disabled,
            ..crate::ObservabilityRetentionConfig::default()
        },
        ..ProtocolMachineConfig::default()
    }
}

fn full_queue_image() -> CodeImage {
    use telltale_types::Label;
    let mut image = receive_image();
    image.programs.insert(
        "A".into(),
        vec![
            Instr::Send { chan: 0, val: 1 },
            Instr::Send { chan: 0, val: 1 },
            Instr::Halt,
        ],
    );
    image.programs.insert(
        "B".into(),
        vec![
            Instr::Receive { chan: 0, dst: 1 },
            Instr::Receive { chan: 0, dst: 1 },
            Instr::Halt,
        ],
    );
    image.global_type = GlobalType::send(
        "A",
        "B",
        Label::new("m"),
        GlobalType::send("A", "B", Label::new("m"), GlobalType::End),
    );
    image.local_types.insert(
        "A".into(),
        LocalTypeR::send(
            "B",
            Label::new("m"),
            LocalTypeR::send("B", Label::new("m"), LocalTypeR::End),
        ),
    );
    image.local_types.insert(
        "B".into(),
        LocalTypeR::recv(
            "A",
            Label::new("m"),
            LocalTypeR::recv("A", Label::new("m"), LocalTypeR::End),
        ),
    );
    image
}
