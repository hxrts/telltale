use std::collections::BTreeMap;

use telltale_lean_bridge::{
    DistributedClaims, InvariantClaims, PartialSynchronyConfig, SchedulerKind, TimingModel,
};
use telltale_types::{GlobalType, Label, LocalTypeR};

use super::ProtocolFixture;

#[must_use]
pub fn three_party_ack() -> ProtocolFixture {
    let global = GlobalType::send(
        "Leader",
        "Replica1",
        Label::new("proposal"),
        GlobalType::send(
            "Leader",
            "Replica2",
            Label::new("proposal"),
            GlobalType::send(
                "Replica1",
                "Leader",
                Label::new("ack"),
                GlobalType::send("Replica2", "Leader", Label::new("ack"), GlobalType::End),
            ),
        ),
    );

    let mut local_types = BTreeMap::new();
    local_types.insert(
        "Leader".to_string(),
        LocalTypeR::send(
            "Replica1",
            Label::new("proposal"),
            LocalTypeR::send(
                "Replica2",
                Label::new("proposal"),
                LocalTypeR::recv(
                    "Replica1",
                    Label::new("ack"),
                    LocalTypeR::recv("Replica2", Label::new("ack"), LocalTypeR::End),
                ),
            ),
        ),
    );
    local_types.insert(
        "Replica1".to_string(),
        LocalTypeR::recv(
            "Leader",
            Label::new("proposal"),
            LocalTypeR::send("Leader", Label::new("ack"), LocalTypeR::End),
        ),
    );
    local_types.insert(
        "Replica2".to_string(),
        LocalTypeR::recv(
            "Leader",
            Label::new("proposal"),
            LocalTypeR::send("Leader", Label::new("ack"), LocalTypeR::End),
        ),
    );

    ProtocolFixture {
        name: "three_party_ack",
        global,
        local_types,
        claims: InvariantClaims {
            liveness: Some(telltale_lean_bridge::LivenessConfig {
                scheduler: SchedulerKind::RoundRobin,
                fairness_k: Some(2),
                progress_required: true,
            }),
            distributed: DistributedClaims {
                partial_synchrony: Some(PartialSynchronyConfig {
                    timing: TimingModel::PartialSynchrony,
                    delta_bound: Some(10),
                }),
                ..DistributedClaims::default()
            },
            ..InvariantClaims::default()
        },
    }
}

#[must_use]
pub fn simple_majority() -> ProtocolFixture {
    three_party_ack()
}
