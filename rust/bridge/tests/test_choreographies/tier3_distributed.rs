//! Tier 3: distributed multi-party protocol fixtures.

use std::collections::BTreeMap;

use telltale_bridge::{
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
            liveness: Some(telltale_bridge::LivenessConfig {
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

/// Asynchronous independent communications: `A->B: m1; C->D: m2`.
///
/// The second communication shares no participant with the first, so the
/// global `comm_async` step may fire it before `m1` is delivered.
#[must_use]
pub fn independent_pairs() -> ProtocolFixture {
    let global = GlobalType::send(
        "A",
        "B",
        Label::new("m1"),
        GlobalType::send("C", "D", Label::new("m2"), GlobalType::End),
    );

    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::send("B", Label::new("m1"), LocalTypeR::End),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::recv("A", Label::new("m1"), LocalTypeR::End),
    );
    local_types.insert(
        "C".to_string(),
        LocalTypeR::send("D", Label::new("m2"), LocalTypeR::End),
    );
    local_types.insert(
        "D".to_string(),
        LocalTypeR::recv("C", Label::new("m2"), LocalTypeR::End),
    );

    ProtocolFixture {
        name: "independent_pairs",
        global,
        local_types,
        claims: InvariantClaims::default(),
    }
}

/// Asynchronous fan-out from one sender: `A->B: x; A->C: y`.
#[must_use]
pub fn fan_out() -> ProtocolFixture {
    let global = GlobalType::send(
        "A",
        "B",
        Label::new("x"),
        GlobalType::send("A", "C", Label::new("y"), GlobalType::End),
    );

    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::send(
            "B",
            Label::new("x"),
            LocalTypeR::send("C", Label::new("y"), LocalTypeR::End),
        ),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::recv("A", Label::new("x"), LocalTypeR::End),
    );
    local_types.insert(
        "C".to_string(),
        LocalTypeR::recv("A", Label::new("y"), LocalTypeR::End),
    );

    ProtocolFixture {
        name: "fan_out",
        global,
        local_types,
        claims: InvariantClaims::default(),
    }
}
