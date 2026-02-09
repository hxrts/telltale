use std::collections::BTreeMap;

use telltale_lean_bridge::{ClassicalClaims, InvariantClaims, LittlesLawConfig, MixingConfig};
use telltale_types::{GlobalType, Label, LocalTypeR};

use super::ProtocolFixture;

#[must_use]
pub fn queue_observer() -> ProtocolFixture {
    let global = GlobalType::send(
        "Ingress",
        "Queue",
        Label::new("enqueue"),
        GlobalType::send("Queue", "Ingress", Label::new("accepted"), GlobalType::End),
    );

    let mut local_types = BTreeMap::new();
    local_types.insert(
        "Ingress".to_string(),
        LocalTypeR::send(
            "Queue",
            Label::new("enqueue"),
            LocalTypeR::recv("Queue", Label::new("accepted"), LocalTypeR::End),
        ),
    );
    local_types.insert(
        "Queue".to_string(),
        LocalTypeR::recv(
            "Ingress",
            Label::new("enqueue"),
            LocalTypeR::send("Ingress", Label::new("accepted"), LocalTypeR::End),
        ),
    );

    ProtocolFixture {
        name: "queue_observer",
        global,
        local_types,
        claims: InvariantClaims {
            classical: ClassicalClaims {
                mixing: Some(MixingConfig {
                    enabled: true,
                    mixing_time_bound: Some(20),
                }),
                littles_law: Some(LittlesLawConfig { enabled: true }),
                ..ClassicalClaims::default()
            },
            ..InvariantClaims::default()
        },
    }
}
