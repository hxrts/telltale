use std::collections::BTreeMap;

use telltale_lean_bridge::InvariantClaims;
use telltale_types::{GlobalType, Label, LocalTypeR};

use super::ProtocolFixture;

#[must_use]
pub fn ping_pong() -> ProtocolFixture {
    let global = GlobalType::send(
        "A",
        "B",
        Label::new("ping"),
        GlobalType::send("B", "A", Label::new("pong"), GlobalType::End),
    );
    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::send(
            "B",
            Label::new("ping"),
            LocalTypeR::recv("B", Label::new("pong"), LocalTypeR::End),
        ),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::recv(
            "A",
            Label::new("ping"),
            LocalTypeR::send("A", Label::new("pong"), LocalTypeR::End),
        ),
    );

    ProtocolFixture {
        name: "ping_pong",
        global,
        local_types,
        claims: InvariantClaims::default(),
    }
}

#[must_use]
pub fn singleton() -> ProtocolFixture {
    let global = GlobalType::End;
    let mut local_types = BTreeMap::new();
    local_types.insert("Solo".to_string(), LocalTypeR::End);

    ProtocolFixture {
        name: "singleton",
        global,
        local_types,
        claims: InvariantClaims::default(),
    }
}

#[must_use]
pub fn chain() -> ProtocolFixture {
    let global = GlobalType::send(
        "A",
        "B",
        Label::new("ab"),
        GlobalType::send(
            "B",
            "C",
            Label::new("bc"),
            GlobalType::send("C", "A", Label::new("ca"), GlobalType::End),
        ),
    );

    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::send(
            "B",
            Label::new("ab"),
            LocalTypeR::recv("C", Label::new("ca"), LocalTypeR::End),
        ),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::recv(
            "A",
            Label::new("ab"),
            LocalTypeR::send("C", Label::new("bc"), LocalTypeR::End),
        ),
    );
    local_types.insert(
        "C".to_string(),
        LocalTypeR::recv(
            "B",
            Label::new("bc"),
            LocalTypeR::send("A", Label::new("ca"), LocalTypeR::End),
        ),
    );

    ProtocolFixture {
        name: "chain",
        global,
        local_types,
        claims: InvariantClaims::default(),
    }
}
