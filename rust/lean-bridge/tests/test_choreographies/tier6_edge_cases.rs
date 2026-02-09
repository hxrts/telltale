use std::collections::BTreeMap;

use telltale_lean_bridge::InvariantClaims;
use telltale_types::{GlobalType, Label, LocalTypeR};

use super::ProtocolFixture;

#[must_use]
pub fn recursive_heartbeat() -> ProtocolFixture {
    let global = GlobalType::mu(
        "X",
        GlobalType::send("A", "B", Label::new("hb"), GlobalType::var("X")),
    );

    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::mu(
            "X",
            LocalTypeR::send("B", Label::new("hb"), LocalTypeR::var("X")),
        ),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::mu(
            "X",
            LocalTypeR::recv("A", Label::new("hb"), LocalTypeR::var("X")),
        ),
    );

    ProtocolFixture {
        name: "recursive_heartbeat",
        global,
        local_types,
        claims: InvariantClaims::default(),
    }
}
