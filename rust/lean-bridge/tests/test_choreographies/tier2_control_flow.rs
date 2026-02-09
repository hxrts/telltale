use std::collections::BTreeMap;

use telltale_lean_bridge::InvariantClaims;
use telltale_types::{GlobalType, Label, LocalTypeR};

use super::ProtocolFixture;

#[must_use]
pub fn binary_choice() -> ProtocolFixture {
    let global = GlobalType::comm(
        "A",
        "B",
        vec![
            (Label::new("yes"), GlobalType::End),
            (Label::new("no"), GlobalType::End),
        ],
    );

    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::send_choice(
            "B",
            vec![
                (Label::new("yes"), None, LocalTypeR::End),
                (Label::new("no"), None, LocalTypeR::End),
            ],
        ),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::recv_choice(
            "A",
            vec![
                (Label::new("yes"), None, LocalTypeR::End),
                (Label::new("no"), None, LocalTypeR::End),
            ],
        ),
    );

    ProtocolFixture {
        name: "binary_choice",
        global,
        local_types,
        claims: InvariantClaims::default(),
    }
}
