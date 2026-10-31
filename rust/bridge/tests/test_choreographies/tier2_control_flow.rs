//! Tier 2: control flow protocol fixtures (choice, branching).

use std::collections::BTreeMap;

use telltale_bridge::InvariantClaims;
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

/// Bounded recursive loop: `mu X. A->B: tick; A->B: {stop: end, continue: X}`.
///
/// The protocol machine's local-type compiler resolves internal choice to the
/// first branch, so `stop` is listed first: runs unfold the `mu` once and
/// terminate, keeping traces finite while the `continue` back-edge stays in
/// the type (projection, well-formedness, and the Lean validator see it).
#[must_use]
pub fn bounded_loop() -> ProtocolFixture {
    let global = GlobalType::mu(
        "X",
        GlobalType::send(
            "A",
            "B",
            Label::new("tick"),
            GlobalType::comm(
                "A",
                "B",
                vec![
                    (Label::new("stop"), GlobalType::End),
                    (Label::new("continue"), GlobalType::var("X")),
                ],
            ),
        ),
    );

    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::mu(
            "X",
            LocalTypeR::send(
                "B",
                Label::new("tick"),
                LocalTypeR::send_choice(
                    "B",
                    vec![
                        (Label::new("stop"), None, LocalTypeR::End),
                        (Label::new("continue"), None, LocalTypeR::var("X")),
                    ],
                ),
            ),
        ),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::mu(
            "X",
            LocalTypeR::recv(
                "A",
                Label::new("tick"),
                LocalTypeR::recv_choice(
                    "A",
                    vec![
                        (Label::new("stop"), None, LocalTypeR::End),
                        (Label::new("continue"), None, LocalTypeR::var("X")),
                    ],
                ),
            ),
        ),
    );

    ProtocolFixture {
        name: "bounded_loop",
        global,
        local_types,
        claims: InvariantClaims::default(),
    }
}
