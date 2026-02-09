#![allow(dead_code, unused_imports)]

use std::collections::BTreeMap;

use telltale_lean_bridge::{InvariantClaims, ProtocolBundle};
use telltale_types::{GlobalType, LocalTypeR};

pub mod tier1_minimal;
pub mod tier2_control_flow;
pub mod tier3_distributed;
pub mod tier4_classical;
pub mod tier5_negative;
pub mod tier6_edge_cases;

#[derive(Clone, Debug)]
pub struct ProtocolFixture {
    pub name: &'static str,
    pub global: GlobalType,
    pub local_types: BTreeMap<String, LocalTypeR>,
    pub claims: InvariantClaims,
}

impl ProtocolFixture {
    #[must_use]
    pub fn with_claims(mut self, claims: InvariantClaims) -> Self {
        self.claims = claims;
        self
    }

    #[must_use]
    pub fn to_bundle(&self) -> ProtocolBundle {
        telltale_lean_bridge::export_protocol_bundle(
            &self.global,
            &self.local_types,
            self.claims.clone(),
        )
    }
}

pub use tier1_minimal::{chain, ping_pong, singleton};
pub use tier5_negative::{bad_quorum, deadlock, unbounded_wait};
