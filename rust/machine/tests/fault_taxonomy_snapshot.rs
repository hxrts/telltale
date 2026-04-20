#![allow(missing_docs)]
#![cfg(not(target_arch = "wasm32"))]
//! Snapshot tests for fault taxonomy code stability.

use telltale_machine::coroutine::Fault;
use telltale_machine::fault_code_of;
use telltale_machine::instr::Endpoint;
use telltale_machine::model::state::Edge;
use telltale_types::ValType;

#[test]
fn fault_taxonomy_mapping_snapshot_is_stable() {
    let samples = [
        Fault::TypeViolation {
            expected: ValType::Unit,
            actual: ValType::Nat,
            message: "m".to_string(),
        },
        Fault::UnknownLabel {
            label: "branch_x".to_string(),
        },
        Fault::ChannelClosed {
            endpoint: Endpoint {
                sid: 1,
                role: "A".to_string(),
            },
        },
        Fault::VerificationFailed {
            edge: Edge::new(2, "A", "B"),
            message: "bad sig".to_string(),
        },
        Fault::Transfer {
            message: "ownership".to_string(),
        },
        Fault::OutOfCredits,
    ];

    let snapshot: Vec<&str> = samples.iter().map(fault_code_of).collect();
    let encoded = serde_json::to_string(&snapshot).expect("serialize snapshot");
    assert_eq!(
        encoded,
        "[\"machine.fault.type\",\"machine.fault.label\",\"machine.fault.channel\",\"machine.fault.verification\",\"machine.fault.transfer\",\"machine.fault.credits\"]"
    );
}
