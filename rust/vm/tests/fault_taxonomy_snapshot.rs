#![cfg(not(target_arch = "wasm32"))]
#![allow(missing_docs)]

use telltale_types::ValType;
use telltale_vm::coroutine::Fault;
use telltale_vm::fault_code_of;
use telltale_vm::instr::Endpoint;
use telltale_vm::session::Edge;

#[test]
fn fault_taxonomy_mapping_snapshot_is_stable() {
    let samples = vec![
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
        Fault::TransferFault {
            message: "ownership".to_string(),
        },
        Fault::OutOfCredits,
    ];

    let snapshot: Vec<&str> = samples.iter().map(fault_code_of).collect();
    let encoded = serde_json::to_string(&snapshot).expect("serialize snapshot");
    assert_eq!(
        encoded,
        "[\"vm.fault.type\",\"vm.fault.label\",\"vm.fault.channel\",\"vm.fault.verification\",\"vm.fault.transfer\",\"vm.fault.credits\"]"
    );
}
