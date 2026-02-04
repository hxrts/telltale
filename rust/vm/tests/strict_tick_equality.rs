//! Strict tick equality regression tests.

#[allow(dead_code, unreachable_pub)]
mod helpers;

use telltale_vm::vm::{VMConfig, VM};

use helpers::PassthroughHandler;

#[test]
fn test_strict_tick_equality_same_engine() {
    let image = helpers::simple_send_recv_image("A", "B", "msg");
    let handler = PassthroughHandler;

    let mut vm1 = VM::new(VMConfig::default());
    vm1.load_choreography(&image).expect("load vm1");
    vm1.run(&handler, 50).expect("run vm1");

    let mut vm2 = VM::new(VMConfig::default());
    vm2.load_choreography(&image).expect("load vm2");
    vm2.run(&handler, 50).expect("run vm2");

    assert_eq!(vm1.trace(), vm2.trace(), "strict traces should match");
}
