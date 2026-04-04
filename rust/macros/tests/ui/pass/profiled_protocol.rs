//! Pass: protocol with an execution profile declaration.
use telltale_macros::tell;

tell! {
    profile Replay fairness eventual admissibility replay escalation_window bounded

    protocol ReplayAware under Replay =
      roles A, B
      A -> B : Ping
}

fn main() {
    assert_eq!(ReplayAware::proof_status::EXECUTION_PROFILES, ["Replay"]);
    let _roles = ReplayAware::sessions::setup();
}
