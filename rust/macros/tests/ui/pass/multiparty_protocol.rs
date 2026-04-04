//! Pass: three-party multiparty protocol.
use telltale_macros::tell;

tell! {
    protocol Demo =
      roles A, B, C
      A -> B : Ping
      B -> C : Relay(u64)
      C -> A : Ack
}

fn main() {
    let _roles = Demo::sessions::setup();
}
