//! Pass: broadcast protocol with leader-to-all send.
use telltale_macros::tell;

tell! {
    protocol Broadcast =
      roles Leader, Worker1, Worker2
      Leader ->* : Start
}

fn main() {
    let _roles = Broadcast::sessions::setup();
}
