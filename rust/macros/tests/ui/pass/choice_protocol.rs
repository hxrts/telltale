//! Pass: choice protocol with branching on seller decision.
use telltale_macros::tell;

tell! {
    protocol Purchase =
      roles Buyer, Seller
      choice Seller at
        | Accept =>
          Seller -> Buyer : Confirmation
        | Reject =>
          Seller -> Buyer : Rejection
}

fn main() {
    let _roles = Purchase::sessions::setup();
}
