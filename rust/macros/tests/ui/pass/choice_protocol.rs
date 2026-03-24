use telltale_macros::choreography;

choreography! {
    protocol Purchase =
      roles Buyer, Seller
      choice Seller at
        | Accept =>
          Seller -> Buyer : Confirmation
        | Reject =>
          Seller -> Buyer : Rejection
}

fn main() {
    let _roles = setup();
}
