use telltale_macros::tell;

tell! {
    module commerce exposing (Checkout)

    protocol Checkout =
      roles Buyer, Seller
      Buyer -> Seller : Offer
      choice Seller at
        | accept =>
          Seller -> Buyer : Accept
        | reject =>
          Seller -> Buyer : Reject
}

fn main() {
    let _roles = commerce::Checkout::sessions::setup();
}
