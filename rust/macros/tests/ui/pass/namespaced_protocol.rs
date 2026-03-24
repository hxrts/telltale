use telltale_macros::choreography;

choreography!(r#"
module commerce exposing (Checkout)

protocol Checkout =
  roles Buyer, Seller
  Buyer -> Seller : Offer
  choice Seller at
    | accept =>
      Seller -> Buyer : Accept
    | reject =>
      Seller -> Buyer : Reject
"#);

fn main() {
    let _roles = commerce::setup();
}
