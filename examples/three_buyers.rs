//! Three-party shopping protocol demonstrating multiparty session types.
//!
//! Alice wants to buy an item. She asks Seller for a quote, then negotiates
//! with Bob to split the cost. Bob decides whether to confirm or quit.
//!
//! ```text
//! protocol ThreeBuyers =
//!   roles Alice, Bob, Seller
//!   Alice -> Seller : Request(i32)
//!   Seller -> Alice : Quote(i32)
//!   Seller -> Bob : Quote(i32)
//!   Alice -> Bob : Contribution(i32)
//!   choice Bob at
//!     | Confirm =>
//!         Bob -> Alice : Confirm(i32)
//!         Bob -> Seller : Confirm(i32)
//!         Seller -> Bob : Date(i32)
//!     | Quit =>
//!         Bob -> Alice : Quit(i32)
//!         Bob -> Seller : Quit(i32)
//! ```
//!
//! Uses the `choreography!` macro to generate session types, roles, and
//! messages from the global protocol specification.
#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]
#![allow(missing_docs)]

use futures::{executor, try_join};
use std::error::Error;
use telltale::try_session;
use telltale_macros::choreography;

choreography! {
    protocol ThreeBuyers = {
        roles Alice, Bob, Seller;
        Alice -> Seller : Request(i32);
        Seller -> Alice : Quote(i32);
        Seller -> Bob : Quote(i32);
        Alice -> Bob : Contribution(i32);
        choice Bob at {
            | Confirm => {
                Bob -> Alice : Confirm(i32);
                Bob -> Seller : Confirm(i32);
                Seller -> Bob : Date(i32);
            }
            | Quit => {
                Bob -> Alice : Quit(i32);
                Bob -> Seller : Quit(i32);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Endpoint implementations
// ---------------------------------------------------------------------------

async fn alice(role: &mut Alice) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: AliceSession<'_, _>| async {
        // Request item 42
        let s = s.send(Request(42)).await?;
        println!("Alice: requested item 42");

        // Receive quote from Seller
        let (Quote(price), s) = s.receive().await?;
        println!("Alice: received quote of {price}");

        // Tell Bob how much Alice will contribute
        let s = s.send(Contribution(price)).await?;
        println!("Alice: told Bob contribution of {price}");

        // Wait for Bob's decision
        match s.branch().await? {
            AliceChoice1::Confirm(Confirm(amount), end) => {
                println!("Alice: Bob confirmed, paying {amount}");
                Ok(((), end))
            }
            AliceChoice1::Quit(Quit(_), end) => {
                println!("Alice: Bob quit the purchase");
                Ok(((), end))
            }
        }
    })
    .await
}

async fn bob(role: &mut Bob) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: BobSession<'_, _>| async {
        // Receive quote from Seller
        let (Quote(seller_price), s) = s.receive().await?;
        println!("Bob: received quote of {seller_price} from Seller");

        // Receive Alice's contribution
        let (Contribution(alice_share), s) = s.receive().await?;
        println!("Bob: Alice will contribute {alice_share}");

        // Decide based on whether quotes match
        if alice_share == seller_price {
            println!("Bob: quotes match, confirming purchase");

            // Notify Alice and Seller, then receive delivery date
            let s = s.select(Confirm(alice_share)).await?;
            let s = s.send(Confirm(alice_share)).await?;
            let (Date(date), end) = s.receive().await?;
            println!("Bob: delivery in {date} days");

            Ok(((), end))
        } else {
            println!("Bob: quotes don't match, quitting");

            // Notify Alice and Seller
            let s = s.select(Quit(0)).await?;
            let end = s.send(Quit(0)).await?;

            Ok(((), end))
        }
    })
    .await
}

async fn seller(role: &mut Seller) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: SellerSession<'_, _>| async {
        // Receive request from Alice
        let (Request(item), s) = s.receive().await?;
        println!("Seller: received request for item {item}");

        // Quote same price to both Alice and Bob
        let price = item; // price equals item id for this example
        let s = s.send(Quote(price)).await?;
        println!("Seller: quoted {price} to Alice");

        let s = s.send(Quote(price)).await?;
        println!("Seller: quoted {price} to Bob");

        // Wait for Bob's decision
        match s.branch().await? {
            SellerChoice1::Confirm(Confirm(_), s) => {
                println!("Seller: order confirmed, shipping in 7 days");
                let end = s.send(Date(7)).await?;
                Ok(((), end))
            }
            SellerChoice1::Quit(Quit(_), end) => {
                println!("Seller: order cancelled");
                Ok(((), end))
            }
        }
    })
    .await
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() {
    let Roles(mut a, mut b, mut s) = Roles::default();
    executor::block_on(async {
        try_join!(alice(&mut a), bob(&mut b), seller(&mut s)).unwrap();
    });
}
