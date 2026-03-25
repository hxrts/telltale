//! Three-party shopping protocol demonstrating multiparty session types.
//!
//! This is a projection-surface example: `tell!` owns the confirm/quit branch,
//! while Rust supplies Alice's requested item and contribution strategy plus
//! Bob's local affordability calculation.

use futures::{executor, try_join};
use std::error::Error;
use telltale::{tell, try_session};

#[derive(Clone, Copy, Debug)]
struct AlicePlan {
    item: i32,
    contribution: i32,
}

#[derive(Clone, Copy, Debug)]
enum PurchaseDecision {
    Confirm(i32),
    Quit,
}

fn decide_purchase(seller_price: i32, alice_share: i32) -> PurchaseDecision {
    if alice_share == seller_price {
        PurchaseDecision::Confirm(alice_share)
    } else {
        PurchaseDecision::Quit
    }
}

tell! {
    -- // Alice asks for a quote, then Bob decides whether the purchase proceeds.
    protocol ThreeBuyers =
      roles Alice, Bob, Seller
      Alice -> Seller : Request(i32)
      Seller -> Alice : Quote(i32)
      Seller -> Bob : Quote(i32)
      Alice -> Bob : Contribution(i32)
      choice Bob at
        -- // Confirm notifies Alice and Seller, then Seller returns a delivery date.
        | Confirm =>
          Bob -> Alice : Confirm(i32)
          Bob -> Seller : Confirm(i32)
          Seller -> Bob : Date(i32)
        -- // Quit notifies both other participants that the purchase is cancelled.
        | Quit =>
          Bob -> Alice : Quit(i32)
          Bob -> Seller : Quit(i32)
}

use ThreeBuyers::sessions::*;

// ---------------------------------------------------------------------------
// Endpoint implementations
// ---------------------------------------------------------------------------

async fn alice(role: &mut Alice, plan: AlicePlan) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: AliceSession<'_, _>| async {
        let s = s.send(Request(plan.item)).await?;
        println!("Alice: requested item {}", plan.item);

        // Receive quote from Seller
        let (Quote(price), s) = s.receive().await?;
        println!("Alice: received quote of {price}");

        // Tell Bob how much Alice will contribute
        let s = s.send(Contribution(plan.contribution)).await?;
        println!("Alice: told Bob contribution of {}", plan.contribution);

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
        match decide_purchase(seller_price, alice_share) {
            PurchaseDecision::Confirm(amount) => {
                println!("Bob: quotes match, confirming purchase");

                let s = s.select(Confirm(amount)).await?;
                let s = s.send(Confirm(amount)).await?;
                let (Date(date), end) = s.receive().await?;
                println!("Bob: delivery in {date} days");

                Ok(((), end))
            }
            PurchaseDecision::Quit => {
                println!("Bob: quotes don't match, quitting");

                let s = s.select(Quit(0)).await?;
                let end = s.send(Quit(0)).await?;

                Ok(((), end))
            }
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

fn main() -> Result<(), Box<dyn Error>> {
    let Roles(mut a, mut b, mut s) = Roles::default();
    let alice_plan = AlicePlan {
        item: 42,
        contribution: 42,
    };
    executor::block_on(async { try_join!(alice(&mut a, alice_plan), bob(&mut b), seller(&mut s)) })?;
    Ok(())
}
