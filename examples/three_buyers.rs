//! Three-party shopping protocol demonstrating multiparty session types.
//!
//! Alice wants to buy an item. She asks Seller for a quote, then negotiates
//! with Bob to split the cost. Bob decides whether to confirm or quit.
//!
//! This example uses the manual session type API (`#[session]`, `#[derive(Role)]`,
//! `#[derive(Message)]`) because the protocol requires branching (`choice Bob at
//! Alice, Seller`) which the `choreography!` macro does not yet support.
//!
//! ```tell
//! protocol ThreeBuyers =
//!   roles Alice, Bob, Seller
//!   Alice -> Seller : Request of i32
//!   Seller -> Alice : Quote of i32
//!   Seller -> Bob : Quote of i32
//!   Alice -> Bob : Contribution of i32
//!   choice Bob at Alice, Seller
//!     | Confirm =>
//!         Bob -> Alice : Confirm of i32
//!         Bob -> Seller : Confirm of i32
//!         Seller -> Bob : Date of i32
//!     | Quit =>
//!         Bob -> Alice : Quit of i32
//!         Bob -> Seller : Quit of i32
//! ```
#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]
#![allow(missing_docs)]

use futures::{
    channel::mpsc::{UnboundedReceiver, UnboundedSender},
    executor, try_join,
};
use std::error::Error;
#[allow(unused_imports)]
use telltale::{
    channel::Bidirectional, session, try_session, Branch, End, Message, Receive, Role, Roles,
    Select, Send,
};

type Channel = Bidirectional<UnboundedSender<Label>, UnboundedReceiver<Label>>;

// ---------------------------------------------------------------------------
// Roles
// ---------------------------------------------------------------------------

#[derive(Roles)]
#[allow(dead_code)]
struct Roles {
    alice: Alice,
    bob: Bob,
    seller: Seller,
}

#[derive(Role)]
#[message(Label)]
struct Alice {
    #[route(Bob)]
    bob: Channel,
    #[route(Seller)]
    seller: Channel,
}

#[derive(Role)]
#[message(Label)]
struct Bob {
    #[route(Alice)]
    alice: Channel,
    #[route(Seller)]
    seller: Channel,
}

#[derive(Role)]
#[message(Label)]
struct Seller {
    #[route(Alice)]
    alice: Channel,
    #[route(Bob)]
    bob: Channel,
}

// ---------------------------------------------------------------------------
// Messages
// ---------------------------------------------------------------------------

#[derive(Message)]
enum Label {
    Request(Request),
    Quote(Quote),
    Contribution(Contribution),
    Confirm(Confirm),
    Quit(Quit),
    Date(Date),
}

struct Request(i32);
struct Quote(i32);
struct Contribution(i32);
struct Confirm(i32);
#[allow(dead_code)]
struct Quit(i32);
struct Date(i32);

// ---------------------------------------------------------------------------
// Session types — Alice
// ---------------------------------------------------------------------------
//
// Alice -> Seller : Request
// Receive Quote from Seller
// Alice -> Bob : Contribution
// Branch from Bob: Confirm(i32, End) | Quit(i32, End)

#[session]
type ProtoAlice = Send<
    Seller,
    Request,
    Receive<Seller, Quote, Send<Bob, Contribution, Branch<Bob, ProtoAliceBranch>>>,
>;

#[session]
enum ProtoAliceBranch {
    Confirm(Confirm, End),
    Quit(Quit, End),
}

// ---------------------------------------------------------------------------
// Session types — Bob
// ---------------------------------------------------------------------------
//
// Receive Quote from Seller
// Receive Contribution from Alice
// Select at Alice, Seller:
//   Confirm => Send Confirm to Alice, Send Confirm to Seller, Receive Date from Seller
//   Quit    => Send Quit to Alice, Send Quit to Seller

#[session]
type ProtoBob = Receive<Seller, Quote, Receive<Alice, Contribution, Select<Alice, ProtoBobChoice>>>;

#[session]
enum ProtoBobChoice {
    #[allow(dead_code)]
    Confirm(Confirm, Select<Seller, ProtoBobConfirmSeller>),
    #[allow(dead_code)]
    Quit(Quit, Select<Seller, ProtoBobQuitSeller>),
}

#[session]
enum ProtoBobConfirmSeller {
    #[allow(dead_code)]
    Confirm(Confirm, Receive<Seller, Date, End>),
}

#[session]
enum ProtoBobQuitSeller {
    Quit(Quit, End),
}

// ---------------------------------------------------------------------------
// Session types — Seller
// ---------------------------------------------------------------------------
//
// Receive Request from Alice
// Seller -> Alice : Quote
// Seller -> Bob : Quote
// Branch from Bob: Confirm => Receive Confirm, Send Date to Bob
//                  Quit    => Receive Quit

#[session]
type ProtoSeller =
    Receive<Alice, Request, Send<Alice, Quote, Send<Bob, Quote, Branch<Bob, ProtoSellerBranch>>>>;

#[session]
enum ProtoSellerBranch {
    Confirm(Confirm, Send<Bob, Date, End>),
    Quit(Quit, End),
}

// ---------------------------------------------------------------------------
// Endpoint implementations
// ---------------------------------------------------------------------------

async fn alice(role: &mut Alice) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: ProtoAlice<'_, _>| async {
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
            ProtoAliceBranch::Confirm(Confirm(amount), end) => {
                println!("Alice: Bob confirmed, paying {amount}");
                Ok(((), end))
            }
            ProtoAliceBranch::Quit(Quit(_), end) => {
                println!("Alice: Bob quit the purchase");
                Ok(((), end))
            }
        }
    })
    .await
}

async fn bob(role: &mut Bob) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: ProtoBob<'_, _>| async {
        // Receive quote from Seller
        let (Quote(seller_price), s) = s.receive().await?;
        println!("Bob: received quote of {seller_price} from Seller");

        // Receive Alice's contribution
        let (Contribution(alice_share), s) = s.receive().await?;
        println!("Bob: Alice will contribute {alice_share}");

        // Decide based on whether quotes match
        if alice_share == seller_price {
            println!("Bob: quotes match, confirming purchase");

            // Notify Alice
            let s = s.select(Confirm(alice_share)).await?;

            // Notify Seller
            let s = s.select(Confirm(alice_share)).await?;

            // Receive delivery date from Seller
            let (Date(date), end) = s.receive().await?;
            println!("Bob: delivery in {date} days");

            Ok(((), end))
        } else {
            println!("Bob: quotes don't match, quitting");

            // Notify Alice
            let s = s.select(Quit(0)).await?;

            // Notify Seller
            let end = s.select(Quit(0)).await?;

            Ok(((), end))
        }
    })
    .await
}

async fn seller(role: &mut Seller) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: ProtoSeller<'_, _>| async {
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
            ProtoSellerBranch::Confirm(Confirm(_), s) => {
                println!("Seller: order confirmed, shipping in 7 days");
                let end = s.send(Date(7)).await?;
                Ok(((), end))
            }
            ProtoSellerBranch::Quit(Quit(_), end) => {
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
    let mut roles = Roles::default();
    executor::block_on(async {
        try_join!(
            alice(&mut roles.alice),
            bob(&mut roles.bob),
            seller(&mut roles.seller)
        )
        .unwrap();
    });
}
