//! Two-party travel agency negotiation protocol.
//!
//! ```text
//! protocol TravelAgency =
//!   roles Customer, Agency
//!   Customer -> Agency : Order of i32
//!   Agency -> Customer : Quote of i32
//!   choice Customer at Agency
//!     | Accept =>
//!         Customer -> Agency : Address of i32
//!         Agency -> Customer : Date of i32
//!     | Reject =>
//!         Customer -> Agency : Reject of i32
//! ```
//!
//! Uses the manual session type API (`#[session]`, `#[derive(Role)]`,
//! `#[derive(Message)]`) because the protocol includes branching (`choice
//! Customer at Agency`) which the `choreography!` macro does not yet support.
#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]
#![allow(missing_docs)]

use futures::{
    channel::mpsc::{UnboundedReceiver, UnboundedSender},
    executor, try_join,
};
use std::error::Error;
use telltale::{
    channel::Bidirectional, session, try_session, Branch, End, Message, Receive, Role, Roles,
    Select, Send,
};

type Channel = Bidirectional<UnboundedSender<Label>, UnboundedReceiver<Label>>;

// ---------------------------------------------------------------------------
// Roles
// ---------------------------------------------------------------------------

#[derive(Roles)]
struct Roles(Customer, Agency);

#[derive(Role)]
#[message(Label)]
struct Customer(#[route(Agency)] Channel);

#[derive(Role)]
#[message(Label)]
struct Agency(#[route(Customer)] Channel);

// ---------------------------------------------------------------------------
// Messages
// ---------------------------------------------------------------------------

#[derive(Message)]
enum Label {
    Order(Order),
    Quote(Quote),
    Accept(Accept),
    Reject(Reject),
    Address(Address),
    Date(Date),
}

struct Order(i32);
struct Quote(i32);
#[allow(dead_code)]
struct Accept(i32);
#[allow(dead_code)]
struct Reject(i32);
struct Address(i32);
struct Date(i32);

// ---------------------------------------------------------------------------
// Session types — Customer
// ---------------------------------------------------------------------------

#[session]
type ProtoCustomer = Send<Agency, Order, Receive<Agency, Quote, Select<Agency, CustomerChoice>>>;

#[session]
enum CustomerChoice {
    #[allow(dead_code)]
    Accept(Accept, Send<Agency, Address, Receive<Agency, Date, End>>),
    #[allow(dead_code)]
    Reject(Reject, End),
}

// ---------------------------------------------------------------------------
// Session types — Agency
// ---------------------------------------------------------------------------

#[session]
type ProtoAgency = Receive<Customer, Order, Send<Customer, Quote, Branch<Customer, AgencyChoice>>>;

#[session]
enum AgencyChoice {
    Accept(
        Accept,
        Receive<Customer, Address, Send<Customer, Date, End>>,
    ),
    Reject(Reject, End),
}

// ---------------------------------------------------------------------------
// Endpoint implementations
// ---------------------------------------------------------------------------

async fn customer(role: &mut Customer) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: ProtoCustomer<'_, _>| async {
        let distance: i32 = 5;

        // Send order with trip distance
        let s = s.send(Order(distance)).await?;

        // Receive quote from agency
        let (Quote(price), s) = s.receive().await?;

        if price < 100 {
            // Accept and send delivery address
            let s = s.select(Accept(price)).await?;
            let address = 123;
            let s = s.send(Address(address)).await?;

            // Receive delivery date
            let (Date(date), s) = s.receive().await?;
            println!("Order: distance {distance}, quote {price} — accepted. Delivery date: {date}");
            Ok(((), s))
        } else {
            // Reject the quote
            let s = s.select(Reject(price)).await?;
            println!("Order: distance {distance}, quote {price} — rejected.");
            Ok(((), s))
        }
    })
    .await
}

async fn agency(role: &mut Agency) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: ProtoAgency<'_, _>| async {
        // Receive order
        let (Order(distance), s) = s.receive().await?;

        // Quote 10x the distance
        let price = distance * 10;
        let s = s.send(Quote(price)).await?;

        // Branch on customer's choice
        match s.branch().await? {
            AgencyChoice::Accept(_accept, s) => {
                let (Address(_addr), s) = s.receive().await?;
                let date = 42;
                let s = s.send(Date(date)).await?;
                Ok(((), s))
            }
            AgencyChoice::Reject(_reject, s) => Ok(((), s)),
        }
    })
    .await
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() {
    let Roles(mut c, mut a) = Roles::default();
    executor::block_on(async {
        try_join!(customer(&mut c), agency(&mut a)).unwrap();
    });
}
