//! Two-party travel agency negotiation protocol.
//!
//! This is a projection-surface example: `tell!` owns the accept/reject
//! negotiation branch, while Rust provides the customer's budget and the
//! agency's local quote calculation.

use futures::{executor, try_join};
use std::error::Error;
use telltale::{tell, try_session};

#[derive(Clone, Copy, Debug)]
struct TravelRequest {
    distance: i32,
    max_budget: i32,
    address: i32,
}

#[derive(Clone, Copy, Debug)]
enum QuoteDecision {
    Accept,
    Reject,
}

fn decide_quote(price: i32, max_budget: i32) -> QuoteDecision {
    if price < max_budget {
        QuoteDecision::Accept
    } else {
        QuoteDecision::Reject
    }
}

fn quote_for_distance(distance: i32) -> i32 {
    distance * 10
}

tell! {
    -- // Customer places one order, receives a quote, then accepts or rejects it.
    protocol TravelAgency =
      roles Customer, Agency
      Customer -> Agency : Order(i32)
      Agency -> Customer : Quote(i32)
      choice Customer at
        -- // Accept sends the address and receives the travel date.
        | Accept =>
          Customer -> Agency : Address(i32)
          Agency -> Customer : Date(i32)
        -- // Reject ends the negotiation after sending the refusal.
        | Reject =>
          Customer -> Agency : Rejection(i32)
}

use TravelAgency::sessions::*;

// ---------------------------------------------------------------------------
// Endpoint implementations
// ---------------------------------------------------------------------------

async fn customer(role: &mut Customer, request: TravelRequest) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: CustomerSession<'_, _>| async {
        let s = s.send(Order(request.distance)).await?;

        // Receive quote from agency
        let (Quote(price), s) = s.receive().await?;

        match decide_quote(price, request.max_budget) {
            QuoteDecision::Accept => {
                let s = s.select(Accept).await?;
                let s = s.send(Address(request.address)).await?;

                let (Date(date), s) = s.receive().await?;
                println!(
                    "Order: distance {}, quote {price} — accepted. Delivery date: {date}",
                    request.distance
                );
                Ok(((), s))
            }
            QuoteDecision::Reject => {
                let s = s.select(Reject).await?;
                let s = s.send(Rejection(price)).await?;
                println!("Order: distance {}, quote {price} — rejected.", request.distance);
                Ok(((), s))
            }
        }
    })
    .await
}

async fn agency(role: &mut Agency) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: AgencySession<'_, _>| async {
        // Receive order
        let (Order(distance), s) = s.receive().await?;

        let price = quote_for_distance(distance);
        let s = s.send(Quote(price)).await?;

        // Branch on customer's choice
        match s.branch().await? {
            AgencyChoice1::Accept(_accept, s) => {
                let (Address(_addr), s) = s.receive().await?;
                let date = 42;
                let s = s.send(Date(date)).await?;
                Ok(((), s))
            }
            AgencyChoice1::Reject(_reject, s) => {
                let (Rejection(_price), s) = s.receive().await?;
                Ok(((), s))
            }
        }
    })
    .await
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() -> Result<(), Box<dyn Error>> {
    let Roles(mut c, mut a) = Roles::default();
    let request = TravelRequest {
        distance: 5,
        max_budget: 100,
        address: 123,
    };
    executor::block_on(async { try_join!(customer(&mut c, request), agency(&mut a)) })?;
    Ok(())
}
