//! Two-party travel agency negotiation protocol.
//! Uses the `tell!` macro to derive session types, roles, messages,
//! and channel wiring from the global protocol specification.

use futures::{executor, try_join};
use std::error::Error;
use telltale::{tell, try_session};

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

async fn customer(role: &mut Customer) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: CustomerSession<'_, _>| async {
        let distance: i32 = 5;

        // Send order with trip distance
        let s = s.send(Order(distance)).await?;

        // Receive quote from agency
        let (Quote(price), s) = s.receive().await?;

        if price < 100 {
            // Accept and send delivery address
            let s = s.select(Accept).await?;
            let address = 123;
            let s = s.send(Address(address)).await?;

            // Receive delivery date
            let (Date(date), s) = s.receive().await?;
            println!("Order: distance {distance}, quote {price} — accepted. Delivery date: {date}");
            Ok(((), s))
        } else {
            // Reject the quote
            let s = s.select(Reject).await?;
            let s = s.send(Rejection(price)).await?;
            println!("Order: distance {distance}, quote {price} — rejected.");
            Ok(((), s))
        }
    })
    .await
}

async fn agency(role: &mut Agency) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: AgencySession<'_, _>| async {
        // Receive order
        let (Order(distance), s) = s.receive().await?;

        // Quote 10x the distance
        let price = distance * 10;
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
    executor::block_on(async { try_join!(customer(&mut c), agency(&mut a)) })?;
    Ok(())
}
