//! Two-party travel agency negotiation protocol.
//!
//! This is an effect-boundary example: `tell!` owns the accept/reject branch,
//! while generated effect traits model customer preferences and agency quoting
//! and scheduling.

use futures::{executor, try_join};
use std::error::Error;
use telltale::{tell, try_session};

tell! {
    -- // Customer-side travel request and budget.
    type alias TravelRequest = { distance : Int, maxBudget : Int, address : Int }

    -- // Customer's decision after receiving a quote.
    type QuoteDecision =
      | Accept
      | Reject

    -- // Customer host provides the request and accepts or rejects one quote.
    effect CustomerPreferences
      command request : Session -> TravelRequest
      command decide : Int -> QuoteDecision

    -- // Agency host computes a quote and schedules fulfillment.
    effect AgencyRuntime
      command quote : Int -> Int
      command schedule : Int -> Int

    -- // Customer places one order, receives a quote, then accepts or rejects it.
    protocol TravelAgency uses CustomerPreferences, AgencyRuntime =
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

use TravelAgency::effects;
use TravelAgency::sessions::*;

struct CustomerHost {
    request: effects::TravelRequest,
}

struct AgencyHost;

impl effects::CustomerPreferences for CustomerHost {
    fn request(&mut self, _input: effects::Session) -> effects::TravelRequest {
        self.request.clone()
    }

    fn decide(&mut self, input: i64) -> effects::QuoteDecision {
        if input < self.request.max_budget {
            effects::QuoteDecision::Accept
        } else {
            effects::QuoteDecision::Reject
        }
    }
}

impl effects::AgencyRuntime for AgencyHost {
    fn quote(&mut self, input: i64) -> i64 {
        input * 10
    }

    fn schedule(&mut self, _input: i64) -> i64 {
        42
    }
}

async fn customer(role: &mut Customer, host: &mut CustomerHost) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: CustomerSession<'_, _>| async {
        let request = effects::CustomerPreferences::request(host, effects::Session::new("travel"));
        let distance = i32::try_from(request.distance)?;
        let address = i32::try_from(request.address)?;
        let s = s.send(Order(distance)).await?;

        let (Quote(price), s) = s.receive().await?;

        match effects::CustomerPreferences::decide(host, price.into()) {
            effects::QuoteDecision::Accept => {
                let s = s.select(Accept).await?;
                let s = s.send(Address(address)).await?;

                let (Date(date), s) = s.receive().await?;
                println!("Order: distance {distance}, quote {price} — accepted. Delivery date: {date}");
                Ok(((), s))
            }
            effects::QuoteDecision::Reject => {
                let s = s.select(Reject).await?;
                let s = s.send(Rejection(price)).await?;
                println!("Order: distance {distance}, quote {price} — rejected.");
                Ok(((), s))
            }
        }
    })
    .await
}

async fn agency(role: &mut Agency, host: &mut AgencyHost) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: AgencySession<'_, _>| async {
        let (Order(distance), s) = s.receive().await?;

        let price = i32::try_from(effects::AgencyRuntime::quote(host, distance.into()))?;
        let s = s.send(Quote(price)).await?;

        match s.branch().await? {
            AgencyChoice1::Accept(_accept, s) => {
                let (Address(_addr), s) = s.receive().await?;
                let date = i32::try_from(effects::AgencyRuntime::schedule(host, distance.into()))?;
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

fn main() -> Result<(), Box<dyn Error>> {
    let Roles(mut c, mut a) = Roles::default();
    let mut customer_host = CustomerHost {
        request: effects::TravelRequest {
            distance: 5,
            max_budget: 100,
            address: 123,
        },
    };
    let mut agency_host = AgencyHost;
    executor::block_on(async {
        try_join!(customer(&mut c, &mut customer_host), agency(&mut a, &mut agency_host))
    })?;
    Ok(())
}
