//! Three-party shopping protocol demonstrating multiparty session types.
//!
//! This is an effect-boundary example: `tell!` owns the confirm/quit branch,
//! while generated effect traits model Alice's plan, Seller's price quote, and
//! Bob's affordability decision.

use futures::{executor, try_join};
use std::error::Error;
use telltale::{tell, try_session};

tell! {
    -- // Execution profile keeps the example on the proof-backed effect boundary.
    profile Replay fairness eventual admissibility replay escalation_window bounded

    -- // Alice-side shopping request provided by the host.
    type alias BuyerPlan =
    {
      item : Int
      contribution : Int
    }

    -- // Bob decides whether the purchase proceeds.
    type PurchaseDecision =
      | Confirm(Int)
      | Quit

    -- // Seller quote and Alice contribution presented to Bob together.
    type alias Offer =
    {
      sellerPrice : Int
      aliceShare : Int
    }

    -- // Alice host provides the requested item and intended contribution.
    effect AlicePlanner
      command request : Session -> BuyerPlan
      {
        class : best_effort
        progress : immediate
        region : session
        agreement_use : none
        reentrancy : allow
      }

    -- // Seller host quotes one price for the requested item.
    effect SellerPricing
      command quote : Int -> Int
      {
        class : best_effort
        progress : immediate
        region : session
        agreement_use : none
        reentrancy : allow
      }

    -- // Bob host evaluates the offer and decides whether to buy.
    effect BobBudget
      command decide : Offer -> PurchaseDecision
      {
        class : best_effort
        progress : immediate
        region : session
        agreement_use : none
        reentrancy : allow
      }

    -- // Alice asks for a quote, then Bob decides whether the purchase proceeds.
    protocol ThreeBuyers uses AlicePlanner, SellerPricing, BobBudget under Replay =
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

use ThreeBuyers::effects;
use ThreeBuyers::sessions::*;

struct AliceHost {
    plan: effects::BuyerPlan,
}

struct BobHost;

struct SellerHost;

impl effects::AlicePlanner for AliceHost {
    fn request(&mut self, _input: effects::Session) -> effects::BuyerPlan {
        self.plan.clone()
    }
}

impl effects::SellerPricing for SellerHost {
    fn quote(&mut self, input: i64) -> i64 {
        input
    }
}

impl effects::BobBudget for BobHost {
    fn decide(&mut self, input: effects::Offer) -> effects::PurchaseDecision {
        if input.alice_share == input.seller_price {
            effects::PurchaseDecision::Confirm(input.alice_share)
        } else {
            effects::PurchaseDecision::Quit
        }
    }
}

async fn alice(role: &mut Alice, host: &mut AliceHost) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: AliceSession<'_, _>| async {
        let plan = effects::AlicePlanner::request(host, effects::Session::new("three-buyers"));
        let item = i32::try_from(plan.item)?;
        let contribution = i32::try_from(plan.contribution)?;

        let s = s.send(Request(item)).await?;
        println!("Alice: requested item {item}");

        let (Quote(price), s) = s.receive().await?;
        println!("Alice: received quote of {price}");

        let s = s.send(Contribution(contribution)).await?;
        println!("Alice: told Bob contribution of {contribution}");

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

async fn bob(role: &mut Bob, host: &mut BobHost) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: BobSession<'_, _>| async {
        let (Quote(seller_price), s) = s.receive().await?;
        println!("Bob: received quote of {seller_price} from Seller");

        let (Contribution(alice_share), s) = s.receive().await?;
        println!("Bob: Alice will contribute {alice_share}");

        match effects::BobBudget::decide(
            host,
            effects::Offer {
                seller_price: seller_price.into(),
                alice_share: alice_share.into(),
            },
        ) {
            effects::PurchaseDecision::Confirm(amount) => {
                println!("Bob: quotes match, confirming purchase");
                let amount = i32::try_from(amount)?;

                let s = s.select(Confirm(amount)).await?;
                let s = s.send(Confirm(amount)).await?;
                let (Date(date), end) = s.receive().await?;
                println!("Bob: delivery in {date} days");

                Ok(((), end))
            }
            effects::PurchaseDecision::Quit => {
                println!("Bob: quotes don't match, quitting");

                let s = s.select(Quit(0)).await?;
                let end = s.send(Quit(0)).await?;

                Ok(((), end))
            }
        }
    })
    .await
}

async fn seller(role: &mut Seller, host: &mut SellerHost) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: SellerSession<'_, _>| async {
        let (Request(item), s) = s.receive().await?;
        println!("Seller: received request for item {item}");

        let price = i32::try_from(effects::SellerPricing::quote(host, item.into()))?;
        let s = s.send(Quote(price)).await?;
        println!("Seller: quoted {price} to Alice");

        let s = s.send(Quote(price)).await?;
        println!("Seller: quoted {price} to Bob");

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

fn main() -> Result<(), Box<dyn Error>> {
    let Roles(mut a, mut b, mut s) = Roles::default();
    let mut alice_host = AliceHost {
        plan: effects::BuyerPlan {
            item: 42,
            contribution: 42,
        },
    };
    let mut bob_host = BobHost;
    let mut seller_host = SellerHost;
    println!(
        "execution profiles = {:?}",
        ThreeBuyers::proof_status::EXECUTION_PROFILES
    );
    println!(
        "session projectable = {}",
        ThreeBuyers::proof_status::SESSION_PROJECTABLE
    );
    executor::block_on(async {
        try_join!(
            alice(&mut a, &mut alice_host),
            bob(&mut b, &mut bob_host),
            seller(&mut s, &mut seller_host)
        )
    })?;
    Ok(())
}
