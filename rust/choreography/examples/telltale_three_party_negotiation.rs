#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

// Three-party negotiation protocol example using TelltaleHandler
//
// This example demonstrates a negotiation protocol between a buyer, seller, and broker.
// The broker facilitates the negotiation by coordinating offers and acceptances.

/// Maximum price the buyer will accept in this demo scenario.
const BUYER_ACCEPT_PRICE_MAX: u32 = 1200;

use serde::{Deserialize, Serialize};
use telltale_choreography::effects::{
    handlers::telltale::{SimpleChannel, TelltaleEndpoint, TelltaleHandler},
    ChoreoHandler, LabelId, RoleId,
};
use telltale_choreography::RoleName;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Role {
    Buyer,
    Seller,
    Broker,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum NegotiationLabel {
    Accept,
    Reject,
}

impl LabelId for NegotiationLabel {
    fn as_str(&self) -> &'static str {
        match self {
            NegotiationLabel::Accept => "accept",
            NegotiationLabel::Reject => "reject",
        }
    }

    fn from_str(label: &str) -> Option<Self> {
        match label {
            "accept" => Some(NegotiationLabel::Accept),
            "reject" => Some(NegotiationLabel::Reject),
            _ => None,
        }
    }
}

impl RoleId for Role {
    type Label = NegotiationLabel;

    fn role_name(&self) -> RoleName {
        match self {
            Role::Buyer => RoleName::from_static("Buyer"),
            Role::Seller => RoleName::from_static("Seller"),
            Role::Broker => RoleName::from_static("Broker"),
        }
    }
}

impl telltale::Role for Role {
    type Message = Message;

    fn seal(&mut self) {}
    fn is_sealed(&self) -> bool {
        false
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum Message {
    Offer { item: String, price: u32 },
    Counter { item: String, price: u32 },
    Accept,
    Reject,
}

impl telltale::Message<Box<dyn std::any::Any + Send>> for Message {
    fn upcast(msg: Box<dyn std::any::Any + Send>) -> Self {
        *msg.downcast::<Message>().unwrap()
    }

    fn downcast(self) -> Result<Box<dyn std::any::Any + Send>, Self> {
        Ok(Box::new(self))
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Initialize tracing
    tracing_subscriber::fmt::init();

    println!("=== Three-Party Negotiation Protocol ===\n");

    // Create endpoints
    let mut buyer_ep = TelltaleEndpoint::new(Role::Buyer);
    let mut seller_ep = TelltaleEndpoint::new(Role::Seller);
    let mut broker_ep = TelltaleEndpoint::new(Role::Broker);

    // Create channels between all parties
    let (buyer_to_broker_ch, broker_from_buyer_ch) = SimpleChannel::pair();
    let (seller_to_broker_ch, broker_from_seller_ch) = SimpleChannel::pair();
    let (broker_to_buyer_ch, buyer_from_broker_ch) = SimpleChannel::pair();
    let (broker_to_seller_ch, seller_from_broker_ch) = SimpleChannel::pair();

    // Register channels
    buyer_ep.register_channel(Role::Broker, buyer_to_broker_ch);
    buyer_ep.register_channel(Role::Broker, buyer_from_broker_ch); // Note: same peer, different direction

    seller_ep.register_channel(Role::Broker, seller_to_broker_ch);
    seller_ep.register_channel(Role::Broker, seller_from_broker_ch);

    broker_ep.register_channel(Role::Buyer, broker_from_buyer_ch);
    broker_ep.register_channel(Role::Seller, broker_from_seller_ch);
    broker_ep.register_channel(Role::Buyer, broker_to_buyer_ch);
    broker_ep.register_channel(Role::Seller, broker_to_seller_ch);

    // Create handlers
    let mut buyer_handler = TelltaleHandler::<Role, Message>::new();
    let mut seller_handler = TelltaleHandler::<Role, Message>::new();
    let mut broker_handler = TelltaleHandler::<Role, Message>::new();

    println!("Phase 1: Buyer makes initial offer to Broker");
    let initial_offer = Message::Offer {
        item: "Vintage Guitar".to_string(),
        price: 1000,
    };
    buyer_handler
        .send(&mut buyer_ep, Role::Broker, &initial_offer)
        .await?;
    println!("  Buyer → Broker: Offer for Vintage Guitar at $1000");

    let offer_from_buyer: Message = broker_handler.recv(&mut broker_ep, Role::Buyer).await?;
    println!("  Broker received offer from Buyer");

    println!("\nPhase 2: Broker forwards offer to Seller");
    broker_handler
        .send(&mut broker_ep, Role::Seller, &offer_from_buyer)
        .await?;

    let offer_from_broker: Message = seller_handler.recv(&mut seller_ep, Role::Broker).await?;
    if let Message::Offer { item, price } = offer_from_broker {
        println!("  Seller received: {item} at ${price}");

        // Seller makes counter-offer
        println!("\nPhase 3: Seller makes counter-offer");
        let counter = Message::Counter {
            item: item.clone(),
            price: 1200,
        };
        seller_handler
            .send(&mut seller_ep, Role::Broker, &counter)
            .await?;
        println!("  Seller → Broker: Counter-offer at $1200");
    }

    let counter_from_seller: Message = broker_handler.recv(&mut broker_ep, Role::Seller).await?;
    println!("  Broker received counter-offer from Seller");

    println!("\nPhase 4: Broker forwards counter-offer to Buyer");
    broker_handler
        .send(&mut broker_ep, Role::Buyer, &counter_from_seller)
        .await?;

    let counter_from_broker: Message = buyer_handler.recv(&mut buyer_ep, Role::Broker).await?;
    if let Message::Counter { item, price } = counter_from_broker {
        println!("  Buyer received counter: {item} at ${price}");

        // Buyer makes choice: accept or reject
        println!("\nPhase 5: Buyer makes decision");

        // For demo purposes, buyer accepts if price is at or below threshold
        let decision = if price <= BUYER_ACCEPT_PRICE_MAX {
            println!("  Buyer decides to ACCEPT");
            NegotiationLabel::Accept
        } else {
            println!("  Buyer decides to REJECT");
            NegotiationLabel::Reject
        };

        buyer_handler
            .choose(&mut buyer_ep, Role::Broker, decision)
            .await?;
    }

    let buyer_decision = broker_handler.offer(&mut broker_ep, Role::Buyer).await?;
    println!("\nPhase 6: Broker processes decision");

    if buyer_decision == NegotiationLabel::Accept {
        println!("  Broker: Finalizing sale...");
        let accept_msg = Message::Accept;
        broker_handler
            .send(&mut broker_ep, Role::Seller, &accept_msg)
            .await?;

        let _confirmation: Message = seller_handler.recv(&mut seller_ep, Role::Broker).await?;
        println!("  Seller: Sale confirmed!");
        println!("\nNegotiation successful!");
    } else {
        println!("  Broker: Negotiation failed");
        let reject_msg = Message::Reject;
        broker_handler
            .send(&mut broker_ep, Role::Seller, &reject_msg)
            .await?;

        let _rejection: Message = seller_handler.recv(&mut seller_ep, Role::Broker).await?;
        println!("  Seller: Offer rejected");
        println!("\nNegotiation failed");
    }

    // Display session metadata
    println!("\n=== Session Metadata ===");
    println!("Buyer operations: {}", buyer_ep.active_channel_count());
    println!("Seller operations: {}", seller_ep.active_channel_count());
    println!("Broker operations: {}", broker_ep.active_channel_count());

    // Cleanup
    buyer_ep.close_all_channels();
    seller_ep.close_all_channels();
    broker_ep.close_all_channels();

    println!("\n=== Protocol Complete ===");
    Ok(())
}
