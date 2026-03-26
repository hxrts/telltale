//! Bounded recursion example driven from canonical `tell!` protocols.
//!
//! This is a theory-facing example: `tell!` remains the source of truth for the
//! recursive protocol surface, and the example projects the relevant local view
//! into `LocalTypeR` before running the bounded-recursion algorithms.

use anyhow::{anyhow, Result};
use telltale::tell;
use telltale_language::{ast::convert::local_to_local_r, parse_choreography_str, project};
use telltale_theory::bounded::{bound_recursion, unfold_bounded, BoundingStrategy};
use telltale_theory::limits::{FuelSteps, YieldAfterSteps};
use telltale_types::LocalTypeR;

tell! {
    -- // Client can keep the ping-pong loop going or stop.
    protocol PingPong =
      roles Client, Server
      rec loop
        choice Client at
          | Continue =>
            Client -> Server : Ping
            Server -> Client : Pong
            continue loop
          | Stop =>
            Client -> Server : Stop
}

tell! {
    -- // Client either continues the loop after an ack or stops.
    protocol ContinueOrStop =
      roles Client, Server
      rec outer
        choice Client at
          | Continue =>
            Client -> Server : Continue
            Server -> Client : Ack
            continue outer
          | Stop =>
            Client -> Server : Stop
}

tell! {
    -- // Three-party ring viewed from role A with an explicit stop branch.
    protocol RingToken =
      roles A, B, C
      rec ring
        choice A at
          | Continue =>
            A -> B : Token
            B -> C : Token
            C -> A : Token
            continue ring
          | Stop =>
            A -> B : Stop
            B -> C : Stop
}

fn local_view(source: &str, role_name: &str) -> Result<LocalTypeR> {
    let choreography = parse_choreography_str(source)?;
    let role = choreography
        .roles
        .iter()
        .find(|role| role.name() == role_name)
        .ok_or_else(|| anyhow!("role {role_name} not found in choreography"))?;
    let local = project(&choreography, role)?;
    Ok(local_to_local_r(&local)?)
}

fn main() -> Result<()> {
    println!("=== Bounded Recursion Example ===\n");

    // Start with a simple recursive ping-pong protocol.
    let ping = local_view(PingPong::SOURCE, "Client")?;
    println!("Original recursive protocol:\n{ping:#?}\n");

    // 1. Fuel: hard cap on iterations.
    let fuel = bound_recursion(&ping, BoundingStrategy::Fuel(FuelSteps(3)));
    println!("1. Fuel(3):\n{fuel:#?}\n");

    // 2. YieldAfter: cooperative yield point after N steps.
    let yielded = bound_recursion(&ping, BoundingStrategy::YieldAfter(YieldAfterSteps(5)));
    println!("2. YieldAfter(5):\n{yielded:#?}\n");

    // 3. YieldWhen: yield on a named condition.
    let conditional = bound_recursion(&ping, BoundingStrategy::YieldWhen("done".into()));
    println!("3. YieldWhen(\"done\"):\n{conditional:#?}\n");

    // 4. Unfold: expand recursive structure to fixed depth.
    let unfolded = unfold_bounded(&ping, 2);
    println!("4. Unfold depth 2:\n{unfolded:#?}\n");

    // 5. Choice protocol with Fuel bounding.
    let choice = local_view(ContinueOrStop::SOURCE, "Client")?;
    let bounded_choice = bound_recursion(&choice, BoundingStrategy::Fuel(FuelSteps(2)));
    println!("5. Choice protocol bounded Fuel(2):\n{bounded_choice:#?}\n");

    // 6. Ring protocol with Fuel bounding.
    let ring = local_view(RingToken::SOURCE, "A")?;
    let bounded_ring = bound_recursion(&ring, BoundingStrategy::Fuel(FuelSteps(5)));
    println!("6. Ring (role A) bounded Fuel(5):\n{bounded_ring:#?}\n");

    println!("=== Bounded Recursion Demo Complete ===");
    Ok(())
}
