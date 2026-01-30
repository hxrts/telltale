//! Bounded Recursion Example
//!
//! This example demonstrates bounded recursion strategies for session types.
//! Bounded recursion is essential for:
//! - Formal verification (Lean proofs require finite unfolding)
//! - Runtime safety (preventing infinite loops)
//! - Testing (deterministic execution)
//!
//! Run with: cargo run --example bounded_recursion

use telltale_theory::{
    bound_recursion, unfold_bounded, BoundingStrategy, FuelSteps, YieldAfterSteps,
};
use telltale_types::{Label, LocalTypeR};

fn main() {
    println!("=== Bounded Recursion Example ===\n");

    // Create a recursive ping-pong protocol
    let recursive_protocol = LocalTypeR::mu(
        "loop",
        LocalTypeR::send(
            "Server",
            Label::new("ping"),
            LocalTypeR::recv("Server", Label::new("pong"), LocalTypeR::var("loop")),
        ),
    );

    println!("Original recursive protocol:");
    println!("{:#?}\n", recursive_protocol);

    // Strategy 1: Fuel-based bounding
    println!("1. Fuel Strategy (max 3 iterations)");
    println!("-----------------------------------");
    let fuel_bounded = bound_recursion(&recursive_protocol, BoundingStrategy::Fuel(FuelSteps(3)));
    println!("Bounded protocol with Fuel(3):");
    println!("{:#?}\n", fuel_bounded);

    // Strategy 2: YieldAfter bounding
    println!("2. YieldAfter Strategy (yield after 5 steps)");
    println!("--------------------------------------------");
    let yield_bounded = bound_recursion(
        &recursive_protocol,
        BoundingStrategy::YieldAfter(YieldAfterSteps(5)),
    );
    println!("Bounded protocol with YieldAfter(5):");
    println!("{:#?}\n", yield_bounded);

    // Strategy 3: YieldWhen bounding
    println!("3. YieldWhen Strategy (yield when condition met)");
    println!("------------------------------------------------");
    let condition_bounded = bound_recursion(
        &recursive_protocol,
        BoundingStrategy::YieldWhen("done".to_string()),
    );
    println!("Bounded protocol with YieldWhen(\"done\"):");
    println!("{:#?}\n", condition_bounded);

    // Unfold bounded: explicitly expand recursion
    println!("4. Unfold Bounded (expand to depth 2)");
    println!("-------------------------------------");
    let unfolded = unfold_bounded(&recursive_protocol, 2);
    println!("Unfolded to depth 2:");
    println!("{:#?}\n", unfolded);

    // More complex example: nested recursion
    println!("5. Complex Protocol with Choice");
    println!("-------------------------------");

    let complex_protocol = LocalTypeR::mu(
        "outer",
        LocalTypeR::Send {
            partner: "Server".to_string(),
            branches: vec![
                (
                    Label::new("continue"),
                    LocalTypeR::recv("Server", Label::new("ack"), LocalTypeR::var("outer")),
                ),
                (Label::new("stop"), LocalTypeR::End),
            ],
        },
    );

    println!("Complex recursive protocol with choice:");
    println!("{:#?}\n", complex_protocol);

    let bounded_complex = bound_recursion(&complex_protocol, BoundingStrategy::Fuel(FuelSteps(2)));
    println!("Bounded with Fuel(2):");
    println!("{:#?}\n", bounded_complex);

    // Example: Ring protocol with bounded recursion
    println!("6. Ring Protocol Example");
    println!("------------------------");

    // A's view of a 3-party ring
    let ring_a = LocalTypeR::mu(
        "ring",
        LocalTypeR::recv(
            "C",
            Label::new("token"),
            LocalTypeR::send("B", Label::new("token"), LocalTypeR::var("ring")),
        ),
    );

    println!("Role A's view of ring protocol:");
    println!("{:#?}\n", ring_a);

    let bounded_ring = bound_recursion(&ring_a, BoundingStrategy::Fuel(FuelSteps(5)));
    println!("Bounded ring (Fuel 5):");
    println!("{:#?}\n", bounded_ring);

    println!("=== Bounded Recursion Demo Complete ===");
}
