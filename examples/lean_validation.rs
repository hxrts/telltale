//! Lean Validation Example
//!
//! This example demonstrates how to use the Lean bridge to validate
//! protocol definitions by converting between Rust and Lean JSON format.
//!
//! Run with: cargo run --example lean_validation

use rumpsteak_lean_bridge::{global_to_json, json_to_global, json_to_local, local_to_json};
use rumpsteak_types::{GlobalType, Label, LocalTypeR};

#[allow(clippy::too_many_lines)]
fn main() {
    println!("=== Lean Validation Example ===\n");

    // Example 1: Simple ping-pong protocol
    println!("1. Simple Ping-Pong Protocol");
    println!("----------------------------");

    let ping_pong = GlobalType::comm(
        "Client",
        "Server",
        vec![(
            Label::new("ping"),
            GlobalType::comm(
                "Server",
                "Client",
                vec![(Label::new("pong"), GlobalType::End)],
            ),
        )],
    );

    // Export to JSON
    let json = global_to_json(&ping_pong);
    println!(
        "GlobalType JSON:\n{}\n",
        serde_json::to_string_pretty(&json).unwrap()
    );

    // Round-trip validation
    let parsed = json_to_global(&json).expect("Failed to parse JSON");
    assert_eq!(ping_pong, parsed);
    println!("✓ Round-trip validation successful\n");

    // Example 2: Calculator protocol with choice
    println!("2. Calculator Protocol with Choice");
    println!("----------------------------------");

    let calculator = GlobalType::comm(
        "Client",
        "Server",
        vec![
            (
                Label::new("add"),
                GlobalType::comm(
                    "Server",
                    "Client",
                    vec![(Label::new("result"), GlobalType::End)],
                ),
            ),
            (
                Label::new("sub"),
                GlobalType::comm(
                    "Server",
                    "Client",
                    vec![(Label::new("result"), GlobalType::End)],
                ),
            ),
            (Label::new("quit"), GlobalType::End),
        ],
    );

    let json = global_to_json(&calculator);
    println!(
        "GlobalType JSON:\n{}\n",
        serde_json::to_string_pretty(&json).unwrap()
    );

    let parsed = json_to_global(&json).expect("Failed to parse JSON");
    assert_eq!(calculator, parsed);
    println!("✓ Round-trip validation successful\n");

    // Example 3: Recursive protocol
    println!("3. Recursive Ring Protocol");
    println!("--------------------------");

    let ring = GlobalType::mu(
        "loop",
        GlobalType::comm(
            "A",
            "B",
            vec![(
                Label::new("token"),
                GlobalType::comm(
                    "B",
                    "C",
                    vec![(
                        Label::new("token"),
                        GlobalType::comm(
                            "C",
                            "A",
                            vec![(Label::new("token"), GlobalType::var("loop"))],
                        ),
                    )],
                ),
            )],
        ),
    );

    let json = global_to_json(&ring);
    println!(
        "GlobalType JSON:\n{}\n",
        serde_json::to_string_pretty(&json).unwrap()
    );

    let parsed = json_to_global(&json).expect("Failed to parse JSON");
    assert_eq!(ring, parsed);
    println!("✓ Round-trip validation successful\n");

    // Example 4: LocalTypeR validation
    println!("4. LocalTypeR Validation");
    println!("------------------------");

    let client_local = LocalTypeR::send(
        "Server",
        Label::new("request"),
        LocalTypeR::recv("Server", Label::new("response"), LocalTypeR::End),
    );

    let json = local_to_json(&client_local);
    println!(
        "LocalTypeR JSON:\n{}\n",
        serde_json::to_string_pretty(&json).unwrap()
    );

    let parsed = json_to_local(&json).expect("Failed to parse JSON");
    assert_eq!(client_local, parsed);
    println!("✓ Round-trip validation successful\n");

    // Example 5: Recursive LocalTypeR
    println!("5. Recursive LocalTypeR");
    println!("-----------------------");

    let recursive_local = LocalTypeR::mu(
        "ping_loop",
        LocalTypeR::send(
            "Server",
            Label::new("ping"),
            LocalTypeR::recv("Server", Label::new("pong"), LocalTypeR::var("ping_loop")),
        ),
    );

    let json = local_to_json(&recursive_local);
    println!(
        "LocalTypeR JSON:\n{}\n",
        serde_json::to_string_pretty(&json).unwrap()
    );

    let parsed = json_to_local(&json).expect("Failed to parse JSON");
    assert_eq!(recursive_local, parsed);
    println!("✓ Round-trip validation successful\n");

    println!("=== All validations passed! ===");
}
