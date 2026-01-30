#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

// Demo: Improved error messages with span information
//
// This example demonstrates the enhanced error reporting in the choreography parser.
// Run with: cargo run --example error_demo

use telltale_choreography::compiler::parser::parse_choreography_str;

fn main() {
    println!("=== Choreography Parser Error Message Demo ===\n");

    // Example 1: Undefined role in send statement
    println!("Example 1: Undefined role\n");
    let input1 = r"
protocol Example = {
    roles Alice, Bob
    
    Alice -> Charlie : Hello
    Bob -> Alice : World
}
";

    match parse_choreography_str(input1) {
        Ok(_) => println!("Unexpected success!"),
        Err(e) => println!("{e}"),
    }

    println!("\n{}\n", "=".repeat(60));

    // Example 2: Duplicate role declaration
    println!("Example 2: Duplicate role declaration\n");
    let input2 = r"
protocol DuplicateExample = {
    roles Alice, Bob, Charlie, Alice
    
    Alice -> Bob : Hello
}
";

    match parse_choreography_str(input2) {
        Ok(_) => println!("Unexpected success!"),
        Err(e) => println!("{e}"),
    }

    println!("\n{}\n", "=".repeat(60));

    // Example 3: Undefined role in loop condition
    println!("Example 3: Undefined role in loop\n");
    let input3 = r"
protocol LoopExample = {
    roles Client, Server
    
    loop decide by UnknownRole {
        Client -> Server : Request
    }
}
";

    match parse_choreography_str(input3) {
        Ok(_) => println!("Unexpected success!"),
        Err(e) => println!("{e}"),
    }

    println!("\n{}\n", "=".repeat(60));

    // Example 4: Invalid loop count
    println!("Example 4: Invalid loop condition\n");
    let input4 = r"
protocol CountExample = {
    roles A, B
    
    loop repeat not_a_number {
        A -> B : Ping
    }
}
";

    match parse_choreography_str(input4) {
        Ok(_) => println!("Unexpected success!"),
        Err(e) => println!("{e}"),
    }

    println!("\n{}\n", "=".repeat(60));

    // Example 5: Success case for comparison
    println!("Example 5: Valid choreography (for comparison)\n");
    let input5 = r"
protocol ValidExample = {
    roles Alice, Bob
    
    Alice -> Bob : Ping
    Bob -> Alice : Pong
}
";

    match parse_choreography_str(input5) {
        Ok(choreo) => {
            println!("Successfully parsed choreography: {}", choreo.name);
            println!(
                "  Roles: {}",
                choreo
                    .roles
                    .iter()
                    .map(|r| r.name().to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            );
        }
        Err(e) => println!("Error: {e}"),
    }
}
