#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

// Choreographic Programming Example
//
// This example demonstrates the free algebra approach to choreographic programming,
// where protocols are built as data structures that can be analyzed, transformed,
// and interpreted using different handlers.
//
// The example shows:
// - Building choreographic programs using the Program builder API
// - Analyzing programs statically (counting operations, extracting roles)
// - Using different handlers (Recording, NoOp) to execute protocols
// - Composing handlers with middleware (Trace, Metrics, Retry)

use futures::executor;
use rumpsteak_aura_choreography::{
    interpret, InterpretResult, Label, Metrics, NoOpHandler, Program, RecordingHandler, Result,
    Retry, Trace,
};
use serde::{Deserialize, Serialize};
use std::time::Duration;

// Define protocol roles
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum Role {
    Alice,
    Bob,
    Carol,
}

// Define unified message type for this choreography
#[derive(Clone, Debug, Serialize, Deserialize)]
enum Message {
    Greeting(String),
    Reply(String),
    Data(i32),
    Farewell,
}

// Example 1: Simple two-party protocol
fn two_party_program() -> Program<Role, Message> {
    Program::new()
        .send(Role::Bob, Message::Greeting("Hello Bob!".to_string()))
        .recv::<Message>(Role::Bob)
        .send(Role::Bob, Message::Farewell)
        .end()
}

// Example 2: Three-party protocol with branching
fn three_party_program() -> Program<Role, Message> {
    Program::new()
        .send(Role::Bob, Message::Greeting("Hello Bob!".to_string()))
        .send(Role::Carol, Message::Greeting("Hello Carol!".to_string()))
        .choose(Role::Alice, Label("continue"))
        .branch(
            Role::Alice,
            vec![
                (
                    Label("continue"),
                    Program::new()
                        .send(Role::Bob, Message::Data(42))
                        .recv::<Message>(Role::Carol)
                        .end(),
                ),
                (
                    Label("stop"),
                    Program::new().send(Role::Bob, Message::Farewell).end(),
                ),
            ],
        )
        .end()
}

// Example 3: Protocol with timeout and parallel composition
fn advanced_program() -> Program<Role, Message> {
    Program::new()
        .with_timeout(
            Role::Alice,
            Duration::from_secs(5),
            Program::new()
                .send(Role::Bob, Message::Greeting("Quick hello!".to_string()))
                .recv::<Message>(Role::Bob)
                .end(),
        )
        .parallel(vec![
            Program::new().send(Role::Bob, Message::Data(1)).end(),
            Program::new().send(Role::Carol, Message::Data(2)).end(),
        ])
        .end()
}

// Example 4: Protocol with loops
fn looping_program() -> Program<Role, Message> {
    Program::new()
        .loop_n(
            3,
            Program::new()
                .send(Role::Bob, Message::Data(1))
                .recv::<Message>(Role::Bob),
        )
        .send(Role::Bob, Message::Farewell)
        .end()
}

// Generic program runner
async fn run_program<H>(
    handler: &mut H,
    endpoint: &mut H::Endpoint,
    program: Program<Role, Message>,
    name: &str,
) -> Result<InterpretResult<Message>>
where
    H: rumpsteak_aura_choreography::ChoreoHandler<Role = Role>,
{
    println!("{name}: Starting choreography");
    interpret(handler, endpoint, program).await
}

fn main() {
    executor::block_on(async {
        println!("╔════════════════════════════════════════════════════════════╗");
        println!("║   Choreographic Programming - Free Algebra Examples       ║");
        println!("╚════════════════════════════════════════════════════════════╝\n");

        println!("=== 1. Program Analysis ===");
        analyze_programs();

        println!("\n=== 2. Recording Handler (captures events) ===");
        run_with_recording().await;

        println!("\n=== 3. NoOp Handler (validates structure) ===");
        run_with_noop().await;

        println!("\n=== 4. Traced Handler (debugging) ===");
        run_with_tracing().await;

        println!("\n=== 5. Metrics Handler (statistics) ===");
        run_with_metrics().await;

        println!("\n=== 6. Retry Handler (fault tolerance) ===");
        run_with_retry().await;

        println!("\n╔════════════════════════════════════════════════════════════╗");
        println!("║   All examples completed successfully!                     ║");
        println!("╚════════════════════════════════════════════════════════════╝");
    });
}

fn analyze_programs() {
    let programs = vec![
        ("Two-party", two_party_program()),
        ("Three-party", three_party_program()),
        ("Advanced", advanced_program()),
        ("Looping", looping_program()),
    ];

    for (name, prog) in programs {
        println!("\n{name} protocol:");
        println!("  • Send operations: {}", prog.send_count());
        println!("  • Receive operations: {}", prog.recv_count());
        println!("  • Roles involved: {:?}", prog.roles_involved());
        println!("  • Has timeouts: {}", prog.has_timeouts());
        println!("  • Has parallel: {}", prog.has_parallel());
        println!("  • Total effects: {}", prog.effects.len());

        if let Err(e) = prog.validate() {
            println!("  Validation error: {e}");
        } else {
            println!("  Validation passed");
        }
    }
}

async fn run_with_recording() {
    println!("Recording handler captures all choreographic operations for testing/verification.\n");

    let mut handler = RecordingHandler::new(Role::Alice);
    let mut endpoint = ();

    let program = two_party_program();
    let result = run_program(&mut handler, &mut endpoint, program, "Alice").await;

    match result {
        Ok(interp_result) => {
            println!("Execution completed: {:?}", interp_result.final_state);
            println!("  Captured {} events:", handler.events().len());
            for (i, event) in handler.events().iter().enumerate() {
                println!("    {}. {:?}", i + 1, event);
            }
        }
        Err(e) => println!("Execution failed: {e}"),
    }
}

async fn run_with_noop() {
    println!("NoOp handler validates protocol structure without executing operations.\n");

    let mut handler = NoOpHandler::<Role>::new();
    let mut endpoint = ();

    let program = three_party_program();
    let result = run_program(&mut handler, &mut endpoint, program, "Alice").await;

    match result {
        Ok(interp_result) => {
            println!("Protocol structure validated");
            println!("  Final state: {:?}", interp_result.final_state);
        }
        Err(e) => println!("Validation failed: {e}"),
    }
}

async fn run_with_tracing() {
    println!("Trace middleware logs all operations for debugging (uses tracing crate).\n");

    let inner_handler = NoOpHandler::<Role>::new();
    let mut handler = Trace::with_prefix(inner_handler, "alice");
    let mut endpoint = ();

    let program = two_party_program();
    let result = run_program(&mut handler, &mut endpoint, program, "Alice").await;

    match result {
        Ok(interp_result) => {
            println!(
                "Traced execution completed: {:?}",
                interp_result.final_state
            );
            println!("  (Check logs with RUST_LOG=debug for detailed traces)");
        }
        Err(e) => println!("Execution failed: {e}"),
    }
}

async fn run_with_metrics() {
    println!("Metrics middleware collects statistics about protocol execution.\n");

    let inner_handler = NoOpHandler::<Role>::new();
    let mut handler = Metrics::new(inner_handler);
    let mut endpoint = ();

    let program = looping_program();
    let result = run_program(&mut handler, &mut endpoint, program, "Bob").await;

    match result {
        Ok(interp_result) => {
            println!("Execution completed: {:?}", interp_result.final_state);
        }
        Err(e) => println!("Execution failed: {e}"),
    }

    println!("\nCollected metrics:");
    println!("  • Send operations: {}", handler.send_count());
    println!("  • Receive operations: {}", handler.recv_count());
    println!("  • Errors encountered: {}", handler.error_count());
}

async fn run_with_retry() {
    println!("Retry middleware adds automatic retry logic with exponential backoff.\n");

    let inner_handler = NoOpHandler::<Role>::new();
    let mut handler = Retry::with_config(inner_handler, 3, Duration::from_millis(100));
    let mut endpoint = ();

    let program = two_party_program();
    let result = run_program(&mut handler, &mut endpoint, program, "Carol").await;

    match result {
        Ok(interp_result) => {
            println!(
                "Execution completed with retry support: {:?}",
                interp_result.final_state
            );
            println!("  (Retries up to 3 times on failure with 100ms base delay)");
        }
        Err(e) => println!("Execution failed after retries: {e}"),
    }
}

// Protocol-agnostic testing demonstrates how choreographies can be tested
// without actual network communication
#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_two_party_protocol() {
        let mut handler = RecordingHandler::new(Role::Alice);
        let mut endpoint = ();

        let program = two_party_program();
        let result = run_program(&mut handler, &mut endpoint, program, "Alice").await;

        assert!(result.is_ok());

        // Verify captured events
        // RecordingHandler captures events until it cannot produce a value (at receive)
        let events = handler.events();
        assert!(events.len() >= 2); // At least 2 sends captured before failure at receive
    }

    #[test]
    fn test_program_analysis() {
        let program = two_party_program();
        assert_eq!(program.send_count(), 2);
        assert_eq!(program.recv_count(), 1);
        assert!(program.roles_involved().contains(&Role::Bob));
        assert!(!program.has_timeouts());
        assert!(!program.has_parallel());
    }

    #[test]
    fn test_advanced_features() {
        let program = advanced_program();
        assert!(program.has_timeouts());
        assert!(program.has_parallel());

        let looping = looping_program();
        assert!(looping.send_count() > 1); // Loop multiplies operations
    }

    #[test]
    fn test_validation() {
        // Valid programs should pass validation
        assert!(two_party_program().validate().is_ok());
        assert!(three_party_program().validate().is_ok());
        assert!(advanced_program().validate().is_ok());
        assert!(looping_program().validate().is_ok());
    }
}
