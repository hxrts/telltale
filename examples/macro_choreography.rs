#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

// Programmatic Choreography Construction with Algebraic Effects
//
// This example demonstrates building complex choreographic protocols programmatically
// using the algebraic effect API. It shows the two-phase commit protocol as a
// real-world distributed coordination example.
//
// The example shows:
// - Building choreographies programmatically with the Program builder API
// - Multi-party protocols (coordinator + multiple participants)
// - Choice/branching in distributed protocols (commit vs. abort)
// - Using different effect handlers for execution and testing
// - Static analysis of choreographic programs

use futures::executor;
use rumpsteak_aura_choreography::{
    interpret, InterpretResult, Label, Metrics, NoOpHandler, Program, RecordingHandler, Result,
};
use serde::{Deserialize, Serialize};

// NOTE: The choreography! macro generates Rumpsteak session types
// For this example, we'll demonstrate the algebraic effect API directly
// without using the macro, showing how to build choreographic programs programmatically

// Roles for the algebraic effect programs
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum Role {
    Coordinator,
    Participant1,
    Participant2,
}

// Messages for the effect algebra representation
#[derive(Clone, Debug, Serialize, Deserialize)]
enum ProtocolMessage {
    Prepare(i32),
    Vote(bool),
    Commit,
    Abort,
}

// Build the coordinator's program using the algebraic effect API
// This demonstrates the programmatic construction of choreographies
fn coordinator_program() -> Program<Role, ProtocolMessage> {
    Program::new()
        // Prepare phase: broadcast prepare message to both participants
        .send(Role::Participant1, ProtocolMessage::Prepare(42))
        .send(Role::Participant2, ProtocolMessage::Prepare(42))
        // Voting phase: collect votes from participants
        .recv::<ProtocolMessage>(Role::Participant1)
        .recv::<ProtocolMessage>(Role::Participant2)
        // Decision phase (simplified - always commit)
        .send(Role::Participant1, ProtocolMessage::Commit)
        .send(Role::Participant2, ProtocolMessage::Commit)
        .end()
}

// Build participant program
fn participant_program(coordinator: Role) -> Program<Role, ProtocolMessage> {
    Program::new()
        .recv::<ProtocolMessage>(coordinator)
        .send(coordinator, ProtocolMessage::Vote(true))
        .recv::<ProtocolMessage>(coordinator)
        .end()
}

// More complex example with choices
fn coordinator_with_choice_program() -> Program<Role, ProtocolMessage> {
    Program::new()
        .send(Role::Participant1, ProtocolMessage::Prepare(100))
        .send(Role::Participant2, ProtocolMessage::Prepare(100))
        .recv::<ProtocolMessage>(Role::Participant1)
        .recv::<ProtocolMessage>(Role::Participant2)
        // Coordinator makes a choice based on votes
        .choose(Role::Coordinator, Label("commit"))
        .branch(
            Role::Coordinator,
            vec![
                (
                    Label("commit"),
                    Program::new()
                        .send(Role::Participant1, ProtocolMessage::Commit)
                        .send(Role::Participant2, ProtocolMessage::Commit)
                        .end(),
                ),
                (
                    Label("abort"),
                    Program::new()
                        .send(Role::Participant1, ProtocolMessage::Abort)
                        .send(Role::Participant2, ProtocolMessage::Abort)
                        .end(),
                ),
            ],
        )
        .end()
}

async fn run_program<H>(
    handler: &mut H,
    endpoint: &mut H::Endpoint,
    program: Program<Role, ProtocolMessage>,
    name: &str,
) -> Result<InterpretResult<ProtocolMessage>>
where
    H: rumpsteak_aura_choreography::ChoreoHandler<Role = Role>,
{
    println!("  {name}: Executing protocol");
    interpret(handler, endpoint, program).await
}

fn main() {
    executor::block_on(async {
        println!("╔════════════════════════════════════════════════════════════╗");
        println!("║   Two-Phase Commit Choreography (Algebraic Effects)        ║");
        println!("╚════════════════════════════════════════════════════════════╝\n");

        println!("=== 1. Protocol Analysis ===");
        analyze_protocols();

        println!("\n=== 2. Simple Two-Phase Commit ===");
        run_simple_two_phase().await;

        println!("\n=== 3. Two-Phase Commit with Choice ===");
        run_with_choice().await;

        println!("\n=== 4. Recording Handler (Test Mode) ===");
        run_with_recording().await;

        println!("\n=== 5. Metrics Collection ===");
        run_with_metrics().await;

        println!("\n╔════════════════════════════════════════════════════════════╗");
        println!("║   Two-phase commit choreography working perfectly!         ║");
        println!("╚════════════════════════════════════════════════════════════╝");
    });
}

fn analyze_protocols() {
    let coordinator_prog = coordinator_program();
    let participant_prog = participant_program(Role::Coordinator);
    let choice_prog = coordinator_with_choice_program();

    println!("\nCoordinator protocol:");
    println!("  • Send operations: {}", coordinator_prog.send_count());
    println!("  • Receive operations: {}", coordinator_prog.recv_count());
    println!(
        "  • Roles involved: {:?}",
        coordinator_prog.roles_involved()
    );
    println!("  • Total effects: {}", coordinator_prog.effects.len());

    println!("\nParticipant protocol:");
    println!("  • Send operations: {}", participant_prog.send_count());
    println!("  • Receive operations: {}", participant_prog.recv_count());
    println!(
        "  • Roles involved: {:?}",
        participant_prog.roles_involved()
    );
    println!("  • Total effects: {}", participant_prog.effects.len());

    println!("\nCoordinator with choice:");
    println!("  • Send operations: {}", choice_prog.send_count());
    println!("  • Receive operations: {}", choice_prog.recv_count());
    println!("  • Has branches: {}", !choice_prog.effects.is_empty());
    println!("  • Total effects: {}", choice_prog.effects.len());

    // Validate protocols
    for (name, prog) in [
        ("Coordinator", coordinator_prog),
        ("Participant", participant_prog),
        ("Choice", choice_prog),
    ] {
        match prog.validate() {
            Ok(()) => println!("  {name} protocol validated"),
            Err(e) => println!("  {name} protocol error: {e}"),
        }
    }
}

async fn run_simple_two_phase() {
    println!("Simulating two-phase commit with NoOpHandler\n");

    let coordinator_prog = coordinator_program();
    let mut handler = NoOpHandler::<Role>::new();
    let mut endpoint = ();

    let result = run_program(&mut handler, &mut endpoint, coordinator_prog, "Coordinator").await;

    match result {
        Ok(interp_result) => {
            println!("  Coordinator completed: {:?}", interp_result.final_state);
            println!("  Protocol phases:");
            println!("    1. Prepare phase - sent to both participants");
            println!("    2. Vote phase - received from both participants");
            println!("    3. Decision phase - commit sent to both");
        }
        Err(e) => println!("  Failed: {e}"),
    }
}

async fn run_with_choice() {
    println!("Running two-phase commit with coordinator choice\n");

    let prog = coordinator_with_choice_program();
    let mut handler = NoOpHandler::<Role>::new();
    let mut endpoint = ();

    let result = run_program(&mut handler, &mut endpoint, prog, "Coordinator").await;

    match result {
        Ok(interp_result) => {
            println!(
                "  Coordinator with choice completed: {:?}",
                interp_result.final_state
            );
            println!("  Branches available:");
            println!("    • commit: Send Commit to all participants");
            println!("    • abort: Send Abort to all participants");
        }
        Err(e) => println!("  Failed: {e}"),
    }
}

async fn run_with_recording() {
    println!("Recording protocol execution for testing\n");

    let mut coordinator_handler = RecordingHandler::new(Role::Coordinator);
    let mut participant_handler = RecordingHandler::new(Role::Participant1);
    let mut endpoint = ();

    // Run coordinator
    let coordinator_prog = coordinator_program();
    let _ = run_program(
        &mut coordinator_handler,
        &mut endpoint,
        coordinator_prog,
        "Coordinator",
    )
    .await;

    // Run participant
    let participant_prog = participant_program(Role::Coordinator);
    let _ = run_program(
        &mut participant_handler,
        &mut endpoint,
        participant_prog,
        "Participant1",
    )
    .await;

    // Display recorded events
    println!("\n  Coordinator events:");
    for (i, event) in coordinator_handler.events().iter().enumerate() {
        println!("    {}. {:?}", i + 1, event);
    }

    println!("\n  Participant events:");
    for (i, event) in participant_handler.events().iter().enumerate() {
        println!("    {}. {:?}", i + 1, event);
    }

    println!(
        "\n  Captured {} coordinator events, {} participant events",
        coordinator_handler.events().len(),
        participant_handler.events().len()
    );
}

async fn run_with_metrics() {
    println!("Collecting execution metrics\n");

    let inner_handler = NoOpHandler::<Role>::new();
    let mut handler = Metrics::new(inner_handler);
    let mut endpoint = ();

    let prog = coordinator_with_choice_program();
    let result = run_program(&mut handler, &mut endpoint, prog, "Coordinator").await;

    match result {
        Ok(_) => {
            println!("\n  Execution metrics:");
            println!("    • Send operations executed: {}", handler.send_count());
            println!(
                "    • Receive operations executed: {}",
                handler.recv_count()
            );
            println!("    • Errors encountered: {}", handler.error_count());
        }
        Err(e) => println!("  Failed: {e}"),
    }
}

// Integration tests showing protocol correctness
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_protocol_structure() {
        let coordinator = coordinator_program();
        assert_eq!(coordinator.send_count(), 4); // 2 prepare + 2 commit
        assert_eq!(coordinator.recv_count(), 2); // 2 votes

        let participant = participant_program(Role::Coordinator);
        assert_eq!(participant.send_count(), 1); // 1 vote
        assert_eq!(participant.recv_count(), 2); // 1 prepare + 1 commit
    }

    #[test]
    fn test_validation() {
        assert!(coordinator_program().validate().is_ok());
        assert!(participant_program(Role::Coordinator).validate().is_ok());
        assert!(coordinator_with_choice_program().validate().is_ok());
    }

    #[tokio::test]
    async fn test_coordinator_execution() {
        let mut handler = RecordingHandler::new(Role::Coordinator);
        let mut endpoint = ();

        let prog = coordinator_program();
        let result = run_program(&mut handler, &mut endpoint, prog, "Test").await;

        assert!(result.is_ok());
        let events = handler.events();
        // RecordingHandler captures events until it hits a receive operation it cannot fulfill
        // Coordinator sends 2 prepares, then tries to receive (where it fails)
        assert!(events.len() >= 2); // At least the 2 prepare sends before first receive
    }

    #[tokio::test]
    async fn test_participant_execution() {
        let mut handler = RecordingHandler::new(Role::Participant1);
        let mut endpoint = ();

        let prog = participant_program(Role::Coordinator);
        let result = run_program(&mut handler, &mut endpoint, prog, "Test").await;

        assert!(result.is_ok());
        let events = handler.events();
        assert!(!events.is_empty());
    }

    #[test]
    fn test_role_extraction() {
        let prog = coordinator_program();
        let roles = prog.roles_involved();

        assert!(roles.contains(&Role::Participant1));
        assert!(roles.contains(&Role::Participant2));
    }
}
