#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

// Edge case testing for the effects system
//
// This test module covers:
// - Effect interpreter edge cases
// - Middleware composition patterns
// - Error handling paths
// - Complex protocol scenarios

use futures::executor;
use serde::{Deserialize, Serialize};
use std::time::Duration;
use telltale_choreography::{
    interpret, LabelId, Metrics, NoOpHandler, Program, RecordingHandler, Retry, RoleId, RoleName,
    Trace,
};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum TestRole {
    Alice,
    Bob,
    Charlie,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum TestLabel {
    OptionA,
    BranchA,
    BranchB,
    Inner,
    Outer,
}

impl LabelId for TestLabel {
    fn as_str(&self) -> &'static str {
        match self {
            TestLabel::OptionA => "option_a",
            TestLabel::BranchA => "branch_a",
            TestLabel::BranchB => "branch_b",
            TestLabel::Inner => "inner",
            TestLabel::Outer => "outer",
        }
    }

    fn from_str(label: &str) -> Option<Self> {
        match label {
            "option_a" => Some(TestLabel::OptionA),
            "branch_a" => Some(TestLabel::BranchA),
            "branch_b" => Some(TestLabel::BranchB),
            "inner" => Some(TestLabel::Inner),
            "outer" => Some(TestLabel::Outer),
            _ => None,
        }
    }
}

impl RoleId for TestRole {
    type Label = TestLabel;

    fn role_name(&self) -> RoleName {
        match self {
            TestRole::Alice => RoleName::from_static("Alice"),
            TestRole::Bob => RoleName::from_static("Bob"),
            TestRole::Charlie => RoleName::from_static("Charlie"),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
enum TestMessage {
    Hello(String),
    Data(i32),
    Quit,
}

// Test 1: Empty program execution
#[test]
fn test_empty_program() {
    executor::block_on(async {
        let program = Program::<TestRole, TestMessage>::new().end();

        let mut handler = NoOpHandler::new();
        let mut endpoint = ();

        let result = interpret(&mut handler, &mut endpoint, program).await;
        assert!(result.is_ok());

        let interp_result = result.unwrap();
        assert!(interp_result.received_values.is_empty());
    });
}

// Test 2: Single send operation
#[test]
fn test_single_send() {
    executor::block_on(async {
        let program = Program::<TestRole, TestMessage>::new()
            .send(TestRole::Bob, TestMessage::Hello("test".into()))
            .end();

        let mut handler = RecordingHandler::new(TestRole::Alice);
        let mut endpoint = ();

        let result = interpret(&mut handler, &mut endpoint, program).await;
        assert!(result.is_ok());

        let events = handler.events();
        assert_eq!(events.len(), 1);
    });
}

// Test 3: Send-receive sequence
#[test]
fn test_send_recv_sequence() {
    executor::block_on(async {
        let program = Program::<TestRole, TestMessage>::new()
            .send(TestRole::Bob, TestMessage::Data(42))
            .recv::<TestMessage>(TestRole::Bob)
            .send(TestRole::Charlie, TestMessage::Quit)
            .end();

        let mut handler = RecordingHandler::new(TestRole::Alice);
        let mut endpoint = ();

        let result = interpret(&mut handler, &mut endpoint, program).await;
        assert!(result.is_ok());

        let events = handler.events();
        // Should record 2 sends (receive fails as it can't produce a value)
        assert!(events.len() >= 2);
    });
}

// Test 4: Choose operation
#[test]
fn test_choose_operation() {
    executor::block_on(async {
        let program = Program::<TestRole, TestMessage>::new()
            .choose(TestRole::Alice, TestLabel::OptionA)
            .end();

        let mut handler = RecordingHandler::new(TestRole::Alice);
        let mut endpoint = ();

        let result = interpret(&mut handler, &mut endpoint, program).await;
        assert!(result.is_ok());
    });
}

// Test 5: Branch with multiple options
#[test]
fn test_branch_operation() {
    executor::block_on(async {
        let program = Program::<TestRole, TestMessage>::new()
            .choose(TestRole::Alice, TestLabel::BranchA)
            .branch(
                TestRole::Alice,
                vec![
                    (
                        TestLabel::BranchA,
                        Program::<TestRole, TestMessage>::new()
                            .send(TestRole::Bob, TestMessage::Data(1))
                            .end(),
                    ),
                    (
                        TestLabel::BranchB,
                        Program::<TestRole, TestMessage>::new()
                            .send(TestRole::Bob, TestMessage::Data(2))
                            .end(),
                    ),
                ],
            )
            .end();

        let mut handler = RecordingHandler::new(TestRole::Alice);
        let mut endpoint = ();

        let result = interpret(&mut handler, &mut endpoint, program).await;
        assert!(result.is_ok());
    });
}

// Test 6: Nested branches
#[test]
fn test_nested_branches() {
    executor::block_on(async {
        let inner_branch = Program::<TestRole, TestMessage>::new()
            .choose(TestRole::Bob, TestLabel::Inner)
            .branch(
                TestRole::Bob,
                vec![(
                    TestLabel::Inner,
                    Program::<TestRole, TestMessage>::new().end(),
                )],
            )
            .end();

        let program = Program::<TestRole, TestMessage>::new()
            .choose(TestRole::Alice, TestLabel::Outer)
            .branch(TestRole::Alice, vec![(TestLabel::Outer, inner_branch)])
            .end();

        let mut handler = NoOpHandler::new();
        let mut endpoint = ();

        let result = interpret(&mut handler, &mut endpoint, program).await;
        assert!(result.is_ok());
    });
}

// Test 7: Loop with fixed iterations
#[test]
fn test_loop_fixed_iterations() {
    executor::block_on(async {
        let program = Program::<TestRole, TestMessage>::new()
            .loop_n(
                3,
                Program::<TestRole, TestMessage>::new()
                    .send(TestRole::Bob, TestMessage::Data(42))
                    .end(),
            )
            .end();

        let mut handler = RecordingHandler::new(TestRole::Alice);
        let mut endpoint = ();

        let result = interpret(&mut handler, &mut endpoint, program).await;
        assert!(result.is_ok());

        let events = handler.events();
        // Should have 3 send events
        assert_eq!(events.len(), 3);
    });
}

// Test 8: Middleware - Trace handler
#[test]
fn test_trace_middleware() {
    executor::block_on(async {
        let program = Program::<TestRole, TestMessage>::new()
            .send(TestRole::Bob, TestMessage::Hello("trace_test".into()))
            .end();

        let inner = NoOpHandler::new();
        let mut handler = Trace::new(inner);
        let mut endpoint = ();

        let result = interpret(&mut handler, &mut endpoint, program).await;
        assert!(result.is_ok());
    });
}

// Test 9: Middleware - Retry handler
#[test]
fn test_retry_middleware() {
    executor::block_on(async {
        let program = Program::<TestRole, TestMessage>::new()
            .send(TestRole::Bob, TestMessage::Data(99))
            .end();

        let inner = NoOpHandler::new();
        let mut handler = Retry::with_config(inner, 3, Duration::from_millis(10));
        let mut endpoint = ();

        let result = interpret(&mut handler, &mut endpoint, program).await;
        assert!(result.is_ok());
    });
}

// Test 10: Middleware - Metrics handler
#[test]
fn test_metrics_middleware() {
    executor::block_on(async {
        let program = Program::<TestRole, TestMessage>::new()
            .send(TestRole::Bob, TestMessage::Data(1))
            .send(TestRole::Charlie, TestMessage::Data(2))
            .end();

        let inner = NoOpHandler::new();
        let mut handler = Metrics::new(inner);
        let mut endpoint = ();

        let result = interpret(&mut handler, &mut endpoint, program).await;
        assert!(result.is_ok());

        // Check metrics were collected
        assert_eq!(handler.send_count(), 2);
        assert_eq!(handler.recv_count(), 0);
    });
}

// Test 11: Stacked middleware
#[test]
fn test_stacked_middleware() {
    executor::block_on(async {
        let program = Program::<TestRole, TestMessage>::new()
            .send(TestRole::Bob, TestMessage::Hello("stacked".into()))
            .end();

        let base = NoOpHandler::new();
        let with_trace = Trace::new(base);
        let mut handler = Metrics::new(with_trace);
        let mut endpoint = ();

        let result = interpret(&mut handler, &mut endpoint, program).await;
        assert!(result.is_ok());

        assert_eq!(handler.send_count(), 1);
    });
}

// Test 12: Parallel effects
#[test]
fn test_parallel_effects() {
    executor::block_on(async {
        let prog1 = Program::<TestRole, TestMessage>::new()
            .send(TestRole::Bob, TestMessage::Data(1))
            .end();
        let prog2 = Program::<TestRole, TestMessage>::new()
            .send(TestRole::Charlie, TestMessage::Data(2))
            .end();

        let program = Program::<TestRole, TestMessage>::new()
            .parallel(vec![prog1, prog2])
            .end();

        let mut handler = RecordingHandler::new(TestRole::Alice);
        let mut endpoint = ();

        let result = interpret(&mut handler, &mut endpoint, program).await;
        assert!(result.is_ok());

        let events = handler.events();
        assert_eq!(events.len(), 2);
    });
}

// Test 13: Program validation
#[test]
fn test_program_validation() {
    let program = Program::<TestRole, TestMessage>::new()
        .send(TestRole::Bob, TestMessage::Data(42))
        .recv::<TestMessage>(TestRole::Bob)
        .end();

    let result = program.validate();
    assert!(result.is_ok());
}

// Test 14: Role extraction
#[test]
fn test_role_extraction() {
    let program = Program::<TestRole, TestMessage>::new()
        .send(TestRole::Bob, TestMessage::Data(1))
        .send(TestRole::Charlie, TestMessage::Data(2))
        .recv::<TestMessage>(TestRole::Bob)
        .end();

    let roles = program.roles_involved();
    assert_eq!(roles.len(), 2);
    assert!(roles.contains(&TestRole::Bob));
    assert!(roles.contains(&TestRole::Charlie));
}

// Test 15: Effect counting
#[test]
fn test_effect_counting() {
    let program = Program::<TestRole, TestMessage>::new()
        .send(TestRole::Bob, TestMessage::Data(1))
        .send(TestRole::Bob, TestMessage::Data(2))
        .recv::<TestMessage>(TestRole::Charlie)
        .end();

    assert_eq!(program.send_count(), 2);
    assert_eq!(program.recv_count(), 1);
}

// Test 16: Program introspection
#[test]
fn test_program_introspection() {
    let program = Program::<TestRole, TestMessage>::new()
        .send(TestRole::Bob, TestMessage::Data(1))
        .send(TestRole::Charlie, TestMessage::Data(2))
        .end();

    // Test effect counting
    assert_eq!(program.send_count(), 2);

    // Test role involvement
    let roles = program.roles_involved();
    assert!(roles.contains(&TestRole::Bob));
    assert!(roles.contains(&TestRole::Charlie));
}

// Test 17: Complex nested program
#[test]
fn test_complex_nested_program() {
    executor::block_on(async {
        let inner_loop = Program::<TestRole, TestMessage>::new()
            .send(TestRole::Bob, TestMessage::Data(42))
            .end();

        let program = Program::<TestRole, TestMessage>::new()
            .loop_n(2, inner_loop)
            .send(TestRole::Charlie, TestMessage::Quit)
            .end();

        let mut handler = NoOpHandler::new();
        let mut endpoint = ();

        let result = interpret(&mut handler, &mut endpoint, program).await;
        assert!(result.is_ok());
    });
}

// Test 18: Multiple consecutive receives
#[test]
fn test_multiple_receives() {
    executor::block_on(async {
        let program = Program::<TestRole, TestMessage>::new()
            .recv::<TestMessage>(TestRole::Bob)
            .recv::<TestMessage>(TestRole::Charlie)
            .end();

        let mut handler = NoOpHandler::new();
        let mut endpoint = ();

        let result = interpret(&mut handler, &mut endpoint, program).await;
        // Will succeed but receives won't produce values with NoOpHandler
        assert!(result.is_ok());
    });
}

// Test 19: Empty parallel
#[test]
#[should_panic(expected = "Parallel must contain at least one program")]
fn test_empty_parallel() {
    executor::block_on(async {
        let program = Program::<TestRole, TestMessage>::new()
            .parallel(vec![])
            .end();

        let mut handler = NoOpHandler::new();
        let mut endpoint = ();

        let result = interpret(&mut handler, &mut endpoint, program).await;
        assert!(result.is_ok());
    });
}

// Test 20: Large program composition
#[test]
fn test_large_composition() {
    executor::block_on(async {
        let mut builder = Program::<TestRole, TestMessage>::new();

        // Build a large program with many effects
        for i in 0..10 {
            builder = builder.send(TestRole::Bob, TestMessage::Data(i));
        }
        let program = builder.end();

        let mut handler = Metrics::new(NoOpHandler::new());
        let mut endpoint = ();

        let result = interpret(&mut handler, &mut endpoint, program).await;
        assert!(result.is_ok());
        assert_eq!(handler.send_count(), 10);
    });
}
