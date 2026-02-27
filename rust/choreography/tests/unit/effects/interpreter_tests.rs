use super::*;
use crate::effects::{LabelId, RoleId};
use crate::identifiers::RoleName;
use std::time::Duration;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum TestRole {
    Alice,
    Bob,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum TestLabel {
    Continue,
}

impl LabelId for TestLabel {
    fn as_str(&self) -> &'static str {
        match self {
            TestLabel::Continue => "continue",
        }
    }

    fn from_str(label: &str) -> Option<Self> {
        match label {
            "continue" => Some(TestLabel::Continue),
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
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, serde::Deserialize)]
struct TestMessage(String);

#[tokio::test]
async fn test_simple_program() {
    let program = Program::new()
        .send(TestRole::Bob, TestMessage("hello".into()))
        .recv::<TestMessage>(TestRole::Bob)
        .end();

    let mut handler = testing::MockHandler::new(TestRole::Alice);
    handler.add_response(testing::MockResponse::Message(
        bincode::serialize(&TestMessage("reply".into()))
            .expect("serialize test message for scripted response"),
    ));

    let mut endpoint = ();
    let result = interpret(&mut handler, &mut endpoint, program)
        .await
        .expect("interpret simple program");

    assert_eq!(result.final_state, InterpreterState::Completed);
    assert_eq!(result.received_values.len(), 1);
}

#[test]
fn test_program_analysis() {
    let program = Program::new()
        .send(TestRole::Bob, TestMessage("hello".into()))
        .recv::<TestMessage>(TestRole::Bob)
        .choose(TestRole::Alice, TestLabel::Continue)
        .end();

    assert_eq!(program.send_count(), 1);
    assert_eq!(program.recv_count(), 1);
    assert!(!program.has_timeouts());
    assert!(!program.has_parallel());

    let roles = program.roles_involved();
    assert!(roles.contains(&TestRole::Alice));
    assert!(roles.contains(&TestRole::Bob));
}

#[tokio::test]
async fn test_branch_does_not_duplicate_received_values() {
    let selected_branch = Program::<TestRole, TestMessage>::new()
        .recv::<TestMessage>(TestRole::Bob)
        .end();
    let program = Program::<TestRole, TestMessage>::new()
        .choose(TestRole::Alice, TestLabel::Continue)
        .branch(TestRole::Alice, vec![(TestLabel::Continue, selected_branch)])
        .end();

    let mut handler = testing::MockHandler::new(TestRole::Alice);
    handler.add_response(testing::MockResponse::Message(
        bincode::serialize(&TestMessage("branch-reply".into()))
            .expect("serialize branch response"),
    ));

    let mut endpoint = ();
    let result = interpret(&mut handler, &mut endpoint, program)
        .await
        .expect("interpret branch program");

    assert_eq!(result.final_state, InterpreterState::Completed);
    assert_eq!(
        result.received_values.len(),
        1,
        "branch execution must not duplicate received values"
    );
}

#[tokio::test]
async fn test_loop_does_not_duplicate_received_values() {
    let body = Program::<TestRole, TestMessage>::new()
        .recv::<TestMessage>(TestRole::Bob)
        .end();
    let program = Program::<TestRole, TestMessage>::new().loop_n(2, body).end();

    let mut handler = testing::MockHandler::new(TestRole::Alice);
    handler.add_response(testing::MockResponse::Message(
        bincode::serialize(&TestMessage("loop-1".into())).expect("serialize loop response 1"),
    ));
    handler.add_response(testing::MockResponse::Message(
        bincode::serialize(&TestMessage("loop-2".into())).expect("serialize loop response 2"),
    ));

    let mut endpoint = ();
    let result = interpret(&mut handler, &mut endpoint, program)
        .await
        .expect("interpret loop program");

    assert_eq!(result.final_state, InterpreterState::Completed);
    assert_eq!(
        result.received_values.len(),
        2,
        "loop execution must report exactly one value per receive"
    );
}

#[tokio::test]
async fn test_timeout_body_does_not_duplicate_received_values() {
    let timed_body = Program::<TestRole, TestMessage>::new()
        .recv::<TestMessage>(TestRole::Bob)
        .end();
    let program = Program::<TestRole, TestMessage>::new()
        .with_timeout(TestRole::Alice, Duration::from_secs(1), timed_body)
        .end();

    let mut handler = testing::MockHandler::new(TestRole::Alice);
    handler.add_response(testing::MockResponse::Message(
        bincode::serialize(&TestMessage("timed-reply".into()))
            .expect("serialize timeout body response"),
    ));

    let mut endpoint = ();
    let result = interpret(&mut handler, &mut endpoint, program)
        .await
        .expect("interpret timeout program");

    assert_eq!(result.final_state, InterpreterState::Completed);
    assert_eq!(
        result.received_values.len(),
        1,
        "timeout body execution must not duplicate received values"
    );
}

#[tokio::test]
async fn test_parallel_uses_deterministic_declaration_order() {
    let first = Program::<TestRole, TestMessage>::new()
        .send(TestRole::Bob, TestMessage("first".into()))
        .end();
    let second = Program::<TestRole, TestMessage>::new()
        .recv::<TestMessage>(TestRole::Bob)
        .end();
    let program = Program::<TestRole, TestMessage>::new()
        .parallel(vec![first, second])
        .end();

    let mut handler = testing::MockHandler::new(TestRole::Alice);
    handler.add_response(testing::MockResponse::Message(
        bincode::serialize(&TestMessage("parallel-reply".into()))
            .expect("serialize parallel response"),
    ));

    let mut endpoint = ();
    let result = interpret(&mut handler, &mut endpoint, program)
        .await
        .expect("interpret parallel program");

    assert_eq!(result.final_state, InterpreterState::Completed);
    assert_eq!(result.received_values.len(), 1);
    assert_eq!(
        handler.operations(),
        &[
            testing::MockOperation::Send {
                to: TestRole::Bob,
                msg_type: std::any::type_name::<TestMessage>().to_string()
            },
            testing::MockOperation::Recv {
                from: TestRole::Bob
            }
        ]
    );
}

#[tokio::test]
async fn test_parallel_fails_fast_on_first_error() {
    let first = Program::<TestRole, TestMessage>::new()
        .recv::<TestMessage>(TestRole::Bob)
        .end();
    let second = Program::<TestRole, TestMessage>::new()
        .send(TestRole::Bob, TestMessage("never-sent".into()))
        .end();
    let program = Program::<TestRole, TestMessage>::new()
        .parallel(vec![first, second])
        .end();

    let mut handler = testing::MockHandler::new(TestRole::Alice);
    let mut endpoint = ();
    let result = interpret(&mut handler, &mut endpoint, program)
        .await
        .expect("interpret parallel error program");

    assert!(
        matches!(result.final_state, InterpreterState::Failed(_)),
        "parallel must stop on first failing branch"
    );
    assert_eq!(
        handler.operations(),
        &[testing::MockOperation::Recv {
            from: TestRole::Bob
        }],
        "later branches must not execute after an earlier failure"
    );
}
