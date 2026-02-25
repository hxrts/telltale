use super::*;
use crate::effects::{LabelId, RoleId};
use crate::identifiers::RoleName;

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
