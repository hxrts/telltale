use super::*;
use async_recursion::async_recursion;
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

async fn interpret_reference(
    handler: &mut testing::MockHandler<TestRole>,
    endpoint: &mut (),
    program: Program<TestRole, TestMessage>,
) -> ChoreoResult<InterpretResult<TestMessage>> {
    #[async_recursion]
    async fn run_program(
        handler: &mut testing::MockHandler<TestRole>,
        endpoint: &mut (),
        program: Program<TestRole, TestMessage>,
        received_values: &mut Vec<TestMessage>,
        last_label: &mut Option<TestLabel>,
    ) -> ChoreoResult<()> {
        for effect in program.into_effects() {
            match effect {
                Effect::Send { to, msg } => handler.send(endpoint, to, &msg).await?,
                Effect::Recv { from, .. } => {
                    let value = handler.recv(endpoint, from).await?;
                    received_values.push(value);
                }
                Effect::Choose { at, label } => {
                    handler.choose(endpoint, at, label).await?;
                    *last_label = Some(label);
                }
                Effect::Offer { from } => {
                    *last_label = Some(handler.offer(endpoint, from).await?);
                }
                Effect::Branch { branches, .. } => {
                    let label = (*last_label).ok_or_else(|| {
                        ChoreographyError::ProtocolViolation(
                            "Branch effect requires a preceding Choose or Offer effect"
                                .to_string(),
                        )
                    })?;
                    let (_, selected) = branches
                        .iter()
                        .find(|(branch_label, _)| branch_label == &label)
                        .ok_or_else(|| {
                            ChoreographyError::ProtocolViolation(format!(
                                "No branch found for label {label:?}"
                            ))
                        })?;
                    run_program(
                        handler,
                        endpoint,
                        selected.clone(),
                        received_values,
                        last_label,
                    )
                    .await?;
                    *last_label = None;
                }
                Effect::Loop { iterations, body } => {
                    for _ in 0..iterations.unwrap_or(1) {
                        run_program(
                            handler,
                            endpoint,
                            (*body).clone(),
                            received_values,
                            last_label,
                        )
                        .await?;
                    }
                }
                Effect::Timeout {
                    dur,
                    body,
                    on_timeout,
                    ..
                } => {
                    #[cfg(not(target_arch = "wasm32"))]
                    let timeout_result =
                        tokio::time::timeout(dur, run_program(
                            handler,
                            endpoint,
                            *body,
                            received_values,
                            last_label,
                        ))
                        .await;

                    #[cfg(target_arch = "wasm32")]
                    let timeout_result = {
                        use futures::future::{select, Either};
                        use futures::pin_mut;
                        use wasm_timer::Delay;

                        let body_future =
                            run_program(handler, endpoint, *body, received_values, last_label);
                        let timeout = Delay::new(dur);
                        pin_mut!(body_future);
                        pin_mut!(timeout);

                        match select(body_future, timeout).await {
                            Either::Left((result, _)) => Ok(result),
                            Either::Right(_) => Err(()),
                        }
                    };

                    match timeout_result {
                        Ok(result) => result?,
                        Err(_) => {
                            if let Some(timeout_body) = on_timeout {
                                run_program(
                                    handler,
                                    endpoint,
                                    *timeout_body,
                                    received_values,
                                    last_label,
                                )
                                .await?;
                            } else {
                                return Err(ChoreographyError::Timeout(dur));
                            }
                        }
                    }
                }
                Effect::Parallel { programs } => {
                    for nested in programs {
                        run_program(handler, endpoint, nested, received_values, last_label)
                            .await?;
                    }
                }
                Effect::Extension(_) => {}
                Effect::End => {}
            }
        }

        Ok(())
    }

    let mut received_values = Vec::new();
    let mut last_label = None;
    let start_len = received_values.len();
    let final_state = match run_program(handler, endpoint, program, &mut received_values, &mut last_label).await {
        Ok(()) => InterpreterState::Completed,
        Err(ChoreographyError::Timeout(_)) => InterpreterState::Timeout,
        Err(err) => InterpreterState::Failed(err.to_string()),
    };

    Ok(InterpretResult {
        received_values: received_values[start_len..].to_vec(),
        final_state,
    })
}

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

#[tokio::test]
async fn test_stack_interpreter_matches_reference_recursive_execution() {
    let nested_branch = Program::<TestRole, TestMessage>::new()
        .recv::<TestMessage>(TestRole::Bob)
        .parallel(vec![
            Program::new()
                .send(TestRole::Bob, TestMessage("parallel-a".into()))
                .end(),
            Program::new()
                .send(TestRole::Alice, TestMessage("parallel-b".into()))
                .end(),
        ])
        .end();
    let loop_body = Program::<TestRole, TestMessage>::new()
        .choose(TestRole::Alice, TestLabel::Continue)
        .branch(TestRole::Alice, vec![(TestLabel::Continue, nested_branch)])
        .end();
    let program = Program::<TestRole, TestMessage>::new()
        .loop_n(2, loop_body)
        .with_timeout(
            TestRole::Alice,
            Duration::from_secs(1),
            Program::new()
                .recv::<TestMessage>(TestRole::Bob)
                .send(TestRole::Bob, TestMessage("tail".into()))
                .end(),
        )
        .end();

    let scripted_messages = vec![
        TestMessage("branch-0".into()),
        TestMessage("branch-1".into()),
        TestMessage("timeout-body".into()),
    ];

    let mut stack_handler = testing::MockHandler::new(TestRole::Alice);
    let mut reference_handler = testing::MockHandler::new(TestRole::Alice);
    for message in &scripted_messages {
        let bytes = bincode::serialize(message).expect("serialize scripted message");
        stack_handler.add_response(testing::MockResponse::Message(bytes.clone()));
        reference_handler.add_response(testing::MockResponse::Message(bytes));
    }

    let mut stack_endpoint = ();
    let mut reference_endpoint = ();
    let stack_result = interpret(&mut stack_handler, &mut stack_endpoint, program.clone())
        .await
        .expect("stack interpreter");
    let reference_result =
        interpret_reference(&mut reference_handler, &mut reference_endpoint, program)
            .await
            .expect("reference interpreter");

    assert_eq!(stack_result.final_state, reference_result.final_state);
    assert_eq!(stack_result.received_values, reference_result.received_values);
    assert_eq!(stack_handler.operations(), reference_handler.operations());
}
