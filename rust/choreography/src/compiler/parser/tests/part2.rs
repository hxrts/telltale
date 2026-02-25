use super::*;
use crate::ast::{Condition, LocalType, Protocol, ValidationError};

#[test]
fn test_role_decides_multiple_loops() {
    // Test two consecutive RoleDecides loops
    let input = r#"
protocol TwoLoops =
  roles A, B
  loop decide by A
A -> B : First
  loop decide by B
B -> A : Second
"#;

    let result = parse_choreography_str(input);
    assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

    let choreo = result.unwrap();
    // First loop should be Rec
    match &choreo.protocol {
        Protocol::Rec { label, body } => {
            assert_eq!(label.to_string(), "RoleDecidesLoop");
            match body.as_ref() {
                Protocol::Choice { role, branches, .. } => {
                    assert_eq!(role.name().to_string(), "A");

                    // Done branch should lead to second loop
                    let done_branch = &branches.as_slice()[1];
                    match &done_branch.protocol {
                        Protocol::Send { continuation, .. } => {
                            // After first loop's Done, should be second Rec
                            match continuation.as_ref() {
                                Protocol::Rec { body, .. } => match body.as_ref() {
                                    Protocol::Choice { role, .. } => {
                                        assert_eq!(role.name().to_string(), "B");
                                    }
                                    _ => panic!("Expected Choice in second loop"),
                                },
                                _ => panic!("Expected second Rec after first loop"),
                            }
                        }
                        _ => panic!("Expected Send in Done branch"),
                    }
                }
                _ => panic!("Expected Choice in first loop"),
            }
        }
        _ => panic!("Expected Rec"),
    }
}

#[test]
fn test_role_decides_empty_body_edge_case() {
    // Edge case: empty loop body (should parse but not desugar - no first statement)
    // Note: This tests the parser's robustness, not valid protocol design
    let input = r#"
protocol EmptyBody =
  roles A, B
  loop decide by A
  A -> B : AfterLoop
"#;

    // This might fail to parse or produce a Loop with empty body
    // Either way, we should handle it gracefully
    let result = parse_choreography_str(input);
    // Just verify it doesn't panic - the exact behavior depends on grammar
    if let Ok(choreo) = result {
        // If parsed, should not be desugared (no first Send)
        match &choreo.protocol {
            Protocol::Loop { .. } => {
                // Expected: Loop not desugared due to empty/invalid body
            }
            Protocol::Send { .. } => {
                // Also acceptable: empty loop might be elided
            }
            _ => {
                // Any other result is acceptable for this edge case
            }
        }
    }
    // Parsing failure is also acceptable for this malformed input
}

#[test]
fn test_role_decides_preserves_branch_label_from_message() {
    // Verify that the branch label matches the first message name exactly
    let input = r#"
protocol CustomMessageName =
  roles Producer, Consumer
  loop decide by Producer
Producer -> Consumer : DataChunk
Consumer -> Producer : Ack
"#;

    let result = parse_choreography_str(input);
    assert!(result.is_ok());

    let choreo = result.unwrap();
    match &choreo.protocol {
        Protocol::Rec { body, .. } => {
            match body.as_ref() {
                Protocol::Choice { branches, .. } => {
                    // First branch label should be "DataChunk" (the message name)
                    let continue_branch = branches.first();
                    assert_eq!(continue_branch.label.to_string(), "DataChunk");

                    // Second branch label should be "Done"
                    let done_branch = &branches.as_slice()[1];
                    assert_eq!(done_branch.label.to_string(), "Done");
                }
                _ => panic!("Expected Choice"),
            }
        }
        _ => panic!("Expected Rec"),
    }
}

#[test]
fn test_role_decides_done_message_targets_same_receiver() {
    // The Done message should go to the same receiver as the first message
    let input = r#"
protocol TargetConsistency =
  roles Sender, Receiver, Observer
  loop decide by Sender
Sender -> Receiver : Data
Receiver -> Observer : Forward
"#;

    let result = parse_choreography_str(input);
    assert!(result.is_ok());

    let choreo = result.unwrap();
    match &choreo.protocol {
        Protocol::Rec { body, .. } => {
            match body.as_ref() {
                Protocol::Choice { branches, .. } => {
                    // Continue branch sends to Receiver
                    let continue_branch = branches.first();
                    match &continue_branch.protocol {
                        Protocol::Send { to, .. } => {
                            assert_eq!(to.name().to_string(), "Receiver");
                        }
                        _ => panic!("Expected Send"),
                    }

                    // Done branch should also send to Receiver (same target)
                    let done_branch = &branches.as_slice()[1];
                    match &done_branch.protocol {
                        Protocol::Send { from, to, .. } => {
                            assert_eq!(from.name().to_string(), "Sender");
                            assert_eq!(to.name().to_string(), "Receiver");
                        }
                        _ => panic!("Expected Send in Done branch"),
                    }
                }
                _ => panic!("Expected Choice"),
            }
        }
        _ => panic!("Expected Rec"),
    }
}

#[test]
fn test_parse_parallel_branches() {
    let input = r#"
protocol Parallel =
  roles A, B, C, D
  branch
A -> B : Msg1
  branch
C -> D : Msg2
"#;

    let result = parse_choreography_str(input);
    assert!(
        result.is_ok(),
        "Failed to parse parallel: {:?}",
        result.err()
    );

    let choreo = result.unwrap();
    match choreo.protocol {
        Protocol::Parallel { protocols } => {
            assert_eq!(protocols.len(), 2);
        }
        _ => panic!("Expected top-level parallel protocol"),
    }
}

#[test]
fn test_single_branch_is_error() {
    let input = r#"
protocol SingleBranch =
  roles A, B
  branch
A -> B : Msg
"#;

    let result = parse_choreography_str(input);
    assert!(result.is_err());
    let err = result.unwrap_err();
    let err_str = err.to_string();
    assert!(err_str.contains("parallel requires at least two adjacent branch blocks"));
}

#[test]
fn test_parse_timed_choice() {
    let input = r#"
protocol TimedRequest =
  roles Alice, Bob
  Alice -> Bob : Request
  timed_choice at Alice(5s) {
OnTime -> {
  Bob -> Alice : Response
}
TimedOut -> {
  Alice -> Bob : Cancel
}
  }
"#;

    let result = parse_choreography_str(input);
    assert!(
        result.is_ok(),
        "Failed to parse timed_choice: {:?}",
        result.err()
    );

    let choreo = result.unwrap();
    assert_eq!(choreo.name.to_string(), "TimedRequest");

    // Verify timed_choice is desugared to Choice with typed annotation
    match &choreo.protocol {
        Protocol::Send { continuation, .. } => {
            match continuation.as_ref() {
                Protocol::Choice {
                    role,
                    branches,
                    annotations,
                } => {
                    assert_eq!(role.name().to_string(), "Alice");
                    assert_eq!(branches.len(), 2);
                    // Check that timed_choice annotation is present
                    assert!(annotations.has_timed_choice());
                    assert_eq!(
                        annotations.timed_choice(),
                        Some(std::time::Duration::from_secs(5))
                    );
                }
                _ => panic!("Expected Choice after Send"),
            }
        }
        _ => panic!("Expected Send as first protocol"),
    }
}

#[test]
fn test_parse_timed_choice_milliseconds() {
    let input = r#"
protocol QuickTimeout =
  roles Client, Server
  timed_choice at Client(500ms) {
Fast -> {
  Server -> Client : Data
}
Slow -> {
  Client -> Server : Abort
}
  }
"#;

    let result = parse_choreography_str(input);
    assert!(
        result.is_ok(),
        "Failed to parse timed_choice with ms: {:?}",
        result.err()
    );

    let choreo = result.unwrap();
    match &choreo.protocol {
        Protocol::Choice { annotations, .. } => {
            assert!(annotations.has_timed_choice());
            assert_eq!(
                annotations.timed_choice(),
                Some(std::time::Duration::from_millis(500))
            );
        }
        _ => panic!("Expected Choice as first protocol"),
    }
}

#[test]
fn test_parse_timed_choice_minutes() {
    let input = r#"
protocol LongTimeout =
  roles A, B
  timed_choice at A(2m) {
Done -> {
  B -> A : Complete
}
Expired -> {
  A -> B : Timeout
}
  }
"#;

    let result = parse_choreography_str(input);
    assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

    let choreo = result.unwrap();
    match &choreo.protocol {
        Protocol::Choice { annotations, .. } => {
            // 2 minutes = 120000 ms
            assert!(annotations.has_timed_choice());
            assert_eq!(
                annotations.timed_choice(),
                Some(std::time::Duration::from_millis(120000))
            );
        }
        _ => panic!("Expected Choice"),
    }
}

#[test]
fn test_parse_heartbeat() {
    let input = r#"
protocol Liveness =
  roles Alice, Bob
  heartbeat Alice -> Bob every 1s on_missing(3) {
Bob -> Alice : Disconnect
  } body {
Alice -> Bob : Data
  }
"#;

    let result = parse_choreography_str(input);
    assert!(
        result.is_ok(),
        "Failed to parse heartbeat: {:?}",
        result.err()
    );

    let choreo = result.unwrap();
    assert_eq!(choreo.name.to_string(), "Liveness");

    // Heartbeat desugars to: rec HeartbeatLoop { ... }
    match &choreo.protocol {
        Protocol::Rec { label, body } => {
            assert_eq!(label.to_string(), "HeartbeatLoop");

            // Inside: Sender -> Receiver: Heartbeat; choice at Receiver { ... }
            match body.as_ref() {
                Protocol::Send {
                    from,
                    to,
                    message,
                    continuation,
                    ..
                } => {
                    assert_eq!(from.name().to_string(), "Alice");
                    assert_eq!(to.name().to_string(), "Bob");
                    assert_eq!(message.name.to_string(), "Heartbeat");

                    // Continuation is Choice at Receiver
                    match continuation.as_ref() {
                        Protocol::Choice {
                            role,
                            branches,
                            annotations,
                        } => {
                            assert_eq!(role.name().to_string(), "Bob");
                            assert_eq!(branches.len(), 2);
                            assert_eq!(branches[0].label.to_string(), "Alive");
                            assert_eq!(branches[1].label.to_string(), "Dead");

                            // Check heartbeat annotation
                            assert!(annotations.has_heartbeat());
                            let (interval, on_missing) = annotations.heartbeat().unwrap();
                            assert_eq!(interval, std::time::Duration::from_secs(1));
                            assert_eq!(on_missing, 3);
                        }
                        _ => panic!("Expected Choice as continuation"),
                    }
                }
                _ => panic!("Expected Send inside Rec"),
            }
        }
        _ => panic!("Expected Rec as top-level protocol"),
    }
}

#[test]
fn test_parse_heartbeat_milliseconds() {
    let input = r#"
protocol FastHeartbeat =
  roles Client, Server
  heartbeat Client -> Server every 500ms on_missing(5) {
Server -> Client : Dead
  } body {
Client -> Server : Ping
  }
"#;

    let result = parse_choreography_str(input);
    assert!(
        result.is_ok(),
        "Failed to parse heartbeat with ms: {:?}",
        result.err()
    );

    let choreo = result.unwrap();
    match &choreo.protocol {
        Protocol::Rec { body, .. } => match body.as_ref() {
            Protocol::Send { continuation, .. } => match continuation.as_ref() {
                Protocol::Choice { annotations, .. } => {
                    assert!(annotations.has_heartbeat());
                    let (interval, on_missing) = annotations.heartbeat().unwrap();
                    assert_eq!(interval, std::time::Duration::from_millis(500));
                    assert_eq!(on_missing, 5);
                }
                _ => panic!("Expected Choice"),
            },
            _ => panic!("Expected Send"),
        },
        _ => panic!("Expected Rec"),
    }
}

#[test]
fn test_parse_runtime_timeout_annotation() {
    let input = r#"
protocol TimedRequest =
  roles Client, Server
  @runtime_timeout(5s) Client -> Server : Request
  Server -> Client : Response
"#;

    let result = parse_choreography_str(input);
    assert!(
        result.is_ok(),
        "Failed to parse @runtime_timeout: {:?}",
        result.err()
    );

    let choreo = result.unwrap();
    match &choreo.protocol {
        Protocol::Send {
            annotations,
            continuation,
            ..
        } => {
            // Check the runtime_timeout annotation was parsed
            assert!(annotations.has_runtime_timeout());
            let timeout = annotations.runtime_timeout().unwrap();
            assert_eq!(timeout, std::time::Duration::from_secs(5));

            // Check continuation doesn't have the annotation
            match continuation.as_ref() {
                Protocol::Send { annotations, .. } => {
                    assert!(!annotations.has_runtime_timeout());
                }
                _ => panic!("Expected Send for Response"),
            }
        }
        _ => panic!("Expected Send for Request"),
    }
}

#[test]
fn test_parse_runtime_timeout_milliseconds() {
    let input = r#"
protocol QuickCheck =
  roles A, B
  @runtime_timeout(100ms) A -> B : Ping
"#;

    let result = parse_choreography_str(input);
    assert!(
        result.is_ok(),
        "Failed to parse @runtime_timeout with ms: {:?}",
        result.err()
    );

    let choreo = result.unwrap();
    match &choreo.protocol {
        Protocol::Send { annotations, .. } => {
            assert!(annotations.has_runtime_timeout());
            let timeout = annotations.runtime_timeout().unwrap();
            assert_eq!(timeout, std::time::Duration::from_millis(100));
        }
        _ => panic!("Expected Send"),
    }
}

#[test]
fn test_parse_parallel_annotation() {
    let input = r#"
protocol Broadcast =
  roles Coordinator, Worker
  @parallel Coordinator -> Worker : Task
"#;

    let result = parse_choreography_str(input);
    assert!(
        result.is_ok(),
        "Failed to parse @parallel: {:?}",
        result.err()
    );

    let choreo = result.unwrap();
    match &choreo.protocol {
        Protocol::Send { annotations, .. } => {
            assert!(annotations.has_parallel(), "Expected parallel annotation");
        }
        _ => panic!("Expected Send"),
    }
}

#[test]
fn test_parse_ordered_annotation() {
    let input = r#"
protocol OrderedCollect =
  roles Coordinator, Worker
  @ordered Worker -> Coordinator : Result
"#;

    let result = parse_choreography_str(input);
    assert!(
        result.is_ok(),
        "Failed to parse @ordered: {:?}",
        result.err()
    );

    let choreo = result.unwrap();
    match &choreo.protocol {
        Protocol::Send { annotations, .. } => {
            assert!(annotations.has_ordered(), "Expected ordered annotation");
        }
        _ => panic!("Expected Send"),
    }
}

#[test]
fn test_parse_min_responses_annotation() {
    let input = r#"
protocol ThresholdSign =
  roles Coordinator, Signer
  @min_responses(3) Signer -> Coordinator : Signature
"#;

    let result = parse_choreography_str(input);
    assert!(
        result.is_ok(),
        "Failed to parse @min_responses: {:?}",
        result.err()
    );

    let choreo = result.unwrap();
    match &choreo.protocol {
        Protocol::Send { annotations, .. } => {
            assert!(
                annotations.has_min_responses(),
                "Expected min_responses annotation"
            );
            assert_eq!(annotations.min_responses(), Some(3));
        }
        _ => panic!("Expected Send"),
    }
}

