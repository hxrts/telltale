use super::*;
use crate::ast::{Condition, LocalType, Protocol, ValidationError};

#[test]
fn test_parse_simple_send() {
    let input = r#"
protocol SimpleSend =
  roles Alice, Bob
  Alice -> Bob : Hello
"#;

    let result = parse_choreography_str(input);
    assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

    let choreo = result.unwrap();
    assert_eq!(choreo.name.to_string(), "SimpleSend");
    assert_eq!(choreo.roles.len(), 2);
}

#[test]
fn test_parse_with_choice() {
    let input = r#"
protocol Negotiation =
  roles Buyer, Seller
  Buyer -> Seller : Offer
  case choose Seller of
accept ->
  Seller -> Buyer : Accept
reject ->
  Seller -> Buyer : Reject
"#;

    let result = parse_choreography_str(input);
    assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

    let choreo = result.unwrap();
    assert_eq!(choreo.name.to_string(), "Negotiation");
}

#[test]
fn test_parse_choice_alias() {
    let input = r#"
protocol AliasChoice =
  roles A, B
  choice at A
ok ->
  A -> B : Ack
fail ->
  A -> B : Nack
"#;

    let result = parse_choreography_str(input);
    assert!(
        result.is_ok(),
        "Failed to parse alias choice: {:?}",
        result.err()
    );
}

#[test]
fn test_parse_undefined_role() {
    let input = r#"
protocol Invalid =
  roles Alice
  Alice -> Bob : Hello
"#;

    let result = parse_choreography_str(input);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(matches!(err, ParseError::UndefinedRole { .. }));

    // Verify error message includes span information
    let err_str = err.to_string();
    assert!(err_str.contains("Undefined role"));
    assert!(err_str.contains("Bob"));
}

#[test]
fn test_parse_duplicate_role() {
    let input = r#"
protocol DuplicateRole =
  roles Alice, Bob, Alice
  Alice -> Bob : Hello
"#;

    let result = parse_choreography_str(input);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(matches!(err, ParseError::DuplicateRole { .. }));

    // Verify error message includes span information
    let err_str = err.to_string();
    assert!(err_str.contains("Duplicate role"));
    assert!(err_str.contains("Alice"));
}

#[test]
fn test_parse_loop_repeat() {
    let input = r#"
protocol LoopProtocol =
  roles Client, Server
  loop repeat 3
Client -> Server : Request
Server -> Client : Response
"#;

    let result = parse_choreography_str(input);
    assert!(result.is_ok(), "Failed to parse: {:?}", result.err());
}

#[test]
fn test_parse_loop_decide() {
    let input = r#"
protocol DecideLoop =
  roles Client, Server
  loop decide by Client
Client -> Server : Ping
Server -> Client : Pong
"#;

    let result = parse_choreography_str(input);
    assert!(
        result.is_ok(),
        "Failed to parse decide loop: {:?}",
        result.err()
    );
}

#[test]
fn test_role_decides_desugaring() {
    // RoleDecides loops should be desugared to choice+rec pattern (Option B: fused)
    // loop decide by Client { Client -> Server: Ping; ... }
    // becomes:
    //   rec RoleDecidesLoop {
    //       choice at Client {
    //           Ping { Client -> Server: Ping; ...; continue }
    //           Done { Client -> Server: Done }
    //       }
    //   }
    let input = r#"
protocol DecideLoop =
  roles Client, Server
  loop decide by Client
Client -> Server : Ping
Server -> Client : Pong
"#;

    let result = parse_choreography_str(input);
    assert!(
        result.is_ok(),
        "Failed to parse decide loop: {:?}",
        result.err()
    );

    let choreo = result.unwrap();
    match &choreo.protocol {
        Protocol::Rec { label, body } => {
            assert_eq!(label.to_string(), "RoleDecidesLoop");
            match body.as_ref() {
                Protocol::Choice { role, branches, .. } => {
                    assert_eq!(role.name().to_string(), "Client");
                    assert_eq!(branches.len(), 2);

                    // First branch should be the continue branch (using first message label)
                    let continue_branch = branches.first();
                    assert_eq!(continue_branch.label.to_string(), "Ping");

                    // Inside the continue branch, we should have the Send
                    match &continue_branch.protocol {
                        Protocol::Send {
                            from,
                            to,
                            message,
                            continuation,
                            ..
                        } => {
                            assert_eq!(from.name().to_string(), "Client");
                            assert_eq!(to.name().to_string(), "Server");
                            assert_eq!(message.name.to_string(), "Ping");

                            // Continuation should be the response followed by Var (continue)
                            match continuation.as_ref() {
                                Protocol::Send {
                                    from,
                                    to,
                                    message,
                                    continuation,
                                    ..
                                } => {
                                    assert_eq!(from.name().to_string(), "Server");
                                    assert_eq!(to.name().to_string(), "Client");
                                    assert_eq!(message.name.to_string(), "Pong");

                                    // Should end with Var (continue RoleDecidesLoop)
                                    match continuation.as_ref() {
                                        Protocol::Var(label) => {
                                            assert_eq!(label.to_string(), "RoleDecidesLoop");
                                        }
                                        _ => panic!(
                                            "Expected Var for continue, got {:?}",
                                            continuation
                                        ),
                                    }
                                }
                                _ => panic!("Expected Send for Pong, got {:?}", continuation),
                            }
                        }
                        _ => {
                            panic!("Expected Send for Ping, got {:?}", continue_branch.protocol)
                        }
                    }

                    // Second branch should be Done
                    let done_branch = &branches.as_slice()[1];
                    assert_eq!(done_branch.label.to_string(), "Done");
                    match &done_branch.protocol {
                        Protocol::Send {
                            from,
                            to,
                            message,
                            continuation,
                            ..
                        } => {
                            assert_eq!(from.name().to_string(), "Client");
                            assert_eq!(to.name().to_string(), "Server");
                            assert_eq!(message.name.to_string(), "Done");
                            assert!(matches!(continuation.as_ref(), Protocol::End));
                        }
                        _ => panic!("Expected Send for Done, got {:?}", done_branch.protocol),
                    }
                }
                _ => panic!("Expected Choice inside Rec, got {:?}", body),
            }
        }
        _ => panic!("Expected Rec at top level, got {:?}", choreo.protocol),
    }
}

#[test]
fn test_role_decides_wrong_first_sender_no_desugar() {
    // When the first statement is a Send but NOT from the deciding role,
    // the loop should NOT be desugared and should remain as Protocol::Loop
    let input = r#"
protocol WrongSender =
  roles Client, Server
  loop decide by Client
Server -> Client : Response
Client -> Server : Ack
"#;

    let result = parse_choreography_str(input);
    assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

    let choreo = result.unwrap();
    // Should remain as Loop, not desugared to Rec
    match &choreo.protocol {
        Protocol::Loop { condition, .. } => match condition {
            Some(Condition::RoleDecides(role)) => {
                assert_eq!(role.name().to_string(), "Client");
            }
            _ => panic!("Expected RoleDecides condition"),
        },
        _ => panic!(
            "Expected Loop (not desugared) when first sender doesn't match deciding role"
        ),
    }
}

#[test]
fn test_role_decides_single_message() {
    // Minimal case: loop with just one message
    let input = r#"
protocol SingleMessage =
  roles A, B
  loop decide by A
A -> B : Msg
"#;

    let result = parse_choreography_str(input);
    assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

    let choreo = result.unwrap();
    match &choreo.protocol {
        Protocol::Rec { label, body } => {
            assert_eq!(label.to_string(), "RoleDecidesLoop");
            match body.as_ref() {
                Protocol::Choice { role, branches, .. } => {
                    assert_eq!(role.name().to_string(), "A");
                    assert_eq!(branches.len(), 2);

                    // Continue branch
                    let continue_branch = branches.first();
                    assert_eq!(continue_branch.label.to_string(), "Msg");
                    match &continue_branch.protocol {
                        Protocol::Send {
                            message,
                            continuation,
                            ..
                        } => {
                            assert_eq!(message.name.to_string(), "Msg");
                            // Should directly continue (no more statements)
                            assert!(matches!(continuation.as_ref(), Protocol::Var(_)));
                        }
                        _ => panic!("Expected Send"),
                    }

                    // Done branch
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
fn test_role_decides_three_roles() {
    // Test with three roles where deciding role sends to one, then another responds
    let input = r#"
protocol ThreeRoles =
  roles Client, Server, Logger
  loop decide by Client
Client -> Server : Request
Server -> Logger : Log
Logger -> Client : Ack
"#;

    let result = parse_choreography_str(input);
    assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

    let choreo = result.unwrap();
    match &choreo.protocol {
        Protocol::Rec { body, .. } => {
            match body.as_ref() {
                Protocol::Choice { role, branches, .. } => {
                    assert_eq!(role.name().to_string(), "Client");

                    let continue_branch = branches.first();
                    assert_eq!(continue_branch.label.to_string(), "Request");

                    // Verify the chain: Request -> Log -> Ack -> continue
                    match &continue_branch.protocol {
                        Protocol::Send {
                            from,
                            to,
                            message,
                            continuation,
                            ..
                        } => {
                            assert_eq!(from.name().to_string(), "Client");
                            assert_eq!(to.name().to_string(), "Server");
                            assert_eq!(message.name.to_string(), "Request");

                            match continuation.as_ref() {
                                Protocol::Send {
                                    from,
                                    to,
                                    message,
                                    continuation,
                                    ..
                                } => {
                                    assert_eq!(from.name().to_string(), "Server");
                                    assert_eq!(to.name().to_string(), "Logger");
                                    assert_eq!(message.name.to_string(), "Log");

                                    match continuation.as_ref() {
                                        Protocol::Send {
                                            from,
                                            to,
                                            message,
                                            continuation,
                                            ..
                                        } => {
                                            assert_eq!(from.name().to_string(), "Logger");
                                            assert_eq!(to.name().to_string(), "Client");
                                            assert_eq!(message.name.to_string(), "Ack");
                                            assert!(matches!(
                                                continuation.as_ref(),
                                                Protocol::Var(_)
                                            ));
                                        }
                                        _ => panic!("Expected Send for Ack"),
                                    }
                                }
                                _ => panic!("Expected Send for Log"),
                            }
                        }
                        _ => panic!("Expected Send for Request"),
                    }

                    // Done branch sends to Server (same as first message target)
                    let done_branch = &branches.as_slice()[1];
                    match &done_branch.protocol {
                        Protocol::Send { from, to, .. } => {
                            assert_eq!(from.name().to_string(), "Client");
                            assert_eq!(to.name().to_string(), "Server");
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
fn test_role_decides_with_type_annotation() {
    // Test that type annotations are preserved through desugaring
    let input = r#"
protocol TypedLoop =
  roles Client, Server
  loop decide by Client
Client -> Server : Request<String>
Server -> Client : Response<u32>
"#;

    let result = parse_choreography_str(input);
    assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

    let choreo = result.unwrap();
    match &choreo.protocol {
        Protocol::Rec { body, .. } => {
            match body.as_ref() {
                Protocol::Choice { branches, .. } => {
                    let continue_branch = branches.first();
                    match &continue_branch.protocol {
                        Protocol::Send {
                            message,
                            continuation,
                            ..
                        } => {
                            assert_eq!(message.name.to_string(), "Request");
                            // Type annotation should be preserved
                            assert!(message.type_annotation.is_some());
                            let type_str =
                                message.type_annotation.as_ref().unwrap().to_string();
                            assert!(
                                type_str.contains("String"),
                                "Expected String type, got: {}",
                                type_str
                            );

                            match continuation.as_ref() {
                                Protocol::Send { message, .. } => {
                                    assert_eq!(message.name.to_string(), "Response");
                                    assert!(message.type_annotation.is_some());
                                    let type_str =
                                        message.type_annotation.as_ref().unwrap().to_string();
                                    assert!(
                                        type_str.contains("u32"),
                                        "Expected u32 type, got: {}",
                                        type_str
                                    );
                                }
                                _ => panic!("Expected Send for Response"),
                            }
                        }
                        _ => panic!("Expected Send for Request"),
                    }
                }
                _ => panic!("Expected Choice"),
            }
        }
        _ => panic!("Expected Rec"),
    }
}

#[test]
fn test_role_decides_first_stmt_is_choice_no_desugar() {
    // When the first statement is NOT a Send (e.g., it's a choice),
    // the loop should NOT be desugared
    let input = r#"
protocol FirstIsChoice =
  roles A, B
  loop decide by A
choice at A
  opt1 ->
    A -> B : Msg1
  opt2 ->
    A -> B : Msg2
"#;

    let result = parse_choreography_str(input);
    assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

    let choreo = result.unwrap();
    // Should remain as Loop, not desugared
    match &choreo.protocol {
        Protocol::Loop { condition, body } => {
            match condition {
                Some(Condition::RoleDecides(role)) => {
                    assert_eq!(role.name().to_string(), "A");
                }
                _ => panic!("Expected RoleDecides condition"),
            }
            // Body should be a Choice
            match body.as_ref() {
                Protocol::Choice { .. } => {}
                _ => panic!("Expected Choice in body"),
            }
        }
        _ => panic!("Expected Loop (not desugared) when first statement is not a Send"),
    }
}

#[test]
fn test_role_decides_followed_by_statements() {
    // Test that statements after the loop are preserved
    let input = r#"
protocol LoopThenMore =
  roles A, B
  loop decide by A
A -> B : Request
B -> A : Response
  A -> B : Goodbye
"#;

    let result = parse_choreography_str(input);
    assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

    let choreo = result.unwrap();
    // The loop should be desugared, followed by the Goodbye send
    match &choreo.protocol {
        Protocol::Rec { body, .. } => {
            match body.as_ref() {
                Protocol::Choice { branches, .. } => {
                    // Done branch should continue to the Goodbye message
                    let done_branch = &branches.as_slice()[1];
                    match &done_branch.protocol {
                        Protocol::Send {
                            message,
                            continuation,
                            ..
                        } => {
                            assert_eq!(message.name.to_string(), "Done");
                            // After Done, should be the Goodbye send
                            match continuation.as_ref() {
                                Protocol::Send { message, .. } => {
                                    assert_eq!(message.name.to_string(), "Goodbye");
                                }
                                _ => panic!("Expected Goodbye after Done"),
                            }
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

