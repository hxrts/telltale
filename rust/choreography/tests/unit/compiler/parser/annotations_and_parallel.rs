use super::*;
use crate::ast::Protocol;
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
  par
    | A -> B : Msg1
    | C -> D : Msg2
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
  par
    | A -> B : Msg
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_timed_choice() {
        let input = r#"
protocol TimedRequest =
  roles Alice, Bob
  Alice -> Bob : Request
  timed_choice at Alice(5s) {
    | OnTime -> {
      Bob -> Alice : Response
    }
    | TimedOut -> {
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
    | Fast -> {
      Server -> Client : Data
    }
    | Slow -> {
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
    | Done -> {
      B -> A : Complete
    }
    | Expired -> {
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
  Client { runtime_timeout = 5s } -> Server : Request
  Server -> Client : Response
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse sender-record runtime_timeout: {:?}",
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
    fn test_parse_multiline_runtime_timeout_annotation_with_closing_paren_on_own_line() {
        let input = r#"
protocol TimedRequest =
  roles Client, Server
  Client {
    runtime_timeout = 5s,
  }
    -> Server : Request
  Server -> Client : Response
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse multiline sender-record runtime_timeout: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Send { annotations, .. } => {
                assert!(annotations.has_runtime_timeout());
                assert_eq!(
                    annotations.runtime_timeout(),
                    Some(std::time::Duration::from_secs(5))
                );
            }
            _ => panic!("Expected Send for Request"),
        }
    }

    #[test]
    fn test_parse_runtime_timeout_milliseconds() {
        let input = r#"
protocol QuickCheck =
  roles A, B
  A { runtime_timeout = 100ms } -> B : Ping
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse sender-record runtime_timeout with ms: {:?}",
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
  Coordinator { parallel = true } -> Worker : Task
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse sender-record parallel metadata: {:?}",
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
    fn test_parse_choice_with_bar_prefixed_branches() {
        let input = r#"
protocol Decision =
  roles A, B
  choice at A
    | Accept ->
        A -> B : Ok
    | Reject ->
        A -> B : No
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse choice with bar-prefixed branches: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Choice { branches, .. } => {
                assert_eq!(branches.len(), 2);
                assert_eq!(branches.first().label.to_string(), "Accept");
                assert_eq!(branches.as_slice()[1].label.to_string(), "Reject");
            }
            _ => panic!("Expected Choice"),
        }
    }

    #[test]
    fn test_parse_par_with_single_line_bar_branches() {
        let input = r#"
protocol ParallelBars =
  roles A, B, C, D
  par
    | A -> B : Left
    | C -> D : Right
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse `par` with single-line branches: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Parallel { protocols } => {
                assert_eq!(protocols.len(), 2);
            }
            _ => panic!("Expected Parallel"),
        }
    }

    #[test]
    fn test_parse_par_with_block_branch() {
        let input = r#"
protocol ParallelBarsBlock =
  roles A, B, C, D
  par
    |
      A -> B : Left
      B -> A : Ack
    | C -> D : Right
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse `par` with block branch: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Parallel { protocols } => {
                assert_eq!(protocols.len(), 2);
                match &protocols.first() {
                    Protocol::Send { continuation, .. } => {
                        assert!(matches!(continuation.as_ref(), Protocol::Send { .. }));
                    }
                    _ => panic!("Expected first branch to be a send sequence"),
                }
            }
            _ => panic!("Expected Parallel"),
        }
    }

    #[test]
    fn test_reject_par_without_bar_branches() {
        let input = r#"
protocol ParallelMissingBars =
  roles A, B, C, D
  par
    A -> B : Left
    C -> D : Right
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_err(),
            "`par` branches must be introduced with `|`"
        );
    }

    #[test]
    fn test_parse_sender_role_annotation_block() {
        let input = r#"
protocol RoleAnnotatedSend =
  roles Role, OtherRole
  Role {
    annotation1 = "value",
    annotation2 = 100,
    annotation3 = another,
  } -> OtherRole : Message of crate.Type
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse sender role annotation block: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Send {
                from,
                to,
                message,
                from_annotations,
                ..
            } => {
                assert_eq!(from.name().to_string(), "Role");
                assert_eq!(to.name().to_string(), "OtherRole");
                assert_eq!(message.name.to_string(), "Message");
                assert_eq!(
                    message.payload.as_ref().map(ToString::to_string),
                    Some("crate :: Type".to_string())
                );
                assert_eq!(
                    from_annotations.get("annotation1"),
                    Some("value".to_string())
                );
                assert_eq!(from_annotations.get("annotation2"), Some("100".to_string()));
                assert_eq!(
                    from_annotations.get("annotation3"),
                    Some("another".to_string())
                );
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_parse_sender_record_with_aligned_arrow_layout() {
        let input = r#"
protocol StyledSend =
  roles Buyer, Seller
  Buyer { priority = high }
    -> Seller : Request of shop.Order
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse aligned-arrow sender record syntax: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Send {
                from_annotations,
                message,
                ..
            } => {
                assert_eq!(from_annotations.get("priority"), Some("high".to_string()));
                assert_eq!(
                    message.payload.as_ref().map(ToString::to_string),
                    Some("shop :: Order".to_string())
                );
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_parse_sender_role_annotation_block_with_indexed_role() {
        let input = r#"
protocol RoleAnnotatedIndexedSend =
  roles Worker[N], Coordinator
  Worker[0] {
    shard = 0,
  } -> Coordinator : Result
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse sender annotation block on indexed role: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Send {
                from,
                from_annotations,
                ..
            } => {
                assert_eq!(from.name().to_string(), "Worker");
                assert_eq!(
                    from.index().as_ref().map(ToString::to_string),
                    Some("0".to_string())
                );
                assert_eq!(from_annotations.get("shard"), Some("0".to_string()));
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_parse_sender_role_annotation_block_on_broadcast() {
        let input = r#"
protocol RoleAnnotatedBroadcast =
  roles Coordinator, Worker
  Coordinator {
    batch_size = 100,
  } ->* : Task
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse sender annotation block on broadcast: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Broadcast {
                from,
                from_annotations,
                ..
            } => {
                assert_eq!(from.name().to_string(), "Coordinator");
                assert_eq!(
                    from_annotations.get("batch_size"),
                    Some("100".to_string())
                );
            }
            _ => panic!("Expected Broadcast"),
        }
    }

    #[test]
    fn test_reject_sender_metadata_in_square_brackets() {
        let input = r#"
protocol InvalidRoleMetadata =
  roles Role, OtherRole
  Role[annotation1 = "value"] -> OtherRole : Message
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_err(),
            "square brackets must stay reserved for role indexing"
        );
    }

    #[test]
    fn test_reject_sender_metadata_at_brackets_syntax() {
        let input = r#"
protocol LegacyRoleAnnotatedSend =
  roles Role, OtherRole
  Role @[
    annotation1 = "value",
  ] -> OtherRole : Message
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_err(), "`@[ ... ]` sender metadata must be rejected");
    }

    #[test]
    fn test_reject_mixed_sender_metadata_and_of_payload_legacy_syntax() {
        let input = r#"
protocol LegacyAndNew =
  roles Role, OtherRole
  Role @[ priority = high ] -> OtherRole : Message of shop.Order
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_err(), "mixed legacy sender metadata must be rejected");
    }

    #[test]
    fn test_parse_ordered_annotation() {
        let input = r#"
protocol OrderedCollect =
  roles Coordinator, Worker
  Worker { ordered = true } -> Coordinator : Result
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse sender-record ordered metadata: {:?}",
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
