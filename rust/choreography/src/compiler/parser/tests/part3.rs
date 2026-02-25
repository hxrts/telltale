use super::*;
use crate::ast::{Condition, LocalType, Protocol, ValidationError};

#[test]
fn test_parse_combined_annotations() {
    let input = r#"
protocol ParallelThreshold =
  roles Coordinator, Worker
  @parallel @min_responses(2) Worker -> Coordinator : Vote
"#;

    let result = parse_choreography_str(input);
    assert!(
        result.is_ok(),
        "Failed to parse combined annotations: {:?}",
        result.err()
    );

    let choreo = result.unwrap();
    match &choreo.protocol {
        Protocol::Send { annotations, .. } => {
            assert!(annotations.has_parallel(), "Expected parallel annotation");
            assert!(
                annotations.has_min_responses(),
                "Expected min_responses annotation"
            );
            assert_eq!(annotations.min_responses(), Some(2));
        }
        _ => panic!("Expected Send"),
    }
}

#[test]
fn test_parse_proof_bundles_and_protocol_requires_metadata() {
    let input = r#"
proof_bundle Base requires [guard_tokens, delegation]
proof_bundle Extra requires [knowledge_flow]
protocol WithBundles requires Base, Extra =
  roles A, B
  A -> B : Ping
"#;

    let choreo = parse_choreography_str(input).expect("parse should succeed");
    let bundles = choreo.proof_bundles();
    assert_eq!(bundles.len(), 2);
    assert_eq!(bundles[0].name, "Base");
    assert_eq!(
        bundles[0].capabilities,
        vec!["guard_tokens".to_string(), "delegation".to_string()]
    );
    assert_eq!(bundles[1].name, "Extra");
    assert_eq!(bundles[1].capabilities, vec!["knowledge_flow".to_string()]);
    assert_eq!(
        choreo.required_proof_bundles(),
        vec!["Base".to_string(), "Extra".to_string()]
    );
}

#[test]
fn test_parse_vm_core_statements_into_extensions() {
    fn collect_vm_ops(protocol: &Protocol, out: &mut Vec<String>) {
        match protocol {
            Protocol::Extension {
                annotations,
                continuation,
                ..
            } => {
                if let Some(op) = annotations.custom("vm_core_op") {
                    out.push(op.to_string());
                }
                collect_vm_ops(continuation, out);
            }
            Protocol::Send { continuation, .. } | Protocol::Broadcast { continuation, .. } => {
                collect_vm_ops(continuation, out);
            }
            Protocol::Choice { branches, .. } => {
                for branch in branches {
                    collect_vm_ops(&branch.protocol, out);
                }
            }
            Protocol::Loop { body, .. } | Protocol::Rec { body, .. } => {
                collect_vm_ops(body, out);
            }
            Protocol::Parallel { protocols } => {
                for protocol in protocols {
                    collect_vm_ops(protocol, out);
                }
            }
            Protocol::Var(_) | Protocol::End => {}
        }
    }

    let input = r#"
protocol VmOps =
  roles A, B
  acquire guard as token
  transfer token to B with bundle Base
  check k for B into out
  A -> B : Ping
"#;

    let choreo = parse_choreography_str(input).expect("parse should succeed");
    let mut vm_ops = Vec::new();
    collect_vm_ops(&choreo.protocol, &mut vm_ops);
    assert_eq!(
        vm_ops,
        vec![
            "acquire".to_string(),
            "transfer".to_string(),
            "check".to_string()
        ]
    );
}

#[test]
fn test_validate_missing_required_bundle_fails() {
    let input = r#"
protocol MissingBundle requires Core =
  roles A, B
  A -> B : Ping
"#;

    let choreo = parse_choreography_str(input).expect("parse should succeed");
    let err = choreo.validate().expect_err("validation should fail");
    assert!(matches!(
        err,
        ValidationError::MissingProofBundle(ref name) if name == "Core"
    ));
}

#[test]
fn test_validate_missing_capability_fails() {
    let input = r#"
proof_bundle DelegationOnly requires [delegation]
protocol NeedGuard requires DelegationOnly =
  roles A, B
  acquire guard as token
  A -> B : Ping
"#;

    let choreo = parse_choreography_str(input).expect("parse should succeed");
    let err = choreo.validate().expect_err("validation should fail");
    assert!(matches!(
        err,
        ValidationError::MissingCapability(ref cap) if cap == "guard_tokens"
    ));
}

#[test]
fn test_validate_duplicate_bundle_fails() {
    let input = r#"
proof_bundle Core requires [delegation]
proof_bundle Core requires [guard_tokens]
protocol DuplicateBundle requires Core =
  roles A, B
  A -> B : Ping
"#;

    let choreo = parse_choreography_str(input).expect("parse should succeed");
    let err = choreo.validate().expect_err("validation should fail");
    assert!(matches!(
        err,
        ValidationError::DuplicateProofBundle(ref name) if name == "Core"
    ));
}

#[test]
fn test_parse_guard_predicate_rejects_non_boolean_expression() {
    let input = r#"
protocol GuardTypeCheck =
  roles A, B
  choice at A
ok when (count + 1) ->
  A -> B : Ack
no ->
  A -> B : Nack
"#;

    let err = parse_choreography_str(input).expect_err("guard should fail");
    assert!(matches!(err, ParseError::Syntax { .. }));
    assert!(err.to_string().contains("boolean-like"));
}

#[test]
fn test_parse_loop_while_rejects_non_boolean_expression() {
    let input = r#"
protocol LoopTypeCheck =
  roles A, B
  loop while "count + 1"
A -> B : Tick
"#;

    let err = parse_choreography_str(input).expect_err("loop condition should fail");
    assert!(matches!(err, ParseError::InvalidCondition { .. }));
    assert!(err.to_string().contains("boolean-like"));
}

#[test]
fn test_projection_preserves_continuation_after_extension() {
    let input = r#"
protocol ExtensionProjection =
  roles A, B
  acquire guard as token
  A -> B : Ping
"#;

    let choreo = parse_choreography_str(input).expect("parse should succeed");
    let role_a = choreo
        .roles
        .iter()
        .find(|r| r.name() == "A")
        .expect("role A should exist");
    let projected =
        crate::compiler::projection::project(&choreo, role_a).expect("projection must work");

    match projected {
        LocalType::Send { to, .. } => assert_eq!(to.name(), "B"),
        other => panic!("expected send continuation projection, got {other:?}"),
    }
}

#[test]
fn test_parse_enriched_proof_bundle_metadata() {
    let input = r#"
proof_bundle Base version "1.0.0" issuer "did:example:issuer" constraint "fresh_nonce" constraint "sig_valid" requires [delegation, guard_tokens]
protocol BundleMeta requires Base =
  roles A, B
  A -> B : Ping
"#;

    let choreo = parse_choreography_str(input).expect("parse should succeed");
    let bundles = choreo.proof_bundles();
    assert_eq!(bundles.len(), 1);
    let bundle = &bundles[0];
    assert_eq!(bundle.name, "Base");
    assert_eq!(bundle.version.as_deref(), Some("1.0.0"));
    assert_eq!(bundle.issuer.as_deref(), Some("did:example:issuer"));
    assert_eq!(
        bundle.constraints,
        vec!["fresh_nonce".to_string(), "sig_valid".to_string()]
    );
    assert_eq!(
        bundle.capabilities,
        vec!["delegation".to_string(), "guard_tokens".to_string()]
    );
}

#[test]
fn test_infer_required_bundles_from_vm_capabilities() {
    let input = r#"
proof_bundle Spec requires [speculation]
protocol Inferred =
  roles A, B
  fork ghost0
  A -> B : Ping
"#;

    let choreo = parse_choreography_str(input).expect("parse should succeed");
    assert_eq!(choreo.required_proof_bundles(), vec!["Spec".to_string()]);
    assert_eq!(
        choreo.inferred_required_proof_bundles(),
        vec!["Spec".to_string()]
    );
    assert!(choreo.validate().is_ok());
}

#[test]
fn test_linear_assets_reject_double_consume() {
    let input = r#"
protocol LinearDoubleConsume =
  roles A, B
  acquire guard as token
  release guard using token
  release guard using token
"#;

    let err = parse_choreography_str(input).expect_err("parse should fail");
    assert!(err.to_string().contains("before acquire"));
}

#[test]
fn test_linear_assets_reject_branch_divergence() {
    let input = r#"
protocol LinearBranchDivergence =
  roles A, B
  acquire guard as token
  choice at A
consume ->
  release guard using token
keep ->
  A -> B : Skip
"#;

    let err = parse_choreography_str(input).expect_err("parse should fail");
    assert!(err.to_string().contains("diverge"));
}

#[test]
fn test_parse_first_class_combinators() {
    fn has_quorum_extension(protocol: &Protocol) -> bool {
        match protocol {
            Protocol::Extension {
                annotations,
                continuation,
                ..
            } => {
                annotations.custom("dsl_combinator") == Some("quorum_collect")
                    || has_quorum_extension(continuation)
            }
            Protocol::Send { continuation, .. } | Protocol::Broadcast { continuation, .. } => {
                has_quorum_extension(continuation)
            }
            Protocol::Choice { branches, .. } => {
                branches.iter().any(|b| has_quorum_extension(&b.protocol))
            }
            Protocol::Loop { body, .. } | Protocol::Rec { body, .. } => {
                has_quorum_extension(body)
            }
            Protocol::Parallel { protocols } => protocols.iter().any(has_quorum_extension),
            Protocol::Var(_) | Protocol::End => false,
        }
    }

    let input = r#"
protocol Combinators =
  roles A, B
  handshake A <-> B : Hello
  quorum_collect A -> B min 2 : Vote
  A -> B : Done
  retry 2 {
A -> B : Ping
  }
"#;

    let choreo = parse_choreography_str(input).expect("parse should succeed");
    match &choreo.protocol {
        Protocol::Send {
            from,
            to,
            message,
            continuation,
            ..
        } => {
            assert_eq!(from.name(), "A");
            assert_eq!(to.name(), "B");
            assert_eq!(message.name.to_string(), "Hello");
            match continuation.as_ref() {
                Protocol::Send { message, .. } => {
                    assert_eq!(message.name.to_string(), "HelloAck");
                }
                _ => panic!("expected second send from handshake"),
            }
        }
        _ => panic!("expected send from handshake lowering"),
    }
    assert!(has_quorum_extension(&choreo.protocol));
}

#[test]
fn test_parse_role_sets_and_topologies() {
    let input = r#"
role_set Signers = Alice, Bob, Carol
role_set Quorum = subset(Signers, 0..2)
cluster LocalCluster = Signers, Quorum
ring RingNet = Alice, Bob, Carol
mesh FullMesh = Alice, Bob, Carol
protocol TopologyAware =
  roles Alice, Bob
  Alice -> Bob : Ping
"#;

    let choreo = parse_choreography_str(input).expect("parse should succeed");
    let role_sets = choreo.role_sets();
    assert_eq!(role_sets.len(), 2);
    assert_eq!(role_sets[0].name, "Signers");
    assert_eq!(
        role_sets[0].members,
        vec!["Alice".to_string(), "Bob".to_string(), "Carol".to_string()]
    );
    assert_eq!(role_sets[1].subset_of.as_deref(), Some("Signers"));
    assert_eq!(role_sets[1].subset_start, Some(0));
    assert_eq!(role_sets[1].subset_end, Some(2));

    let topologies = choreo.topologies();
    assert_eq!(topologies.len(), 3);
    assert_eq!(topologies[0].kind, "cluster");
    assert_eq!(topologies[1].kind, "ring");
    assert_eq!(topologies[2].kind, "mesh");
}

#[test]
fn test_explain_lowering_and_lint_suggestions() {
    let input = r#"
proof_bundle Spec requires [speculation]
protocol ExplainMe =
  roles A, B
  fork ghost0
  A -> B : Ping
"#;

    let report = explain_lowering(input).expect("report generation should succeed");
    assert!(report.contains("Inferred bundles: Spec"));
    assert!(report.contains("dsl.inferred_requires"));
    assert!(report.contains("Lowering:"));

    let choreo = parse_choreography_str(input).expect("parse should succeed");
    let lints = collect_dsl_lints(&choreo, LintLevel::Warn);
    assert!(!lints.is_empty());
    assert!(lints[0]
        .suggestion
        .as_deref()
        .unwrap_or_default()
        .contains("requires"));
    let lsp = render_lsp_lint_diagnostics(&choreo, LintLevel::Warn);
    assert!(lsp.contains("\"quickFix\""));
}

#[test]
fn test_typed_predicate_ir_rejects_if_expression() {
    let input = r#"
protocol PredicateTyping =
  roles A, B
  choice at A
ok when (if ready { true } else { false }) ->
  A -> B : Accept
no ->
  A -> B : Reject
"#;

    let err = parse_choreography_str(input).expect_err("parse should fail");
    assert!(err.to_string().contains("boolean-like"));
}

#[test]
fn test_parse_choreography_macro_tokens_basic() {
    let input: TokenStream = quote::quote! {
        protocol PingPong = {
            roles Alice, Bob;
            Alice -> Bob : Ping;
            Bob -> Alice : Pong;
        }
    };

    let choreo = parse_choreography(input).expect("macro token parsing should succeed");
    assert_eq!(choreo.name.to_string(), "PingPong");
    assert_eq!(choreo.roles.len(), 2);
}

#[test]
fn test_parse_choreography_macro_tokens_normalizes_composite_operators() {
    let input: TokenStream = quote::quote! {
        protocol Ops = {
            roles A, B;
            handshake A <-> B : Hello;
            A ->* : Notice;
        }
    };

    let choreo = parse_choreography(input).expect("macro token parsing should succeed");
    assert_eq!(choreo.name.to_string(), "Ops");
    assert_eq!(choreo.roles.len(), 2);
}
