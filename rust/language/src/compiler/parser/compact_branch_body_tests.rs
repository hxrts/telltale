use super::{parse_choreography_str, parse_declared_operation, ParseError};
use crate::ast::{AuthorityExpr, Protocol};

const SOURCE: &str = r#"
effect Host
  command ready : Unit -> Result String Bool
  {
    class : best_effort
    progress : may_block
    region : session
    agreement_use : forbidden
    reentrancy : allow
  }
agreement_profile ImmediateLocal
  visibility immediate
  rule no_agreement
  usable_at none
  finalized_at none
  evidence witness
operation Check at A progress CheckProgress within bounded agreement ImmediateLocal =
  let result at A = check Host.ready()
  case result of
    | Ok(value) => A -> B : Ready
    | Err(reason) => A -> B : Denied
protocol Commands uses Host =
  roles A, B
  A -> B : Start
"#;

fn assert_actual_result_branches(protocol: &Protocol) {
    let Protocol::Let {
        name,
        execution_role,
        continuation,
        ..
    } = protocol
    else {
        panic!("original binding")
    };
    assert_eq!(name, "result");
    assert_eq!(
        execution_role.as_ref().expect("original placement").name(),
        "A"
    );
    let Protocol::Case { expr, branches } = continuation.as_ref() else {
        panic!("actual case")
    };
    assert!(matches!(expr, AuthorityExpr::Var(name) if name == "result"));
    assert_eq!(branches.len(), 2);
    for (branch, constructor, binder, label) in [
        (&branches[0], "Ok", "value", "Ready"),
        (&branches[1], "Err", "reason", "Denied"),
    ] {
        assert_eq!(branch.pattern.constructor, constructor);
        assert_eq!(branch.pattern.binders, vec![binder.to_string()]);
        let Protocol::Send {
            from,
            to,
            message,
            continuation,
            ..
        } = &branch.protocol
        else {
            panic!("actual compact send")
        };
        assert_eq!(from.name(), "A");
        assert_eq!(to.name(), "B");
        assert_eq!(message.name, label);
        assert!(message.payload.is_none() && matches!(continuation.as_ref(), Protocol::End));
    }
}

#[test]
fn actual_selected_compact_and_indented_result_branches_preserve_same_ast() {
    for source in [
        SOURCE.to_string(),
        SOURCE
            .replace("=> A -> B : Ready", "=>\n        A -> B : Ready")
            .replace("=> A -> B : Denied", "=>\n        A -> B : Denied"),
    ] {
        let parent = parse_choreography_str(&source).expect("actual root fixture parent");
        let (_, selected) =
            parse_declared_operation(&parent, "Check").expect("both documented branch shapes");
        assert_actual_result_branches(&selected.protocol);
    }
}

#[test]
fn compact_choice_and_nested_case_share_checked_statement_dispatch() {
    let source = "protocol Compact =\n  roles A, B\n  choice A at\n    | Yes => A -> B : Yes\n    | No => A -> B : No\n";
    let compact = parse_choreography_str(source).expect("compact choice");
    let indented =
        parse_choreography_str(&source.replace("=> A", "=>\n        A")).expect("indented choice");
    assert_eq!(
        crate::ast::choreography_to_global(&compact).unwrap(),
        crate::ast::choreography_to_global(&indented).unwrap()
    );
    let nested = SOURCE.replace("=> A -> B : Ready", "=> case result of\n        | Ok(value) => A -> B : Ready\n        | Err(reason) => A -> B : Denied");
    let parent = parse_choreography_str(&nested).expect("nested parent");
    let (_, selected) = parse_declared_operation(&parent, "Check").expect("compact nested case");
    let Protocol::Let { continuation, .. } = selected.protocol else {
        panic!("binding")
    };
    let Protocol::Case { branches, .. } = *continuation else {
        panic!("outer case")
    };
    assert!(
        matches!(&branches[0].protocol, Protocol::Case { branches, .. } if branches.len() == 2)
    );
}

#[test]
fn compact_timeout_and_cancel_keep_all_original_branch_messages() {
    let source = "protocol Timed =\n  roles A, B\n  timeout 5s A at\n    A -> B : Work\n  on timeout => A -> B : Expired\n  on cancel => A -> B : Cancelled\n";
    for text in [source.to_string(), source.replace("=> A", "=>\n    A")] {
        let parsed = parse_choreography_str(&text).expect("both timeout branch shapes");
        let Protocol::Timeout {
            body,
            on_timeout,
            on_cancel,
            ..
        } = parsed.protocol
        else {
            panic!("actual timeout")
        };
        for (branch, label) in [
            (body.as_ref(), "Work"),
            (on_timeout.as_ref(), "Expired"),
            (on_cancel.as_deref().expect("actual cancel"), "Cancelled"),
        ] {
            let Protocol::Send { message, .. } = branch else {
                panic!("branch send retained")
            };
            assert_eq!(message.name, label);
        }
    }
}

#[test]
fn compact_branch_undeclared_role_retains_original_typed_error_context() {
    let source = SOURCE.replace("=> A -> B : Ready", "=> A -> Foreign : Ready");
    let parent = parse_choreography_str(&source).expect("valid enclosing source");
    let error = parse_declared_operation(&parent, "Check").unwrap_err();
    let ParseError::UndefinedRole { role, span } = error else {
        panic!("original role error: {error}")
    };
    assert_eq!(role, "Foreign");
    assert!(span.line > 0 && span.column > 0 && span.snippet.contains("Foreign"));
}

#[test]
fn compact_branch_missing_statement_keeps_original_grammar_failure() {
    let malformed = SOURCE.replace("=> A -> B : Ready", "=>");
    let error = parse_choreography_str(&malformed).unwrap_err();
    let ParseError::Pest(original) = error else {
        panic!("actual missing branch grammar error: {error}");
    };
    match original.line_col {
        pest::error::LineColLocation::Pos((line, column))
        | pest::error::LineColLocation::Span((line, column), _) => {
            assert!(line > 0 && column > 0);
        }
    }
}
