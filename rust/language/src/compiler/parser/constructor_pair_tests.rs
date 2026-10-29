//! Actual grammar constructor tokens and their source-to-AST consumers.
use super::{parse_choreography_str, ChoreographyParser, Protocol, Rule};
use crate::ast::{AuthorityBindingMode, AuthorityExpr, CasePattern};
use pest::Parser;

fn source(expression: &str, placement: &str, suffix: &str) -> String {
    format!("protocol Constructors =\n  roles A, B\n  let value{placement} = {expression}{suffix}\n  A -> B : Commit\n")
}

#[test]
fn constructor_bindings_preserve_names_payload_text_and_placement() {
    for (expression, name, arg) in [
        ("Ok", "Ok", None),
        ("Err", "Err", None),
        ("Ok(payload.field)", "Ok", Some("(payload.field)")),
        ("Err(problem)", "Err", Some("(problem)")),
        ("Just(payload.field)", "Just", Some("(payload.field)")),
        ("Nothing", "Nothing", None),
    ] {
        for placement in ["", " at B"] {
            for suffix in ["", " in\n    A -> B : Commit"] {
                let parsed =
                    parse_choreography_str(&source(expression, placement, suffix)).unwrap();
                let Protocol::Let {
                    execution_role,
                    mode,
                    expr,
                    continuation,
                    ..
                } = parsed.protocol
                else {
                    panic!("actual constructor binding was lost");
                };
                assert_eq!(mode, AuthorityBindingMode::Plain);
                assert_eq!(
                    expr,
                    AuthorityExpr::Constructor {
                        name: name.into(),
                        arg: arg.map(str::to_owned)
                    }
                );
                if placement.is_empty() {
                    assert!(execution_role.is_none());
                } else {
                    assert_eq!(*execution_role.unwrap().name(), "B");
                }
                assert!(matches!(*continuation, Protocol::Send { .. }));
            }
        }
    }
}

fn complete_constructor(rule: Rule, expression: &str) -> bool {
    ChoreographyParser::parse(rule, expression)
        .ok()
        .and_then(|mut pairs| pairs.next())
        .is_some_and(|pair| pair.as_span().end() == expression.len())
}

#[test]
fn constructor_productions_preserve_their_existing_arity() {
    for (rule, valid, malformed) in [
        (
            Rule::result_ctor_expr,
            "Ok(payload)",
            vec!["Ok()", "Ok(a,b)", "Err("],
        ),
        (
            Rule::maybe_ctor_expr,
            "Just(payload)",
            vec!["Just", "Just()", "Just(a,b)", "Nothing(payload)"],
        ),
    ] {
        assert!(complete_constructor(rule, valid));
        for expression in malformed {
            assert!(!complete_constructor(rule, expression), "{expression}");
        }
    }
}

#[test]
fn constructor_tokens_preserve_existing_identifier_and_call_fallbacks() {
    for (expression, expected) in [
        ("Just", AuthorityExpr::Var("Just".into())),
        (
            "Just(a,b)",
            AuthorityExpr::Call {
                name: "Just".into(),
                args: vec!["a".into(), "b".into()],
            },
        ),
    ] {
        let parsed = parse_choreography_str(&source(expression, "", "")).unwrap();
        let Protocol::Let { expr, .. } = parsed.protocol else {
            panic!("binding lost");
        };
        assert_eq!(expr, expected);
    }
}

#[test]
fn expression_constructor_tokens_leave_case_patterns_unchanged() {
    let parsed = parse_choreography_str("protocol Cases =\n  roles A, B\n  let value = Nothing\n  case value of\n    | Just(payload) =>\n        A -> B : Present(payload)\n    | Nothing =>\n        A -> B : Missing\n").unwrap();
    let Protocol::Let { continuation, .. } = parsed.protocol else {
        panic!("binding lost");
    };
    let Protocol::Case { branches, .. } = *continuation else {
        panic!("case lost");
    };
    let actual: Vec<_> = branches
        .iter()
        .map(|branch| branch.pattern.clone())
        .collect();
    assert_eq!(
        actual,
        vec![
            CasePattern {
                constructor: "Just".into(),
                binders: vec!["payload".into()]
            },
            CasePattern {
                constructor: "Nothing".into(),
                binders: vec![]
            }
        ]
    );
}
