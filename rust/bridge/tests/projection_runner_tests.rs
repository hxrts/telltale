//! Integration tests for Lean projection export via `telltale_validator`.
//!
//! These tests exercise the real validator binary rather than only local
//! projection logic. In strict CI lanes they must fail closed if the validator
//! is unavailable.

#![allow(clippy::expect_used)]

use serde_json::json;
use telltale_bridge::export::global_to_json;
use telltale_bridge::import::json_to_local;
use telltale_bridge::{LeanRunner, LeanRunnerError};
use telltale_types::{GlobalType, Label, LocalTypeR, PayloadSort};

const STRICT_ENV: &str = "TELLTALE_REQUIRE_LEAN_VALIDATOR";

fn strict_projection_required() -> bool {
    std::env::var(STRICT_ENV)
        .map(|value| value != "0")
        .unwrap_or(false)
}

fn projection_runner() -> Option<LeanRunner> {
    match LeanRunner::for_projection() {
        Ok(runner) => Some(runner),
        Err(LeanRunnerError::BinaryNotFound(_)) => {
            assert!(
                !strict_projection_required(),
                "strict projection verification is enabled but telltale_validator is unavailable"
            );
            eprintln!(
                "SKIPPED: telltale_validator not found, run `cd lean && lake build telltale_validator`"
            );
            None
        }
        Err(err) => panic!("failed to initialize Lean projection runner: {err}"),
    }
}

fn assert_send_projection(
    projections: &std::collections::HashMap<String, serde_json::Value>,
    role: &str,
    partner: &str,
) {
    let local = json_to_local(&projections[role]).expect("parse send projection");
    assert!(
        matches!(&local, LocalTypeR::Send { partner: actual, .. } if actual == partner),
        "{role} should project to Send({partner}), got {local:?}"
    );
}

fn assert_recv_projection(
    projections: &std::collections::HashMap<String, serde_json::Value>,
    role: &str,
    partner: &str,
) {
    let local = json_to_local(&projections[role]).expect("parse recv projection");
    assert!(
        matches!(&local, LocalTypeR::Recv { partner: actual, .. } if actual == partner),
        "{role} should project to Recv({partner}), got {local:?}"
    );
}

#[test]
fn test_projection_corpus() {
    let Some(runner) = projection_runner() else {
        return;
    };

    let simple = GlobalType::send(
        "A",
        "B",
        Label::with_sort("position", PayloadSort::Real),
        GlobalType::End,
    );
    let simple_roles = vec!["A".to_string(), "B".to_string()];
    let simple_projections = runner
        .project(&global_to_json(&simple), &simple_roles)
        .expect("simple projection should succeed");
    assert_send_projection(&simple_projections, "A", "B");
    assert_recv_projection(&simple_projections, "B", "A");

    let recursive = GlobalType::mu(
        "step",
        GlobalType::send(
            "A",
            "B",
            Label::with_sort("position", PayloadSort::Vector(2)),
            GlobalType::send(
                "B",
                "A",
                Label::with_sort("force", PayloadSort::Vector(2)),
                GlobalType::var("step"),
            ),
        ),
    );
    let recursive_roles = vec!["A".to_string(), "B".to_string()];
    let recursive_projections = runner
        .project(&global_to_json(&recursive), &recursive_roles)
        .expect("recursive projection should succeed");
    let a_local = json_to_local(&recursive_projections["A"]).expect("parse A recursive local type");
    let b_local = json_to_local(&recursive_projections["B"]).expect("parse B recursive local type");
    assert!(
        matches!(&a_local, LocalTypeR::Mu { var, .. } if var == "step"),
        "A should project to a recursive local type, got {a_local:?}"
    );
    assert!(
        matches!(&b_local, LocalTypeR::Mu { var, .. } if var == "step"),
        "B should project to a recursive local type, got {b_local:?}"
    );

    let three_party_choice = GlobalType::comm(
        "A",
        "B",
        vec![
            (
                Label::with_sort("yes", PayloadSort::Unit),
                GlobalType::send(
                    "B",
                    "C",
                    Label::with_sort("notify", PayloadSort::Unit),
                    GlobalType::End,
                ),
            ),
            (
                Label::with_sort("no", PayloadSort::Unit),
                GlobalType::send(
                    "B",
                    "C",
                    Label::with_sort("abort", PayloadSort::Unit),
                    GlobalType::End,
                ),
            ),
        ],
    );
    let three_party_roles = vec!["A".to_string(), "B".to_string(), "C".to_string()];
    let choice_projections = runner
        .project(&global_to_json(&three_party_choice), &three_party_roles)
        .expect("three-party choice projection should succeed");
    assert_send_projection(&choice_projections, "A", "B");
    assert_recv_projection(&choice_projections, "B", "A");
    assert_recv_projection(&choice_projections, "C", "B");
}

#[test]
fn test_projection_reports_missing_requested_role_deterministically() {
    let Some(runner) = projection_runner() else {
        return;
    };

    let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let error = runner
        .project(&global_to_json(&global), &["Missing".to_string()])
        .expect_err("requesting a missing role should fail");

    match error {
        LeanRunnerError::ParseError(message) => {
            assert!(
                message.contains("missing projection for role Missing"),
                "expected missing-role diagnostic, got: {message}"
            );
        }
        other => panic!("expected parse error for missing role, got: {other}"),
    }
}

#[test]
fn test_projection_rejects_malformed_payload_with_diagnostic() {
    let Some(runner) = projection_runner() else {
        return;
    };

    let malformed = json!({
        "kind": "bogus_global_type",
        "branches": []
    });
    let error = runner
        .project(&malformed, &["A".to_string()])
        .expect_err("malformed global payload should fail");

    match error {
        LeanRunnerError::ParseError(message) => {
            assert!(
                !message.trim().is_empty(),
                "expected a non-empty validator diagnostic"
            );
        }
        LeanRunnerError::ProcessFailed { .. } => {}
        other => panic!("expected diagnostic-bearing projection failure, got: {other}"),
    }
}
