//! Integration tests for Lean projection export via `telltale_validator`.
//!
//! These tests invoke the validator export mode via `LeanRunner::project` and
//! verify the projected local types match expectations.

use telltale_lean_bridge::export::global_to_json;
use telltale_lean_bridge::import::json_to_local;
use telltale_lean_bridge::runner::LeanRunner;
use telltale_types::{GlobalType, Label, LocalTypeR, PayloadSort};

/// Skip test if the validator binary is not available.
fn projection_runner_if_available() -> Option<LeanRunner> {
    if !LeanRunner::is_projection_available() {
        eprintln!(
            "SKIP: telltale_validator not found, run `cd lean && lake build telltale_validator`"
        );
        return None;
    }
    Some(LeanRunner::for_projection().expect("validator should be available"))
}

#[test]
fn test_simple_two_role_projection() {
    let Some(runner) = projection_runner_if_available() else {
        return;
    };

    // A -> B: position(real). end
    let g = GlobalType::send(
        "A",
        "B",
        Label::with_sort("position", PayloadSort::Real),
        GlobalType::End,
    );

    let json = global_to_json(&g);
    let roles = vec!["A".to_string(), "B".to_string()];
    let projections = runner
        .project(&json, &roles)
        .expect("projection should succeed");

    // A should see send
    let a_local = json_to_local(&projections["A"]).expect("parse A local type");
    assert!(
        matches!(&a_local, LocalTypeR::Send { partner, .. } if partner == "B"),
        "A should send to B"
    );

    // B should see recv
    let b_local = json_to_local(&projections["B"]).expect("parse B local type");
    assert!(
        matches!(&b_local, LocalTypeR::Recv { partner, .. } if partner == "A"),
        "B should recv from A"
    );
}

#[test]
fn test_recursive_protocol_projection() {
    let Some(runner) = projection_runner_if_available() else {
        return;
    };

    // mu step. A -> B: position(vector 2). B -> A: force(vector 2). var step
    let g = GlobalType::mu(
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

    let json = global_to_json(&g);
    let roles = vec!["A".to_string(), "B".to_string()];
    let projections = runner
        .project(&json, &roles)
        .expect("projection should succeed");

    // A: mu step. send B position. recv B force. var step
    let a_local = json_to_local(&projections["A"]).expect("parse A local type");
    assert!(
        matches!(&a_local, LocalTypeR::Mu { var, .. } if var == "step"),
        "A should have recursive type"
    );

    // B: mu step. recv A position. send A force. var step
    let b_local = json_to_local(&projections["B"]).expect("parse B local type");
    assert!(
        matches!(&b_local, LocalTypeR::Mu { var, .. } if var == "step"),
        "B should have recursive type"
    );
}

#[test]
fn test_choice_projection_three_roles() {
    let Some(runner) = projection_runner_if_available() else {
        return;
    };

    // A -> B: { yes: B -> C: notify. end, no: B -> C: abort. end }
    let g = GlobalType::comm(
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

    let json = global_to_json(&g);
    let roles = vec!["A".to_string(), "B".to_string(), "C".to_string()];
    let projections = runner
        .project(&json, &roles)
        .expect("projection should succeed");

    let a_local = json_to_local(&projections["A"]).expect("parse A local type");
    let b_local = json_to_local(&projections["B"]).expect("parse B local type");
    let c_local = json_to_local(&projections["C"]).expect("parse C local type");

    assert!(
        matches!(&a_local, LocalTypeR::Send { partner, .. } if partner == "B"),
        "A should send the choice to B"
    );
    assert!(
        matches!(&b_local, LocalTypeR::Recv { partner, .. } if partner == "A"),
        "B should receive the choice from A"
    );
    assert!(
        matches!(&c_local, LocalTypeR::Recv { partner, .. } if partner == "B"),
        "C should receive B's follow-up branch message"
    );
}
