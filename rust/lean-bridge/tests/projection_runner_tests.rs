//! Integration tests for Lean projection export via `telltale_validator`.
//!
//! These tests invoke the validator export mode via `LeanRunner::project` and
//! verify the projected local types match expectations.

use telltale_lean_bridge::export::global_to_json;
use telltale_lean_bridge::import::json_to_local;
use telltale_lean_bridge::runner::LeanRunner;
use telltale_types::{GlobalType, Label, LocalTypeR, PayloadSort};

/// Skip test if the validator binary is not available.
fn require_projection_runner() -> LeanRunner {
    if !LeanRunner::is_projection_available() {
        eprintln!(
            "SKIP: telltale_validator not found, run `cd lean && lake build telltale_validator`"
        );
        std::process::exit(0);
    }
    LeanRunner::for_projection().expect("validator should be available")
}

#[test]
fn test_simple_two_role_projection() {
    let runner = require_projection_runner();

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
    let runner = require_projection_runner();

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
