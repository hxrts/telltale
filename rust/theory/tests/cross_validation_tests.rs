//! Cross-validation: Rust projection vs Lean projection.
//!
//! Runs both Lean (via lean-bridge `LeanRunner`) and Rust projection on the
//! same `GlobalType` inputs and asserts the outputs are identical.

use telltale_lean_bridge::export::global_to_json;
use telltale_lean_bridge::import::json_to_local;
use telltale_lean_bridge::runner::LeanRunner;
use telltale_theory::project;
use telltale_types::{GlobalType, Label, PayloadSort};

/// Skip if the Lean validator binary is unavailable.
fn require_lean() -> LeanRunner {
    if !LeanRunner::is_projection_available() {
        eprintln!(
            "SKIP: telltale_validator not found, run `cd lean && lake build telltale_validator`"
        );
        std::process::exit(0);
    }
    LeanRunner::for_projection().expect("validator available")
}

/// Project via Lean and Rust, assert results match.
fn cross_validate(runner: &LeanRunner, g: &GlobalType, roles: &[&str]) {
    let json = global_to_json(g);
    let role_strings: Vec<String> = roles.iter().map(|r| r.to_string()).collect();
    let lean_projections = runner
        .project(&json, &role_strings)
        .expect("Lean projection should succeed");

    for role in roles {
        let rust_local = project(g, role).expect("Rust projection should succeed");
        let lean_json = &lean_projections[*role];
        let lean_local = json_to_local(lean_json).expect("parse Lean local type");

        assert_eq!(
            rust_local, lean_local,
            "Rust and Lean projections differ for role {role}"
        );
    }
}

#[test]
fn test_cross_validate_simple_send() {
    let runner = require_lean();
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    cross_validate(&runner, &g, &["A", "B"]);
}

#[test]
fn test_cross_validate_recursive() {
    let runner = require_lean();
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
    cross_validate(&runner, &g, &["A", "B"]);
}

#[test]
fn test_cross_validate_choice() {
    let runner = require_lean();
    let g = GlobalType::comm(
        "A",
        "B",
        vec![
            (Label::new("yes"), GlobalType::End),
            (Label::new("no"), GlobalType::End),
        ],
    );
    cross_validate(&runner, &g, &["A", "B"]);
}

#[test]
fn test_cross_validate_three_party() {
    let runner = require_lean();
    let g = GlobalType::send(
        "A",
        "B",
        Label::new("request"),
        GlobalType::send(
            "B",
            "C",
            Label::new("forward"),
            GlobalType::send("C", "A", Label::new("response"), GlobalType::End),
        ),
    );
    cross_validate(&runner, &g, &["A", "B", "C"]);
}

#[test]
fn test_cross_validate_mean_field_ising() {
    let runner = require_lean();
    let g = GlobalType::mu(
        "step",
        GlobalType::send(
            "A",
            "B",
            Label::with_sort("concentration", PayloadSort::Vector(2)),
            GlobalType::send(
                "B",
                "A",
                Label::with_sort("concentration", PayloadSort::Vector(2)),
                GlobalType::var("step"),
            ),
        ),
    );
    cross_validate(&runner, &g, &["A", "B"]);
}
