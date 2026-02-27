//! Cross-validation: Rust projection vs Lean projection.
//!
//! Runs both Lean (via lean-bridge `LeanRunner`) and Rust projection on the
//! same `GlobalType` inputs and asserts the outputs are identical.

use telltale_lean_bridge::export::global_to_json;
#[cfg(feature = "async-subtyping")]
use telltale_lean_bridge::export::local_to_json;
use telltale_lean_bridge::import::json_to_local;
use telltale_lean_bridge::runner::LeanRunner;
use telltale_theory::project;
#[cfg(feature = "async-subtyping")]
use telltale_theory::{async_subtype, orphan_free};
#[cfg(feature = "async-subtyping")]
use telltale_types::LocalTypeR;
use telltale_types::{GlobalType, Label, PayloadSort};

/// Skip if the Lean validator binary is unavailable.
fn require_lean() -> Option<LeanRunner> {
    if !LeanRunner::is_projection_available() {
        eprintln!(
            "SKIP: telltale_validator not found, run `cd lean && lake build telltale_validator`"
        );
        return None;
    }
    Some(LeanRunner::for_projection().expect("validator available"))
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
    let Some(runner) = require_lean() else {
        return;
    };
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    cross_validate(&runner, &g, &["A", "B"]);
}

#[test]
fn test_cross_validate_recursive() {
    let Some(runner) = require_lean() else {
        return;
    };
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
    let Some(runner) = require_lean() else {
        return;
    };
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
    let Some(runner) = require_lean() else {
        return;
    };
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
    let Some(runner) = require_lean() else {
        return;
    };
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

#[cfg(feature = "async-subtyping")]
fn cross_validate_async_subtype(runner: &LeanRunner, sub: &LocalTypeR, sup: &LocalTypeR) {
    let rust_ok = async_subtype(sub, sup).is_ok();
    let lean_ok = runner
        .check_async_subtype(&local_to_json(sub), &local_to_json(sup))
        .expect("Lean async-subtyping check should succeed");
    assert_eq!(
        rust_ok, lean_ok,
        "Rust and Lean async-subtyping differ for sub={sub:?}, sup={sup:?}"
    );
}

#[cfg(feature = "async-subtyping")]
#[test]
fn test_cross_validate_async_subtyping_identical_send() {
    let Some(runner) = require_lean() else {
        return;
    };
    let t = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
    cross_validate_async_subtype(&runner, &t, &t);
}

#[cfg(feature = "async-subtyping")]
#[test]
fn test_cross_validate_async_subtyping_label_mismatch() {
    let Some(runner) = require_lean() else {
        return;
    };
    let sub = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
    let sup = LocalTypeR::send("B", Label::new("other"), LocalTypeR::End);
    cross_validate_async_subtype(&runner, &sub, &sup);
}

#[cfg(feature = "async-subtyping")]
#[test]
fn test_cross_validate_async_subtyping_phase_mismatch() {
    let Some(runner) = require_lean() else {
        return;
    };
    let sub = LocalTypeR::send(
        "B",
        Label::new("req"),
        LocalTypeR::recv("B", Label::new("resp"), LocalTypeR::End),
    );
    let sup = LocalTypeR::send("B", Label::new("req"), LocalTypeR::End);
    cross_validate_async_subtype(&runner, &sub, &sup);
}

#[cfg(feature = "async-subtyping")]
fn cross_validate_orphan_free(runner: &LeanRunner, lt: &LocalTypeR) {
    let rust_ok = orphan_free(lt);
    let lean_ok = runner
        .check_orphan_free(&local_to_json(lt))
        .expect("Lean orphan-free check should succeed");
    assert_eq!(
        rust_ok, lean_ok,
        "Rust and Lean orphan-free checks differ for local type {lt:?}"
    );
}

#[cfg(feature = "async-subtyping")]
#[test]
fn test_cross_validate_orphan_free_matching_label() {
    let Some(runner) = require_lean() else {
        return;
    };
    let t = LocalTypeR::send(
        "B",
        Label::new("req"),
        LocalTypeR::recv("B", Label::new("req"), LocalTypeR::End),
    );
    cross_validate_orphan_free(&runner, &t);
}

#[cfg(feature = "async-subtyping")]
#[test]
fn test_cross_validate_orphan_free_unmatched_send() {
    let Some(runner) = require_lean() else {
        return;
    };
    let t = LocalTypeR::send("B", Label::new("req"), LocalTypeR::End);
    cross_validate_orphan_free(&runner, &t);
}
