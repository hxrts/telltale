#![allow(clippy::expect_used)]
//! Regular practical fragment checks via Lean projection runner.

use telltale_bridge::{local_to_json, LeanRunner};
use telltale_language::ast::convert::local_to_local_r;
use telltale_language::compiler::parser::parse_choreography_str;
use telltale_types::{Label, LocalTypeR};

fn strict_projection_runner_required() -> bool {
    std::env::var("TELLTALE_REQUIRE_LEAN_PROJECTION_RUNNER")
        .map(|value| value != "0")
        .unwrap_or(false)
}

fn lean_runner_or_skip() -> Option<LeanRunner> {
    match LeanRunner::for_projection() {
        Ok(runner) => Some(runner),
        Err(err) => {
            if strict_projection_runner_required() {
                panic!("Lean projection runner is required for strict checks: {err}");
            }
            eprintln!("skipping regular practical fragment checks: {err}");
            None
        }
    }
}

fn full_unfold_head(local: &LocalTypeR) -> &'static str {
    match local.full_unfold() {
        LocalTypeR::End => "end",
        LocalTypeR::Var(_) => "var",
        LocalTypeR::Mu { .. } => "mu",
        LocalTypeR::Send { .. } => "send",
        LocalTypeR::Recv { .. } => "recv",
    }
}

#[test]
fn lean_and_rust_agree_on_regular_practical_fragment_corpus() {
    let Some(runner) = lean_runner_or_skip() else {
        return;
    };

    let cases = vec![
        ("end", LocalTypeR::End),
        (
            "send",
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End),
        ),
        (
            "guarded_recv_loop",
            LocalTypeR::mu(
                "t",
                LocalTypeR::recv("B", Label::new("msg"), LocalTypeR::var("t")),
            ),
        ),
        ("unguarded_loop", LocalTypeR::mu("t", LocalTypeR::var("t"))),
        (
            "unbound_variable",
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("t")),
        ),
    ];

    for (name, local) in cases {
        let result = runner
            .check_regular_practical_fragment(&local_to_json(&local))
            .unwrap_or_else(|err| panic!("Lean regular fragment check for {name}: {err}"));
        assert_eq!(
            result.result,
            local.regular_practical_fragment(),
            "fragment result mismatch for {name}"
        );
        assert_eq!(
            result.reaches_communication,
            local.reaches_communication(),
            "reachability mismatch for {name}"
        );
        assert_eq!(
            result.well_formed,
            local.well_formed(),
            "well-formedness mismatch for {name}"
        );
        assert_eq!(
            result.full_unfold_head,
            full_unfold_head(&local),
            "full-unfold head mismatch for {name}"
        );
    }
}

#[test]
fn projected_session_types_land_in_the_regular_practical_fragment() {
    let Some(runner) = lean_runner_or_skip() else {
        return;
    };

    let choreography = parse_choreography_str(
        r#"
        protocol PingPong =
          roles A, B
          A -> B : Ping
          B -> A : Pong
        "#,
    )
    .expect("parse ping-pong protocol");
    choreography
        .validate()
        .expect("validate ping-pong protocol");

    for role in &choreography.roles {
        let projected = telltale_language::project(&choreography, role)
            .unwrap_or_else(|err| panic!("project {}: {err}", role.name()));
        let local = local_to_local_r(&projected)
            .unwrap_or_else(|err| panic!("convert {} local type: {err}", role.name()));
        let result = runner
            .check_regular_practical_fragment(&local_to_json(&local))
            .unwrap_or_else(|err| panic!("Lean regular fragment check for {}: {err}", role.name()));
        assert!(
            result.result,
            "projected ping-pong local for {} should be automatically discharged",
            role.name()
        );
    }
}
