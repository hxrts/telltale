//! Strict compiler-pipeline conformance tests.
//!
//! These tests bind the supported DSL subset directly to the Lean-facing JSON
//! bridge: parse DSL, lower to theory types, round-trip through exact-shape
//! JSON import/export, and compare projections against the Lean validator.

#![allow(clippy::expect_used)]

use serde_json::json;
use telltale_bridge::{global_to_json, json_to_global, json_to_local, local_to_json, LeanRunner};
use telltale_language::ast::{
    choreography_to_global, local_to_local_r, local_types_equivalent, Choreography, ConversionError,
};
use telltale_language::compiler::parser::parse_choreography_str;
use telltale_language::compiler::projection::project;
use telltale_types::{GlobalType, LocalTypeR};

const STRICT_ENV: &str = "TELLTALE_REQUIRE_LEAN_VALIDATOR";

fn strict_projection_required() -> bool {
    std::env::var(STRICT_ENV)
        .map(|value| value != "0")
        .unwrap_or(false)
}

fn projection_runner() -> Option<LeanRunner> {
    match LeanRunner::for_projection() {
        Ok(runner) => Some(runner),
        Err(telltale_bridge::LeanRunnerError::BinaryNotFound(_)) => {
            assert!(
                !strict_projection_required(),
                "strict compiler-pipeline verification is enabled but telltale_validator is unavailable"
            );
            eprintln!(
                "SKIPPED: telltale_validator not found, run `cd lean && lake build telltale_validator`"
            );
            None
        }
        Err(err) => panic!("failed to initialize Lean projection runner: {err}"),
    }
}

fn parse_choreography(input: &str) -> Choreography {
    parse_choreography_str(input).expect("failed to parse supported DSL fixture")
}

fn find_role<'a>(choreography: &'a Choreography, name: &str) -> &'a telltale_language::ast::Role {
    choreography
        .roles
        .iter()
        .find(|role| *role.name() == name)
        .unwrap_or_else(|| panic!("role {name} not found"))
}

fn assert_global_json_roundtrip(global: &GlobalType) {
    let json = global_to_json(global);
    let parsed = json_to_global(&json).expect("global export should import");
    assert_eq!(
        &parsed, global,
        "global import/export must preserve exact structure"
    );
    assert_eq!(
        global_to_json(&parsed),
        json,
        "global export/import/export must be canonical"
    );
}

fn assert_local_json_roundtrip(local: &LocalTypeR) {
    let json = local_to_json(local);
    let parsed = json_to_local(&json).expect("local export should import");
    assert!(
        local_types_equivalent(&parsed, local),
        "local import/export must preserve theory-equivalent structure: parsed={parsed:?} local={local:?}"
    );
    assert_eq!(
        local_to_json(&parsed),
        json,
        "local export/import/export must be canonical"
    );
}

fn assert_projection_matches_lean(
    runner: &LeanRunner,
    choreography: &Choreography,
    global: &GlobalType,
) {
    let role_names: Vec<String> = choreography
        .roles
        .iter()
        .map(|role| role.name().to_string())
        .collect();
    let global_json = global_to_json(global);
    let lean_projections = runner
        .project(&global_json, &role_names)
        .expect("Lean projection export should succeed");

    for role_name in &role_names {
        let role = find_role(choreography, role_name);
        let local = project(choreography, role)
            .unwrap_or_else(|err| panic!("DSL projection should succeed for {role_name}: {err:?}"));
        let local_r = local_to_local_r(&local)
            .unwrap_or_else(|err| panic!("local_to_local_r should succeed for {role_name}: {err}"));
        assert_local_json_roundtrip(&local_r);

        let lean_local = json_to_local(
            lean_projections
                .get(role_name)
                .unwrap_or_else(|| panic!("Lean output missing role {role_name}")),
        )
        .expect("Lean projection JSON should import");
        assert!(
            local_types_equivalent(&local_r, &lean_local),
            "Rust and Lean projections must match for role {role_name}: rust={local_r:?} lean={lean_local:?}"
        );

        let validation_result = runner
            .validate(
                &global_json,
                &json!({
                    "role": role_name,
                    "local_type": local_to_json(&local_r),
                }),
            )
            .expect("Lean validator call should succeed");
        assert!(
            validation_result.success,
            "Lean validator should accept the converted Rust local type for {role_name}: {:?}",
            validation_result
        );
    }
}

#[test]
fn supported_dsl_subset_lowers_to_exact_json_and_matches_lean_projection() {
    let cases = [
        (
            "ping_pong",
            r#"
protocol PingPong =
    roles A, B
    A -> B : Ping
    B -> A : Pong
"#,
        ),
        (
            "binary_choice",
            r#"
protocol BinaryChoice =
    roles Client, Server
    choice Client at
      | Accept =>
          Client -> Server : Accept
      | Reject =>
          Client -> Server : Reject
"#,
        ),
        (
            "recursive",
            r#"
protocol SimpleRec =
    roles A, B
    rec Loop
        A -> B : Ping
        B -> A : Pong
        continue Loop
"#,
        ),
        (
            "counted_loop",
            r#"
protocol CountedLoop =
    roles A, B
    loop repeat 3
      A -> B : Ping
      B -> A : Pong
"#,
        ),
        (
            "mergeable_three_party_choice",
            r#"
protocol MergeableThreePartyChoice =
    roles A, B, C
    choice A at
      | Left =>
          A -> B : Left
          B -> C : Notify
      | Right =>
          A -> B : Right
          B -> C : Notify
"#,
        ),
    ];

    let runner = projection_runner();
    for (name, dsl) in cases {
        let choreography = parse_choreography(dsl);
        let global = choreography_to_global(&choreography)
            .unwrap_or_else(|err| panic!("supported case {name} must lower to GlobalType: {err}"));
        assert_global_json_roundtrip(&global);
        if let Some(runner) = &runner {
            assert_projection_matches_lean(runner, &choreography, &global);
        }
    }
}

#[test]
fn unsupported_protocol_features_fail_closed_at_global_conversion_boundary() {
    let cases = [
        (
            "parallel",
            r#"
protocol ParallelFlow =
    roles A, B, C, D
    par
      | A -> B : Left
      | C -> D : Right
"#,
            "Parallel",
        ),
        (
            "timeout",
            r#"
protocol TimeoutFlow =
    roles A, B
    timeout 5s A at
      B -> A : Slow
    on timeout =>
      A -> B : TimedOut
"#,
            "Timeout",
        ),
    ];

    for (name, dsl, expected_feature) in cases {
        let choreography = parse_choreography(dsl);
        let err = choreography_to_global(&choreography)
            .expect_err(&format!("unsupported case {name} must fail closed"));
        assert!(
            matches!(err, ConversionError::UnsupportedFeature { ref feature, .. } if feature == expected_feature),
            "unsupported case {name} must report {expected_feature}, got {err:?}"
        );
    }
}
