use std::fs;
use std::path::{Path, PathBuf};

use telltale_runtime::compiler::parser::parse_choreography_file;

#[derive(Clone, Copy)]
struct PassCase {
    name: &'static str,
    session_projectable: bool,
    protocol_machine_executable: bool,
    theory_convertible: bool,
}

#[derive(Clone, Copy)]
struct ControlFlowPair {
    construct: &'static str,
    pass: PassCase,
    fail_fixture: &'static str,
}

const CONTROL_FLOW_PAIRS: &[ControlFlowPair] = &[
    ControlFlowPair {
        construct: "call",
        pass: PassCase {
            name: "call_plain_communication",
            session_projectable: true,
            protocol_machine_executable: true,
            theory_convertible: true,
        },
        fail_fixture: "linear_call_fail_closed",
    },
    ControlFlowPair {
        construct: "case",
        pass: PassCase {
            name: "case_authoritative_binding",
            session_projectable: false,
            protocol_machine_executable: true,
            theory_convertible: false,
        },
        fail_fixture: "linear_case_divergence",
    },
    ControlFlowPair {
        construct: "choice",
        pass: PassCase {
            name: "choice_observational_binding",
            session_projectable: true,
            protocol_machine_executable: true,
            theory_convertible: true,
        },
        fail_fixture: "linear_choice_divergence",
    },
    ControlFlowPair {
        construct: "loop",
        pass: PassCase {
            name: "loop_authoritative_binding",
            session_projectable: true,
            protocol_machine_executable: true,
            theory_convertible: true,
        },
        fail_fixture: "linear_loop_preservation",
    },
    ControlFlowPair {
        construct: "par",
        pass: PassCase {
            name: "parallel_observational_binding",
            session_projectable: true,
            protocol_machine_executable: true,
            theory_convertible: false,
        },
        fail_fixture: "linear_parallel_preservation",
    },
    ControlFlowPair {
        construct: "recursion",
        pass: PassCase {
            name: "recursion_authoritative_binding",
            session_projectable: true,
            protocol_machine_executable: true,
            theory_convertible: true,
        },
        fail_fixture: "linear_recursion_preservation",
    },
    ControlFlowPair {
        construct: "timeout",
        pass: PassCase {
            name: "timeout_observational_binding",
            session_projectable: false,
            protocol_machine_executable: true,
            theory_convertible: false,
        },
        fail_fixture: "linear_timeout_divergence",
    },
];

const OBSERVER_AUTHORITY_FAIL_FIXTURES: &[&str] = &[
    "observational_call_with_check",
    "observational_choice_with_check",
    "observational_timeout_with_check",
];

fn authority_fixture_dir(kind: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("ui")
        .join(kind)
}

fn compile_fixture(path: &Path) -> Result<telltale_runtime::ast::Choreography, String> {
    let choreography = parse_choreography_file(path).map_err(|err| err.to_string())?;
    choreography.validate().map_err(|err| err.to_string())?;
    Ok(choreography)
}

fn expected_stderr(stem: &str) -> String {
    fs::read_to_string(authority_fixture_dir("authority_fail").join(format!("{stem}.stderr")))
        .unwrap_or_else(|err| panic!("read expected stderr for {stem}: {err}"))
}

#[test]
fn authority_control_flow_pairs_spell_out_supported_and_rejected_surfaces() {
    let pass_dir = authority_fixture_dir("authority_pass");
    let fail_dir = authority_fixture_dir("authority_fail");

    for pair in CONTROL_FLOW_PAIRS {
        let pass_path = pass_dir.join(format!("{}.tell", pair.pass.name));
        let choreography = compile_fixture(&pass_path).unwrap_or_else(|err| {
            panic!(
                "pass fixture {} for {} should compile: {err}",
                pass_path.display(),
                pair.construct
            )
        });
        let status = choreography.language_tier_status();
        assert_eq!(
            status.session_projectable, pair.pass.session_projectable,
            "unexpected session_projectable status for {} ({})",
            pair.pass.name, pair.construct
        );
        assert_eq!(
            status.protocol_machine_executable, pair.pass.protocol_machine_executable,
            "unexpected protocol_machine_executable status for {} ({})",
            pair.pass.name, pair.construct
        );
        assert_eq!(
            status.theory_convertible, pair.pass.theory_convertible,
            "unexpected theory_convertible status for {} ({})",
            pair.pass.name, pair.construct
        );

        let fail_path = fail_dir.join(format!("{}.tell", pair.fail_fixture));
        let err = compile_fixture(&fail_path).expect_err("negative fixture must fail");
        for needle in expected_stderr(pair.fail_fixture)
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty())
        {
            assert!(
                err.contains(needle),
                "negative fixture {} for {} failed with unexpected error.\nexpected snippet: {}\nactual error: {}",
                fail_path.display(),
                pair.construct,
                needle,
                err
            );
        }
    }
}

#[test]
fn observer_authority_separation_fails_closed_under_control_flow() {
    let fail_dir = authority_fixture_dir("authority_fail");

    for stem in OBSERVER_AUTHORITY_FAIL_FIXTURES {
        let err = compile_fixture(&fail_dir.join(format!("{stem}.tell")))
            .expect_err("observer/authority separation fixture must fail");
        for needle in expected_stderr(stem)
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty())
        {
            assert!(
                err.contains(needle),
                "fixture {stem} failed with unexpected error.\nexpected snippet: {needle}\nactual error: {err}"
            );
        }
    }
}

#[test]
fn authority_control_flow_fixture_inventory_is_explicit() {
    let listed_passes: Vec<_> = CONTROL_FLOW_PAIRS
        .iter()
        .map(|pair| pair.pass.name)
        .collect();
    let listed_fails: Vec<_> = CONTROL_FLOW_PAIRS
        .iter()
        .map(|pair| pair.fail_fixture)
        .chain(OBSERVER_AUTHORITY_FAIL_FIXTURES.iter().copied())
        .collect();

    let mut actual_passes: Vec<_> = fs::read_dir(authority_fixture_dir("authority_pass"))
        .expect("read authority pass fixtures")
        .map(|entry| entry.expect("authority pass entry").path())
        .filter(|path| path.extension().and_then(|ext| ext.to_str()) == Some("tell"))
        .map(|path| {
            path.file_stem()
                .and_then(|stem| stem.to_str())
                .expect("fixture stem should be UTF-8")
                .to_string()
        })
        .collect();
    actual_passes.sort();

    let mut actual_fails: Vec<_> = fs::read_dir(authority_fixture_dir("authority_fail"))
        .expect("read authority fail fixtures")
        .map(|entry| entry.expect("authority fail entry").path())
        .filter(|path| path.extension().and_then(|ext| ext.to_str()) == Some("tell"))
        .map(|path| {
            path.file_stem()
                .and_then(|stem| stem.to_str())
                .expect("fixture stem should be UTF-8")
                .to_string()
        })
        .filter(|stem| {
            CONTROL_FLOW_PAIRS
                .iter()
                .any(|pair| pair.fail_fixture == stem)
                || OBSERVER_AUTHORITY_FAIL_FIXTURES
                    .iter()
                    .any(|fixture| fixture == stem)
        })
        .collect();
    actual_fails.sort();

    let mut expected_passes: Vec<_> = listed_passes.into_iter().map(str::to_string).collect();
    expected_passes.sort();
    let mut expected_fails: Vec<_> = listed_fails.into_iter().map(str::to_string).collect();
    expected_fails.sort();

    assert_eq!(actual_passes, expected_passes);
    assert_eq!(actual_fails, expected_fails);
}
