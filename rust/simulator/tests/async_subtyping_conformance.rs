#![allow(clippy::expect_used, clippy::unwrap_used)]
//! Conformance: the Rust checkers accept the recursive and asynchronous trace
//! corpus programs, and the bounded async-subtyping checker reports fuel
//! exhaustion as inconclusive, never as a refutation.

#[allow(unreachable_pub)]
#[path = "../../bridge/tests/test_choreographies/mod.rs"]
mod test_choreographies;

use telltale_simulator::{decide_async_subtyping, DecisionInconclusive, DecisionOutcome};
use telltale_theory::coherence::check_coherent;
use telltale_theory::limits::UnfoldSteps;
use telltale_theory::projection::project;
use telltale_theory::subtyping::{
    async_subtype, siso_decompose_with_fuel, sync_subtype, AsyncSubtypeError,
};
use telltale_theory::well_formedness::validate_global;
use telltale_types::{Label, LocalTypeR};

fn corpus() -> Vec<test_choreographies::ProtocolFixture> {
    vec![
        test_choreographies::bounded_loop(),
        test_choreographies::independent_pairs(),
        test_choreographies::fan_out(),
    ]
}

#[test]
fn type_checker_accepts_recursive_and_async_corpus() {
    for fixture in corpus() {
        validate_global(&fixture.global)
            .unwrap_or_else(|err| panic!("{} not well-formed: {err:?}", fixture.name));
        assert!(
            check_coherent(&fixture.global).is_coherent_core(),
            "{} not coherent",
            fixture.name
        );
        for (role, local) in &fixture.local_types {
            let projected = project(&fixture.global, role)
                .unwrap_or_else(|err| panic!("{} project {role}: {err:?}", fixture.name));
            sync_subtype(&projected, local).unwrap_or_else(|err| {
                panic!("{} local for {role} rejected: {err:?}", fixture.name)
            });
        }
    }
}

#[test]
fn async_subtyping_certifies_async_corpus_locals() {
    for fixture in [
        test_choreographies::independent_pairs(),
        test_choreographies::fan_out(),
    ] {
        for (role, local) in &fixture.local_types {
            let report = decide_async_subtyping(local, local);
            assert!(
                report.is_certified(),
                "{} {role}: {:?}",
                fixture.name,
                report.outcome
            );
        }
    }
}

/// Recursive type whose SISO decomposition cannot finish within the fuel.
fn infinite_sender() -> LocalTypeR {
    LocalTypeR::mu(
        "X",
        LocalTypeR::send("B", Label::new("hb"), LocalTypeR::var("X")),
    )
}

#[test]
fn fuel_exhaustion_is_inconclusive_not_refutation() {
    let lt = infinite_sender();
    let err = siso_decompose_with_fuel(&lt, UnfoldSteps(0)).expect_err("zero fuel must give up");
    assert!(matches!(err, AsyncSubtypeError::UnfoldLimitExceeded));
    assert!(err.is_inconclusive());
    assert!(!err.is_refutation());

    let loop_fixture = test_choreographies::bounded_loop();
    let pairs = [
        (lt.clone(), lt),
        (
            loop_fixture.local_types["A"].clone(),
            loop_fixture.local_types["A"].clone(),
        ),
        (
            loop_fixture.local_types["B"].clone(),
            loop_fixture.local_types["B"].clone(),
        ),
    ];
    for (sub, sup) in pairs {
        match async_subtype(&sub, &sup) {
            Ok(()) => assert!(decide_async_subtyping(&sub, &sup).is_certified()),
            Err(err) => {
                assert!(err.is_inconclusive(), "reflexive pair refuted: {err:?}");
                let report = decide_async_subtyping(&sub, &sup);
                assert!(!report.is_refuted(), "inconclusive reported as refutation");
                assert!(report.is_inconclusive());
                assert_eq!(
                    report.outcome,
                    DecisionOutcome::Inconclusive(
                        DecisionInconclusive::AsyncSubtypeUnfoldLimitExceeded
                    )
                );
            }
        }
    }
}

#[test]
fn infinite_sender_exhausts_default_fuel() {
    let lt = infinite_sender();
    let err = async_subtype(&lt, &lt).expect_err("default fuel should be exhausted");
    assert!(err.is_inconclusive());
    assert!(decide_async_subtyping(&lt, &lt).is_inconclusive());
}
