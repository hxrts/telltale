//! Source-controlled conformance vectors for `telltale-search`.
#![cfg(not(target_arch = "wasm32"))]
#![allow(clippy::expect_used, missing_docs)]

mod support;

use serde_json::{json, Value};
#[cfg(feature = "multi-thread")]
use std::num::NonZeroU64;
use support::FixtureDomain;
#[cfg(feature = "multi-thread")]
use telltale_search::NativeParallelExecutor;
use telltale_search::{
    run_with_executor, validate_fairness_certificate_trace, EpsilonMilli, SearchFairnessAssumption,
    SearchRunConfig, SearchSchedulerProfile, SerialProposalExecutor,
};

fn vector_domain() -> FixtureDomain {
    let mut domain = FixtureDomain::default();
    domain.edge(0, 1, "0-1", 1);
    domain.edge(0, 2, "0-2", 1);
    domain.edge(1, 3, "1-3", 1);
    domain.edge(2, 3, "2-3", 2);
    domain
}

fn expected_vectors() -> Value {
    serde_json::from_str(include_str!("data/search_vectors_v1.json"))
        .expect("parse source-controlled search vectors")
}

#[cfg(feature = "multi-thread")]
fn expected_threaded_exact_vectors() -> Value {
    serde_json::from_str(include_str!("data/search_vectors_threaded_exact_v1.json"))
        .expect("parse source-controlled exact-threaded search vectors")
}

fn actual_canonical_vectors() -> Value {
    let mut machine =
        telltale_search::SearchMachine::new(vector_domain(), 1, 0, 3, EpsilonMilli::one());
    let (report, replay) = run_with_executor(
        &mut machine,
        &SerialProposalExecutor,
        SearchRunConfig {
            scheduler_profile: SearchSchedulerProfile::CanonicalSerial,
            batch_width: 1,
            fairness_assumptions: [SearchFairnessAssumption::DeterministicSchedulerConfluence]
                .into_iter()
                .collect(),
        },
    )
    .expect("canonical vector run");

    assert_eq!(validate_fairness_certificate_trace(&replay), Ok(()));

    json!({
        "schema_version": "search_vectors_v1",
        "theorem_pack": report.theorem_pack,
        "route_bounds": report.route_bounds,
        "final_state": report.final_state,
        "fairness_certificate_trace": report.fairness_certificate_trace,
        "observation": report.observation,
        "replay_rounds": replay.rounds,
    })
}

#[cfg(feature = "multi-thread")]
fn actual_threaded_exact_vectors() -> Value {
    let mut machine =
        telltale_search::SearchMachine::new(vector_domain(), 1, 0, 3, EpsilonMilli::one());
    let executor = NativeParallelExecutor::new(NonZeroU64::new(1).expect("non-zero width"))
        .expect("threaded executor");
    let (report, replay) = run_with_executor(
        &mut machine,
        &executor,
        SearchRunConfig {
            scheduler_profile: SearchSchedulerProfile::ThreadedExactSingleLane,
            batch_width: 1,
            fairness_assumptions: [SearchFairnessAssumption::DeterministicSchedulerConfluence]
                .into_iter()
                .collect(),
        },
    )
    .expect("threaded exact vector run");

    assert_eq!(validate_fairness_certificate_trace(&replay), Ok(()));

    json!({
        "schema_version": "search_vectors_threaded_exact_v1",
        "theorem_pack": report.theorem_pack,
        "fairness": report.fairness,
        "route_bounds": report.route_bounds,
        "final_state": report.final_state,
        "fairness_certificate_trace": report.fairness_certificate_trace,
        "observation": report.observation,
        "replay_rounds": replay.rounds,
    })
}

#[test]
fn canonical_search_vectors_match_the_source_controlled_fixture() {
    assert_eq!(actual_canonical_vectors(), expected_vectors());
}

#[test]
fn tampered_search_vectors_are_rejected_by_exact_fixture_comparison() {
    let actual = actual_canonical_vectors();

    let mut tampered_theorem_pack = expected_vectors();
    tampered_theorem_pack["theorem_pack"]["inventory"][0]["present"] = Value::Bool(false);
    assert_ne!(actual, tampered_theorem_pack);

    let mut tampered_final_state = expected_vectors();
    tampered_final_state["final_state"]["incumbent_cost"] = json!(3);
    assert_ne!(actual, tampered_final_state);

    let mut tampered_certified_batch = expected_vectors();
    tampered_certified_batch["fairness_certificate_trace"][0]["certified_batch_nodes"] = json!([9]);
    assert_ne!(actual, tampered_certified_batch);

    let mut tampered_commits = expected_vectors();
    tampered_commits["fairness_certificate_trace"][1]["certified_normalized_commits"][0]
        ["parent"] = json!(9);
    assert_ne!(actual, tampered_commits);

    let mut tampered_round_state = expected_vectors();
    tampered_round_state["replay_rounds"][0]["state_after_round"]["closed_nodes"] = json!([7]);
    assert_ne!(actual, tampered_round_state);

    let mut tampered_discovery_certificate = expected_vectors();
    tampered_discovery_certificate["route_bounds"]["discovery_certificate"]
        ["service_bound_steps"] = json!(2);
    assert_ne!(actual, tampered_discovery_certificate);

    let mut tampered_route_metric = expected_vectors();
    tampered_route_metric["route_bounds"]["selected_route_summary"]["metrics"][2]["value"] =
        json!(9);
    assert_ne!(actual, tampered_route_metric);
}

#[cfg(feature = "multi-thread")]
#[test]
fn threaded_exact_search_vectors_match_the_source_controlled_fixture() {
    assert_eq!(
        actual_threaded_exact_vectors(),
        expected_threaded_exact_vectors()
    );
}

#[cfg(feature = "multi-thread")]
#[test]
fn threaded_exact_vectors_preserve_the_canonical_authoritative_artifacts() {
    let canonical = actual_canonical_vectors();
    let threaded = actual_threaded_exact_vectors();

    assert_eq!(threaded["final_state"], canonical["final_state"]);
    assert_eq!(
        threaded["observation"]["normalized_commit_trace"],
        canonical["observation"]["normalized_commit_trace"]
    );
    assert_eq!(
        threaded["observation"]["incumbent_path"],
        canonical["observation"]["incumbent_path"]
    );
    assert_eq!(
        threaded["theorem_pack"]["inventory"],
        canonical["theorem_pack"]["inventory"]
    );
    assert_eq!(
        threaded["fairness"]["claim_class"],
        json!("ExactOneStepViaThreadedRefinement")
    );
}
