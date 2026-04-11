//! Source-controlled recovery conformance vectors for `telltale-search`.
#![cfg(not(target_arch = "wasm32"))]
#![allow(clippy::expect_used, missing_docs)]

mod support;

use serde_json::{json, Value};
use support::FixtureDomain;
use telltale_search::{
    commit_epoch_reconfiguration, run_with_executor, validate_fairness_certificate_trace,
    EpochReconfigurationRequest, EpsilonMilli, SearchExecutionPolicy, SearchFairnessAssumption,
    SearchReseedingPolicy, SearchRunConfig, SearchSchedulerProfile, SerialProposalExecutor,
};

fn recovery_domain() -> FixtureDomain {
    let mut domain = FixtureDomain::default();
    domain.edge(0, 1, "0-1", 1);
    domain.edge(0, 2, "0-2", 1);
    domain.edge(1, 3, "1-3", 1);
    domain.edge(2, 3, "2-3", 2);
    domain
}

fn expected_recovery_vectors() -> Value {
    serde_json::from_str(include_str!("data/search_recovery_vectors_v1.json"))
        .expect("parse source-controlled recovery vectors")
}

fn actual_recovery_vectors() -> Value {
    let mut machine =
        telltale_search::SearchMachine::new(recovery_domain(), 1, 0, 3, EpsilonMilli::one());
    machine.step_once().expect("first pre-reconfiguration step");
    commit_epoch_reconfiguration(
        &mut machine,
        EpochReconfigurationRequest {
            next_epoch: 2,
            reseeding_policy: SearchReseedingPolicy::StartOnly,
        },
    );
    let (report, replay) = run_with_executor(
        &mut machine,
        &SerialProposalExecutor,
        SearchRunConfig::new(
            SearchExecutionPolicy::new(SearchSchedulerProfile::CanonicalSerial, 1),
            [SearchFairnessAssumption::DeterministicSchedulerConfluence]
                .into_iter()
                .collect(),
        ),
    )
    .expect("recovery run");
    assert_eq!(validate_fairness_certificate_trace(&replay), Ok(()));

    json!({
        "schema_version": "search_recovery_vectors_v1",
        "route_bounds": report.route_bounds,
        "final_state": report.final_state,
        "observation": report.observation,
        "replay_rounds": replay.rounds,
    })
}

#[test]
fn canonical_recovery_vectors_match_the_source_controlled_fixture() {
    assert_eq!(actual_recovery_vectors(), expected_recovery_vectors());
}

#[test]
fn tampered_recovery_vectors_are_rejected_by_exact_fixture_comparison() {
    let actual = actual_recovery_vectors();

    let mut tampered_bounds = expected_recovery_vectors();
    tampered_bounds["route_bounds"]["recovery_bound_steps_after_latest_epoch"] = json!(3);
    assert_ne!(actual, tampered_bounds);

    let mut tampered_summary = expected_recovery_vectors();
    tampered_summary["route_bounds"]["selected_result_summary"]["traversed_epoch_count"] = json!(1);
    assert_ne!(actual, tampered_summary);

    let mut tampered_discovery_certificate = expected_recovery_vectors();
    tampered_discovery_certificate["route_bounds"]["path_problem"]["discovery_certificate"]
        ["class"] = json!("GoalWindowOneStepViaThreadedRefinement");
    assert_ne!(actual, tampered_discovery_certificate);

    let mut tampered_observation = expected_recovery_vectors();
    tampered_observation["observation"]["graph_epoch_trace"] = json!([1]);
    assert_ne!(actual, tampered_observation);
}
