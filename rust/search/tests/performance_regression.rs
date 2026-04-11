#![allow(clippy::expect_used, missing_docs)]

mod support;

use telltale_search::{
    commit_epoch_reconfiguration, run_with_executor, EpochReconfigurationRequest, EpsilonMilli,
    SearchExecutionPolicy, SearchFairnessAssumption, SearchMachine, SearchReseedingPolicy,
    SearchRunConfig, SearchSchedulerProfile, SerialProposalExecutor,
};

use support::FixtureDomain;

fn run_config() -> SearchRunConfig {
    SearchRunConfig::new(
        SearchExecutionPolicy::new(SearchSchedulerProfile::CanonicalSerial, 1),
        [SearchFairnessAssumption::DeterministicSchedulerConfluence]
            .into_iter()
            .collect(),
    )
}

#[test]
fn chain_graph_has_stable_step_commit_and_publication_counts() {
    let mut domain = FixtureDomain::default();
    domain.edge(0, 1, "0-1", 1);
    domain.edge(1, 2, "1-2", 1);
    domain.edge(2, 3, "2-3", 1);

    let mut machine = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
    let (report, replay) =
        run_with_executor(&mut machine, &SerialProposalExecutor, run_config()).expect("chain run");

    assert_eq!(report.progress.productive_steps, 3);
    assert_eq!(report.progress.total_scheduler_steps, 4);
    assert_eq!(report.observation.normalized_commit_trace.len(), 3);
    assert_eq!(
        report.observation.selected_result_publication_trace.len(),
        1
    );
    assert_eq!(replay.rounds.len(), 4);
}

#[test]
fn fan_in_graph_has_stable_batch_commit_shape() {
    let mut domain = FixtureDomain::default();
    domain.edge(0, 1, "0-1", 1);
    domain.edge(0, 2, "0-2", 1);
    domain.edge(0, 3, "0-3", 1);
    domain.edge(1, 4, "1-4", 5);
    domain.edge(2, 4, "2-4", 2);
    domain.edge(3, 4, "3-4", 3);

    let mut machine = SearchMachine::new(domain, 1, 0, 4, EpsilonMilli::one());
    let (report, replay) =
        run_with_executor(&mut machine, &SerialProposalExecutor, run_config()).expect("fan-in run");

    assert_eq!(report.progress.productive_steps, 2);
    assert_eq!(report.progress.total_scheduler_steps, 3);
    assert_eq!(report.observation.normalized_commit_trace.len(), 4);
    assert_eq!(
        report.observation.selected_result_publication_trace.len(),
        1
    );
    assert_eq!(replay.rounds[0].commits.len(), 3);
    assert_eq!(replay.rounds[1].commits.len(), 1);
    assert_eq!(replay.rounds[2].commits.len(), 0);
}

#[test]
fn cyclic_trap_graph_has_stable_commit_and_publication_counts() {
    let mut domain = FixtureDomain::default();
    domain.edge(0, 1, "0-1", 1);
    domain.edge(1, 2, "1-2", 1);
    domain.edge(2, 1, "2-1", 1);
    domain.edge(2, 3, "2-3", 1);

    let mut machine = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
    let (report, replay) =
        run_with_executor(&mut machine, &SerialProposalExecutor, run_config()).expect("cyclic run");

    assert_eq!(report.progress.productive_steps, 3);
    assert_eq!(report.progress.total_scheduler_steps, 4);
    assert_eq!(report.observation.normalized_commit_trace.len(), 3);
    assert_eq!(
        report.observation.selected_result_publication_trace.len(),
        1
    );
    assert_eq!(replay.rounds.len(), 4);
}

#[test]
fn reconfiguration_run_has_stable_epoch_and_commit_accounting() {
    let mut domain = FixtureDomain::default();
    domain.edge(0, 1, "0-1", 1);
    domain.edge(1, 2, "1-2", 1);

    let mut machine = SearchMachine::new(domain, 1, 0, 2, EpsilonMilli::one());
    machine.step_once().expect("initial pre-barrier step");
    commit_epoch_reconfiguration(
        &mut machine,
        EpochReconfigurationRequest {
            next_epoch: 2,
            reseeding_policy: SearchReseedingPolicy::StartOnly,
        },
    );
    let (report, replay) = run_with_executor(&mut machine, &SerialProposalExecutor, run_config())
        .expect("reconfigured run");

    assert_eq!(report.observation.graph_epoch_trace, vec![1, 2]);
    assert_eq!(report.progress.productive_steps, 3);
    assert_eq!(report.progress.total_scheduler_steps, 4);
    assert_eq!(report.observation.normalized_commit_trace.len(), 3);
    assert_eq!(
        report.observation.selected_result_publication_trace.len(),
        1
    );
    assert_eq!(replay.epoch_trace, vec![1, 2]);
}
