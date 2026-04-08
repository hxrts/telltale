#![allow(clippy::expect_used, missing_docs)]

mod support;

use std::num::NonZeroU64;

use support::FixtureDomain;
#[cfg(not(feature = "multi-thread"))]
use telltale_search::NativeParallelExecutorError;
use telltale_search::{
    classify_scheduler_artifact, commit_epoch_reconfiguration, compare_observations,
    proposals_independent, replay_observation, run_with_executor, AuthorityReadSet,
    AuthoritySurface, AuthorityWriteSet, EpochReconfigurationRequest, EpsilonMilli,
    NativeParallelExecutor, ObservationRelation, Proposal, ProposalKind, ReplayError,
    ReplayExpectation, SchedulerArtifactClass, SearchDeterminismMode, SearchError,
    SearchFairnessAssumption, SearchMachine, SearchObservableClass, SearchRunConfig,
    SearchSchedulerProfile, SerialProposalExecutor, TotalStepMode,
};

fn make_domain() -> FixtureDomain {
    let mut domain = FixtureDomain::default();
    domain.edge(0, 1, "0-1", 1);
    domain.edge(0, 2, "0-2", 1);
    domain.edge(1, 3, "1-3", 1);
    domain.edge(2, 3, "2-3", 1);
    domain.heuristic_value(1, 1, 0);
    domain.heuristic_value(1, 2, 0);
    domain.heuristic_value(2, 1, 1);
    domain.heuristic_value(2, 2, 0);
    domain
}

#[cfg(feature = "multi-thread")]
fn native_executor(batch_width: u64) -> NativeParallelExecutor {
    NativeParallelExecutor::new(NonZeroU64::new(batch_width).expect("non-zero batch width"))
        .expect("native executor")
}

fn run_config(
    scheduler_profile: SearchSchedulerProfile,
    batch_width: u64,
    fairness: &[SearchFairnessAssumption],
) -> SearchRunConfig {
    SearchRunConfig {
        scheduler_profile,
        batch_width,
        fairness_assumptions: fairness.iter().copied().collect(),
    }
}

fn make_failing_runtime_domain() -> FixtureDomain {
    let mut domain = FixtureDomain {
        fail_node: Some(1),
        ..Default::default()
    };
    domain.edge(0, 1, "0-1", 1);
    domain.edge(0, 2, "0-2", 1);
    domain.edge(1, 3, "1-3", 1);
    domain.edge(2, 4, "2-4", 1);
    domain
}

#[cfg(not(feature = "multi-thread"))]
#[test]
fn native_parallel_executor_requires_the_multi_thread_feature() {
    let err = NativeParallelExecutor::new(NonZeroU64::new(1).expect("non-zero"))
        .expect_err("missing feature");
    assert_eq!(err, NativeParallelExecutorError::MissingMultiThreadFeature);
}

#[cfg(feature = "multi-thread")]
#[test]
fn serial_and_parallel_batch_width_one_are_exactly_equal() {
    let domain = make_domain();
    let mut left = SearchMachine::new(domain.clone(), 1, 0, 3, EpsilonMilli::one());
    let mut right = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
    let (left_report, _) = run_with_executor(
        &mut left,
        &SerialProposalExecutor,
        run_config(
            SearchSchedulerProfile::CanonicalSerial,
            1,
            &[SearchFairnessAssumption::DeterministicSchedulerConfluence],
        ),
    )
    .expect("serial run");
    let (right_report, _) = run_with_executor(
        &mut right,
        &native_executor(1),
        run_config(
            SearchSchedulerProfile::ThreadedExactSingleLane,
            1,
            &[SearchFairnessAssumption::DeterministicSchedulerConfluence],
        ),
    )
    .expect("parallel run");
    assert_eq!(
        left_report.observation.incumbent_cost,
        right_report.observation.incumbent_cost
    );
    assert_eq!(
        left_report.observation.incumbent_path,
        right_report.observation.incumbent_path
    );
    assert_eq!(
        left_report.observation.normalized_commit_trace,
        right_report.observation.normalized_commit_trace
    );
    assert_eq!(right_report.progress.total_step_mode, TotalStepMode::Exact);
    assert_eq!(
        classify_scheduler_artifact(SearchSchedulerProfile::ThreadedExactSingleLane),
        SchedulerArtifactClass::Exact
    );
}

#[cfg(feature = "multi-thread")]
#[test]
fn parallel_executor_processes_the_full_legal_batch_window() {
    let mut domain = FixtureDomain::default();
    domain.edge(0, 1, "0-1", 1);
    domain.edge(0, 2, "0-2", 1);
    domain.edges.insert(1, vec![]);
    domain.edge(2, 3, "2-3", 1);

    let mut machine = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
    let (report, _) = run_with_executor(
        &mut machine,
        &native_executor(1),
        run_config(
            SearchSchedulerProfile::ThreadedExactSingleLane,
            1,
            &[SearchFairnessAssumption::DeterministicSchedulerConfluence],
        ),
    )
    .expect("parallel run");

    assert_eq!(report.observation.incumbent_cost, Some(2));
    assert_eq!(report.observation.incumbent_path, Some(vec![0, 2, 3]));
}

#[cfg(feature = "multi-thread")]
#[test]
fn parallel_envelope_run_is_admitted_modulo_commutativity() {
    let domain = make_domain();
    let mut serial = SearchMachine::new(domain.clone(), 1, 0, 3, EpsilonMilli::one());
    let mut parallel = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
    let (serial_report, _) = run_with_executor(
        &mut serial,
        &SerialProposalExecutor,
        run_config(
            SearchSchedulerProfile::CanonicalSerial,
            1,
            &[SearchFairnessAssumption::DeterministicSchedulerConfluence],
        ),
    )
    .expect("serial run");
    let (parallel_report, _) = run_with_executor(
        &mut parallel,
        &native_executor(2),
        run_config(
            SearchSchedulerProfile::BatchedParallelEnvelopeBounded,
            2,
            &[
                SearchFairnessAssumption::DeterministicSchedulerConfluence,
                SearchFairnessAssumption::NoStarvationWithinLegalWindow,
            ],
        ),
    )
    .expect("parallel run");
    let comparison = compare_observations(
        &serial_report.observation,
        &parallel_report.observation,
        SearchDeterminismMode::ModuloCommutativity,
        &[
            SearchObservableClass::IncumbentCost,
            SearchObservableClass::CanonicalPathIdentity,
            SearchObservableClass::NormalizedCommitTrace,
        ],
    );
    assert!(matches!(
        comparison.relation,
        ObservationRelation::Exact | ObservationRelation::EquivalentModuloCommutativity
    ));
    assert_eq!(
        parallel_report.progress.total_step_mode,
        TotalStepMode::FairnessBounded
    );
    assert_eq!(
        parallel_report.scheduler.authority_class,
        SchedulerArtifactClass::Normalized
    );
}

#[cfg(feature = "multi-thread")]
#[test]
fn fairness_free_exact_claims_are_distinct_from_fairness_bounded_claims() {
    let domain = make_domain();
    let mut machine = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
    let (report, _) = run_with_executor(
        &mut machine,
        &native_executor(2),
        run_config(
            SearchSchedulerProfile::BatchedParallelEnvelopeBounded,
            2,
            &[SearchFairnessAssumption::EventualLiveBatchService],
        ),
    )
    .expect("parallel run");
    assert_eq!(
        report.progress.total_step_mode,
        TotalStepMode::FairnessBounded
    );
    assert_eq!(
        report.progress.productive_steps,
        report.observation.productive_steps
    );
    assert_ne!(
        report.progress.fairness_assumptions,
        [SearchFairnessAssumption::DeterministicSchedulerConfluence]
            .into_iter()
            .collect()
    );
}

#[test]
fn reconfiguration_commits_new_epoch_at_barrier() {
    let domain = make_domain();
    let mut machine = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
    machine.run_to_completion().expect("search run");
    assert!(machine.state().incumbent.is_some());
    commit_epoch_reconfiguration(&mut machine, EpochReconfigurationRequest { next_epoch: 2 });
    let observation = machine.observation_artifact(
        SearchSchedulerProfile::CanonicalSerial,
        [SearchFairnessAssumption::DeterministicSchedulerConfluence]
            .into_iter()
            .collect(),
    );
    assert_eq!(machine.state().phase, 1);
    assert_eq!(machine.state().graph_epoch, 2);
    assert_eq!(observation.graph_epoch_trace, vec![1, 2]);
    assert_eq!(machine.state().g_score.get(&0), Some(&0));
    assert_eq!(machine.state().g_score.len(), 1);
    assert!(machine.state().parent.is_empty());
    assert!(machine.state().incumbent.is_none());
}

#[test]
fn executor_failure_does_not_consume_the_current_batch() {
    let mut machine =
        SearchMachine::new(make_failing_runtime_domain(), 1, 0, 4, EpsilonMilli::one());
    machine.step_once().expect("first canonical step");
    let before_failure = machine.state().clone();

    let err = run_with_executor(
        &mut machine,
        &SerialProposalExecutor,
        run_config(
            SearchSchedulerProfile::CanonicalSerial,
            1,
            &[SearchFairnessAssumption::DeterministicSchedulerConfluence],
        ),
    )
    .expect_err("failing batch");

    assert_eq!(err, SearchError::Domain("boom"));
    assert_eq!(&before_failure, machine.state());
}

#[test]
fn replay_rejects_mismatched_epoch_schedule() {
    let domain = make_domain();
    let mut machine = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
    let (_, replay) = run_with_executor(
        &mut machine,
        &SerialProposalExecutor,
        run_config(
            SearchSchedulerProfile::CanonicalSerial,
            1,
            &[SearchFairnessAssumption::DeterministicSchedulerConfluence],
        ),
    )
    .expect("serial run");
    let err = replay_observation(
        &replay,
        &ReplayExpectation {
            expected_epochs: vec![1, 2],
            expected_phases: replay.rounds.iter().map(|round| round.phase).collect(),
            required_fairness: [SearchFairnessAssumption::DeterministicSchedulerConfluence]
                .into_iter()
                .collect(),
        },
    )
    .expect_err("mismatched epochs");
    assert_eq!(err, ReplayError::EpochSchedule);
}

#[cfg(feature = "multi-thread")]
#[test]
fn replay_rejects_mismatched_phase_or_fairness_premises() {
    let domain = make_domain();
    let mut machine = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
    let (_, replay) = run_with_executor(
        &mut machine,
        &native_executor(2),
        run_config(
            SearchSchedulerProfile::BatchedParallelEnvelopeBounded,
            2,
            &[SearchFairnessAssumption::EventualLiveBatchService],
        ),
    )
    .expect("parallel run");

    let phase_err = replay_observation(
        &replay,
        &ReplayExpectation {
            expected_epochs: replay.epoch_trace.clone(),
            expected_phases: vec![999],
            required_fairness: [SearchFairnessAssumption::EventualLiveBatchService]
                .into_iter()
                .collect(),
        },
    )
    .expect_err("mismatched phases");
    assert_eq!(phase_err, ReplayError::PhaseSchedule);

    let fairness_err = replay_observation(
        &replay,
        &ReplayExpectation {
            expected_epochs: replay.epoch_trace.clone(),
            expected_phases: replay.rounds.iter().map(|round| round.phase).collect(),
            required_fairness: [SearchFairnessAssumption::DeterministicSchedulerConfluence]
                .into_iter()
                .collect(),
        },
    )
    .expect_err("mismatched fairness bundle");
    assert_eq!(fairness_err, ReplayError::FairnessBundle);
}

#[test]
fn replay_rejects_observation_drift() {
    let domain = make_domain();
    let mut machine = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
    let (_, mut replay) = run_with_executor(
        &mut machine,
        &SerialProposalExecutor,
        run_config(
            SearchSchedulerProfile::CanonicalSerial,
            1,
            &[SearchFairnessAssumption::DeterministicSchedulerConfluence],
        ),
    )
    .expect("serial run");
    replay.final_observation.total_scheduler_steps += 1;
    let err = replay_observation(
        &replay,
        &ReplayExpectation {
            expected_epochs: replay.epoch_trace.clone(),
            expected_phases: replay.rounds.iter().map(|round| round.phase).collect(),
            required_fairness: [SearchFairnessAssumption::DeterministicSchedulerConfluence]
                .into_iter()
                .collect(),
        },
    )
    .expect_err("observation drift");
    assert_eq!(err, ReplayError::ObservationArtifact);
}

#[test]
fn goal_targeting_proposals_conflict_on_incumbent_surface() {
    let left = Proposal {
        batch_index: 0,
        from: 1,
        to: 4,
        edge: "1-4",
        edge_cost: 1_u64,
        tentative_g: 2_u64,
        kind: ProposalKind::Relax,
        read_set: AuthorityReadSet {
            target_nodes: [1, 4].into_iter().collect(),
            surfaces: [
                AuthoritySurface::BatchWindow,
                AuthoritySurface::GraphEpoch,
                AuthoritySurface::Phase,
            ]
            .into_iter()
            .collect(),
        },
        write_set: AuthorityWriteSet {
            target_nodes: [4].into_iter().collect(),
            surfaces: [AuthoritySurface::Incumbent].into_iter().collect(),
        },
    };
    let right = Proposal {
        batch_index: 1,
        from: 2,
        to: 4,
        edge: "2-4",
        edge_cost: 1_u64,
        tentative_g: 2_u64,
        kind: ProposalKind::Relax,
        read_set: AuthorityReadSet {
            target_nodes: [2, 4].into_iter().collect(),
            surfaces: [
                AuthoritySurface::BatchWindow,
                AuthoritySurface::GraphEpoch,
                AuthoritySurface::Phase,
            ]
            .into_iter()
            .collect(),
        },
        write_set: AuthorityWriteSet {
            target_nodes: [4].into_iter().collect(),
            surfaces: [AuthoritySurface::Incumbent].into_iter().collect(),
        },
    };

    assert!(!proposals_independent(&left, &right));
}
