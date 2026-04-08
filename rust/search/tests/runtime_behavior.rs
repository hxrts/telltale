#![allow(clippy::expect_used, missing_docs)]

mod support;

use std::num::NonZeroU64;

use support::{FixtureDomain, UnstableOrderDomain};
#[cfg(not(feature = "multi-thread"))]
use telltale_search::NativeParallelExecutorError;
#[cfg(feature = "multi-thread")]
use telltale_search::{
    classify_scheduler_artifact, compare_observations, ObservationRelation, SchedulerArtifactClass,
    SearchDeterminismMode, SearchObservableClass, TotalStepMode,
};
use telltale_search::{
    commit_epoch_reconfiguration, proposals_independent, replay_observation, run_with_executor,
    validate_run_config, AuthorityReadSet, AuthoritySurface, AuthorityWriteSet,
    EpochReconfigurationRequest, EpsilonMilli, NativeParallelExecutor, Proposal, ProposalKind,
    ReplayError, ReplayExpectation, SearchError, SearchFairnessAssumption, SearchMachine,
    SearchRunConfig, SearchRunConfigError, SearchRunError, SearchSchedulerProfile,
    SerialProposalExecutor,
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

fn make_unstable_domain() -> UnstableOrderDomain {
    let mut domain = UnstableOrderDomain::default();
    domain.edge(0, 1, "0-1", 1);
    domain.edge(0, 2, "0-2", 1);
    domain.edge(1, 3, "1-3", 1);
    domain.edge(2, 3, "2-3", 1);
    domain.heuristic_value(1, 1, 0);
    domain.heuristic_value(1, 2, 0);
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
                SearchFairnessAssumption::EventualLiveBatchService,
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
fn envelope_profile_requires_the_declared_fairness_bundle() {
    let domain = make_domain();
    let mut machine = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
    let err = run_with_executor(
        &mut machine,
        &native_executor(2),
        run_config(
            SearchSchedulerProfile::BatchedParallelEnvelopeBounded,
            2,
            &[SearchFairnessAssumption::EventualLiveBatchService],
        ),
    )
    .expect_err("parallel run must fail closed without the full fairness bundle");
    assert_eq!(
        err,
        SearchRunError::InvalidConfig(SearchRunConfigError::MissingFairnessAssumption {
            profile: SearchSchedulerProfile::BatchedParallelEnvelopeBounded,
            assumption: SearchFairnessAssumption::NoStarvationWithinLegalWindow,
        })
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

    assert_eq!(err, SearchRunError::Search(SearchError::Domain("boom")));
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
            expected_snapshots: replay
                .rounds
                .iter()
                .map(|round| round.snapshot_id)
                .collect(),
            expected_phases: replay.rounds.iter().map(|round| round.phase).collect(),
            expected_batch_nodes: replay
                .rounds
                .iter()
                .map(|round| round.batch_nodes.clone())
                .collect(),
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
            &[
                SearchFairnessAssumption::EventualLiveBatchService,
                SearchFairnessAssumption::NoStarvationWithinLegalWindow,
            ],
        ),
    )
    .expect("parallel run");

    let phase_err = replay_observation(
        &replay,
        &ReplayExpectation {
            expected_epochs: replay.epoch_trace.clone(),
            expected_snapshots: replay
                .rounds
                .iter()
                .map(|round| round.snapshot_id)
                .collect(),
            expected_phases: vec![999],
            expected_batch_nodes: replay
                .rounds
                .iter()
                .map(|round| round.batch_nodes.clone())
                .collect(),
            required_fairness: [
                SearchFairnessAssumption::EventualLiveBatchService,
                SearchFairnessAssumption::NoStarvationWithinLegalWindow,
            ]
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
            expected_snapshots: replay
                .rounds
                .iter()
                .map(|round| round.snapshot_id)
                .collect(),
            expected_phases: replay.rounds.iter().map(|round| round.phase).collect(),
            expected_batch_nodes: replay
                .rounds
                .iter()
                .map(|round| round.batch_nodes.clone())
                .collect(),
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
            expected_snapshots: replay
                .rounds
                .iter()
                .map(|round| round.snapshot_id)
                .collect(),
            expected_phases: replay.rounds.iter().map(|round| round.phase).collect(),
            expected_batch_nodes: replay
                .rounds
                .iter()
                .map(|round| round.batch_nodes.clone())
                .collect(),
            required_fairness: [SearchFairnessAssumption::DeterministicSchedulerConfluence]
                .into_iter()
                .collect(),
        },
    )
    .expect_err("observation drift");
    assert_eq!(err, ReplayError::ObservationArtifact);
}

#[test]
fn canonical_serial_rejects_zero_batch_width() {
    let config = run_config(
        SearchSchedulerProfile::CanonicalSerial,
        0,
        &[SearchFairnessAssumption::DeterministicSchedulerConfluence],
    );
    let err = validate_run_config::<FixtureDomain, _>(&SerialProposalExecutor, &config)
        .expect_err("zero batch width must fail");
    assert_eq!(err, SearchRunConfigError::ZeroBatchWidth);
}

#[test]
fn canonical_serial_rejects_non_serial_profile_shape() {
    let config = run_config(
        SearchSchedulerProfile::CanonicalSerial,
        2,
        &[SearchFairnessAssumption::DeterministicSchedulerConfluence],
    );
    let err = validate_run_config::<FixtureDomain, _>(&SerialProposalExecutor, &config)
        .expect_err("canonical serial must require batch width one");
    assert_eq!(
        err,
        SearchRunConfigError::RequiresBatchWidthOne(SearchSchedulerProfile::CanonicalSerial)
    );
}

#[cfg(feature = "multi-thread")]
#[test]
fn threaded_exact_single_lane_rejects_width_greater_than_one() {
    let err = validate_run_config::<FixtureDomain, _>(
        &native_executor(2),
        &run_config(
            SearchSchedulerProfile::ThreadedExactSingleLane,
            2,
            &[SearchFairnessAssumption::DeterministicSchedulerConfluence],
        ),
    )
    .expect_err("exact single-lane must reject width > 1");
    assert_eq!(
        err,
        SearchRunConfigError::RequiresBatchWidthOne(
            SearchSchedulerProfile::ThreadedExactSingleLane
        )
    );
}

#[cfg(feature = "multi-thread")]
#[test]
fn batched_parallel_exact_rejects_missing_exactness_prerequisite() {
    let err = validate_run_config::<FixtureDomain, _>(
        &native_executor(2),
        &run_config(SearchSchedulerProfile::BatchedParallelExact, 2, &[]),
    )
    .expect_err("exact batched runs must require deterministic confluence");
    assert_eq!(
        err,
        SearchRunConfigError::MissingFairnessAssumption {
            profile: SearchSchedulerProfile::BatchedParallelExact,
            assumption: SearchFairnessAssumption::DeterministicSchedulerConfluence,
        }
    );
}

#[cfg(feature = "multi-thread")]
#[test]
fn scheduler_profile_rejects_executor_kind_mismatches() {
    let serial_err = validate_run_config::<FixtureDomain, _>(
        &SerialProposalExecutor,
        &run_config(
            SearchSchedulerProfile::ThreadedExactSingleLane,
            1,
            &[SearchFairnessAssumption::DeterministicSchedulerConfluence],
        ),
    )
    .expect_err("threaded exact single-lane must require native parallel executor");
    assert_eq!(
        serial_err,
        SearchRunConfigError::RequiresNativeParallelExecutor(
            SearchSchedulerProfile::ThreadedExactSingleLane
        )
    );

    let exact_err = validate_run_config::<FixtureDomain, _>(
        &SerialProposalExecutor,
        &run_config(
            SearchSchedulerProfile::CanonicalSerial,
            1,
            &[SearchFairnessAssumption::DeterministicSchedulerConfluence],
        ),
    );
    assert!(exact_err.is_ok());
}

#[test]
fn replay_rejects_mismatched_snapshot_schedule() {
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
            expected_epochs: replay.epoch_trace.clone(),
            expected_snapshots: vec!["wrong-snapshot"],
            expected_phases: replay.rounds.iter().map(|round| round.phase).collect(),
            expected_batch_nodes: replay
                .rounds
                .iter()
                .map(|round| round.batch_nodes.clone())
                .collect(),
            required_fairness: [SearchFairnessAssumption::DeterministicSchedulerConfluence]
                .into_iter()
                .collect(),
        },
    )
    .expect_err("mismatched snapshots");
    assert_eq!(err, ReplayError::SnapshotSchedule);
}

#[test]
fn replay_rejects_mismatched_batch_schedule() {
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
            expected_epochs: replay.epoch_trace.clone(),
            expected_snapshots: replay
                .rounds
                .iter()
                .map(|round| round.snapshot_id)
                .collect(),
            expected_phases: replay.rounds.iter().map(|round| round.phase).collect(),
            expected_batch_nodes: vec![vec![9]],
            required_fairness: [SearchFairnessAssumption::DeterministicSchedulerConfluence]
                .into_iter()
                .collect(),
        },
    )
    .expect_err("mismatched batch schedule");
    assert_eq!(err, ReplayError::BatchSchedule);
}

#[test]
fn replay_rejects_tampered_round_commits() {
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
    replay.rounds[0].commits[0].g_score += 7;
    let err = replay_observation(
        &replay,
        &ReplayExpectation {
            expected_epochs: replay.epoch_trace.clone(),
            expected_snapshots: replay
                .rounds
                .iter()
                .map(|round| round.snapshot_id)
                .collect(),
            expected_phases: replay.rounds.iter().map(|round| round.phase).collect(),
            expected_batch_nodes: replay
                .rounds
                .iter()
                .map(|round| round.batch_nodes.clone())
                .collect(),
            required_fairness: [SearchFairnessAssumption::DeterministicSchedulerConfluence]
                .into_iter()
                .collect(),
        },
    )
    .expect_err("tampered commits");
    assert_eq!(err, ReplayError::ObservationArtifact);
}

#[test]
fn serial_executor_stabilizes_observation_under_unstable_successor_order() {
    let mut left = SearchMachine::new(make_unstable_domain(), 1, 0, 3, EpsilonMilli::one());
    let mut right = SearchMachine::new(make_unstable_domain(), 1, 0, 3, EpsilonMilli::one());
    let (left_report, _) = run_with_executor(
        &mut left,
        &SerialProposalExecutor,
        run_config(
            SearchSchedulerProfile::CanonicalSerial,
            1,
            &[SearchFairnessAssumption::DeterministicSchedulerConfluence],
        ),
    )
    .expect("left serial run");
    let (right_report, _) = run_with_executor(
        &mut right,
        &SerialProposalExecutor,
        run_config(
            SearchSchedulerProfile::CanonicalSerial,
            1,
            &[SearchFairnessAssumption::DeterministicSchedulerConfluence],
        ),
    )
    .expect("right serial run");
    assert_eq!(left_report.observation, right_report.observation);
}

#[cfg(feature = "multi-thread")]
#[test]
fn native_parallel_executor_stabilizes_observation_under_unstable_successor_order() {
    let mut left = SearchMachine::new(make_unstable_domain(), 1, 0, 3, EpsilonMilli::one());
    let mut right = SearchMachine::new(make_unstable_domain(), 1, 0, 3, EpsilonMilli::one());
    let fairness = [SearchFairnessAssumption::DeterministicSchedulerConfluence];
    let (left_report, _) = run_with_executor(
        &mut left,
        &native_executor(1),
        run_config(
            SearchSchedulerProfile::ThreadedExactSingleLane,
            1,
            &fairness,
        ),
    )
    .expect("left threaded run");
    let (right_report, _) = run_with_executor(
        &mut right,
        &native_executor(1),
        run_config(
            SearchSchedulerProfile::ThreadedExactSingleLane,
            1,
            &fairness,
        ),
    )
    .expect("right threaded run");
    assert_eq!(left_report.observation, right_report.observation);
}

#[cfg(feature = "multi-thread")]
#[test]
fn exact_and_envelope_profiles_report_the_expected_scheduler_classes() {
    let domain = make_domain();
    let fairness_exact = [SearchFairnessAssumption::DeterministicSchedulerConfluence];
    let fairness_envelope = [
        SearchFairnessAssumption::EventualLiveBatchService,
        SearchFairnessAssumption::NoStarvationWithinLegalWindow,
    ];

    let mut exact_machine = SearchMachine::new(domain.clone(), 1, 0, 3, EpsilonMilli::one());
    let (exact_report, _) = run_with_executor(
        &mut exact_machine,
        &native_executor(2),
        run_config(
            SearchSchedulerProfile::BatchedParallelExact,
            2,
            &fairness_exact,
        ),
    )
    .expect("exact batched run");
    assert_eq!(
        exact_report.scheduler.authority_class,
        SchedulerArtifactClass::Exact
    );
    assert_eq!(exact_report.progress.total_step_mode, TotalStepMode::Exact);

    let mut envelope_machine = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
    let (envelope_report, _) = run_with_executor(
        &mut envelope_machine,
        &native_executor(2),
        run_config(
            SearchSchedulerProfile::BatchedParallelEnvelopeBounded,
            2,
            &fairness_envelope,
        ),
    )
    .expect("envelope batched run");
    assert_eq!(
        envelope_report.scheduler.authority_class,
        SchedulerArtifactClass::Normalized
    );
    assert_eq!(
        envelope_report.progress.total_step_mode,
        TotalStepMode::FairnessBounded
    );
}

#[cfg(feature = "multi-thread")]
#[test]
fn exact_batched_parallel_profile_matches_serial_on_exact_observables() {
    let domain = make_domain();
    let mut serial = SearchMachine::new(domain.clone(), 1, 0, 3, EpsilonMilli::one());
    let mut exact = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
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
    let (exact_report, _) = run_with_executor(
        &mut exact,
        &native_executor(2),
        run_config(
            SearchSchedulerProfile::BatchedParallelExact,
            2,
            &[SearchFairnessAssumption::DeterministicSchedulerConfluence],
        ),
    )
    .expect("exact batched run");
    let comparison = compare_observations(
        &serial_report.observation,
        &exact_report.observation,
        SearchDeterminismMode::Full,
        &[
            SearchObservableClass::IncumbentCost,
            SearchObservableClass::CanonicalPathIdentity,
            SearchObservableClass::NormalizedCommitTrace,
        ],
    );
    assert_eq!(comparison.relation, ObservationRelation::Exact);
}

#[test]
fn reconfiguration_preserves_progress_accounting_but_resets_search_state() {
    let domain = make_domain();
    let mut machine = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
    machine.step_once().expect("first step");
    let before_productive = machine.state().trace_state.productive_steps;
    let before_total = machine.state().trace_state.total_scheduler_steps;
    commit_epoch_reconfiguration(&mut machine, EpochReconfigurationRequest { next_epoch: 2 });
    assert_eq!(
        machine.state().trace_state.productive_steps,
        before_productive
    );
    assert_eq!(
        machine.state().trace_state.total_scheduler_steps,
        before_total
    );
    assert!(machine.state().closed.is_empty());
    assert!(machine.state().incons.is_empty());
    assert!(machine.state().parent.is_empty());
    assert!(machine.state().incumbent.is_none());
    assert_eq!(machine.state().open.len(), 1);
}

#[test]
fn replay_artifact_records_epoch_barrier_exactly_once_across_reconfiguration() {
    let domain = make_domain();
    let mut machine = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
    machine.step_once().expect("first step");
    commit_epoch_reconfiguration(&mut machine, EpochReconfigurationRequest { next_epoch: 2 });
    let (_, replay) = run_with_executor(
        &mut machine,
        &SerialProposalExecutor,
        run_config(
            SearchSchedulerProfile::CanonicalSerial,
            1,
            &[SearchFairnessAssumption::DeterministicSchedulerConfluence],
        ),
    )
    .expect("post-reconfiguration run");
    assert_eq!(replay.epoch_trace, vec![1, 2]);
}

#[cfg(feature = "multi-thread")]
#[test]
fn parallel_width_variants_preserve_authoritative_results() {
    let domain = make_domain();
    let fairness_exact = [SearchFairnessAssumption::DeterministicSchedulerConfluence];
    let fairness_envelope = [
        SearchFairnessAssumption::EventualLiveBatchService,
        SearchFairnessAssumption::NoStarvationWithinLegalWindow,
    ];

    let mut serial = SearchMachine::new(domain.clone(), 1, 0, 3, EpsilonMilli::one());
    let (serial_report, serial_replay) = run_with_executor(
        &mut serial,
        &SerialProposalExecutor,
        run_config(SearchSchedulerProfile::CanonicalSerial, 1, &fairness_exact),
    )
    .expect("serial run");

    for width in [1_u64, 2, 8] {
        let mut machine = SearchMachine::new(domain.clone(), 1, 0, 3, EpsilonMilli::one());
        let (report, replay) = if width == 1 {
            run_with_executor(
                &mut machine,
                &native_executor(width),
                run_config(
                    SearchSchedulerProfile::ThreadedExactSingleLane,
                    width,
                    &fairness_exact,
                ),
            )
        } else {
            run_with_executor(
                &mut machine,
                &native_executor(width),
                run_config(
                    SearchSchedulerProfile::BatchedParallelEnvelopeBounded,
                    width,
                    &fairness_envelope,
                ),
            )
        }
        .expect("parallel run");

        assert_eq!(
            report.observation.incumbent_cost,
            serial_report.observation.incumbent_cost
        );
        assert_eq!(
            report.observation.incumbent_path,
            serial_report.observation.incumbent_path
        );
        assert_eq!(
            replay.final_observation.incumbent_cost,
            serial_replay.final_observation.incumbent_cost
        );
        let comparison = compare_observations(
            &serial_report.observation,
            &report.observation,
            if width == 1 {
                SearchDeterminismMode::Full
            } else {
                SearchDeterminismMode::ModuloCommutativity
            },
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
    }
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
