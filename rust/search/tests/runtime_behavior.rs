#![allow(clippy::expect_used, missing_docs)]

mod support;

use std::num::NonZeroU64;

use support::{FixtureDomain, UnstableOrderDomain};
#[cfg(not(feature = "multi-thread"))]
use telltale_search::NativeParallelExecutorError;
use telltale_search::{
    classify_fairness_claim, commit_epoch_reconfiguration, fairness_artifact_for_profile,
    proposals_independent, replay_observation, run_with_executor, search_theorem_pack_artifact,
    theorem_backed_observables, validate_fairness_certificate_trace, validate_run_config,
    AuthorityReadSet, AuthoritySurface, AuthorityWriteSet, EpochReconfigurationRequest,
    EpsilonMilli, NativeParallelExecutor, Proposal, ProposalKind, ReplayError, ReplayExpectation,
    SearchDeterminismMode, SearchError, SearchFairnessAssumption, SearchFairnessCertificateClass,
    SearchFairnessClaimClass, SearchFairnessTraceValidationError, SearchMachine,
    SearchRouteDiscoveryBoundClass, SearchRouteDiscoveryCertificateClass, SearchRouteMetricName,
    SearchRouteQualityClass, SearchRunConfig, SearchRunConfigError, SearchRunError,
    SearchSchedulerProfile, SerialProposalExecutor,
};
#[cfg(feature = "multi-thread")]
use telltale_search::{
    classify_scheduler_artifact, compare_observations, ObservationRelation, SchedulerArtifactClass,
    SearchObservableClass, TotalStepMode,
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
    assert_eq!(
        right_report.fairness.certificate.class,
        SearchFairnessCertificateClass::CurrentMinKeyBatchViaThreadedRefinement
    );
    assert!(right_report.fairness.exact_commit_trace_refines_canonical);
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
    assert_eq!(
        exact_report.fairness.certificate.class,
        SearchFairnessCertificateClass::CertifiedCurrentMinKeyWindow
    );
    assert_eq!(
        exact_report.fairness.certificate.service_bound_steps,
        Some(1)
    );

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
    assert_eq!(
        envelope_report.fairness.certificate.class,
        SearchFairnessCertificateClass::None
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
fn exact_profiles_emit_observed_candidate_bounds_and_exact_route_quality() {
    let mut machine = SearchMachine::new(make_domain(), 1, 0, 3, EpsilonMilli::one());
    let (report, replay) = run_with_executor(
        &mut machine,
        &SerialProposalExecutor,
        run_config(
            SearchSchedulerProfile::CanonicalSerial,
            1,
            &[SearchFairnessAssumption::DeterministicSchedulerConfluence],
        ),
    )
    .expect("canonical run");
    assert_eq!(
        report.route_bounds.discovery_class,
        SearchRouteDiscoveryBoundClass::ObservedRunBoundWithGoalWindowCertificate
    );
    assert_eq!(report.route_bounds.candidate_discovery_bound_steps, Some(2));
    assert_eq!(report.route_bounds.goal_service_bound_steps, Some(1));
    assert_eq!(report.route_bounds.goal_window_entry_bound_steps, Some(3));
    assert_eq!(
        report
            .route_bounds
            .discovery_certificate
            .as_ref()
            .map(|certificate| certificate.class),
        Some(SearchRouteDiscoveryCertificateClass::GoalWindowOneStepExact)
    );
    assert_eq!(
        report
            .route_bounds
            .discovery_certificate
            .as_ref()
            .map(|certificate| certificate.service_bound_steps),
        Some(1)
    );
    assert_eq!(
        report
            .route_bounds
            .discovery_certificate
            .as_ref()
            .map(|certificate| certificate.observed_goal_window_step),
        Some(3)
    );
    assert_eq!(
        report.route_bounds.recovery_bound_steps_after_latest_epoch,
        Some(2)
    );
    assert_eq!(
        report.route_bounds.quality_class,
        SearchRouteQualityClass::ExactOptimal
    );
    assert_eq!(report.route_bounds.selected_route_cost, Some(2));
    assert_eq!(report.route_bounds.optimality_gap, Some(0));
    assert_eq!(report.route_bounds.approximation_ratio_milli, Some(1_000));
    assert_eq!(report.route_bounds.admissible_upper_bound, Some(2));
    assert_eq!(
        report
            .route_bounds
            .selected_route_summary
            .as_ref()
            .map(|s| s.hop_count),
        Some(2)
    );
    assert_eq!(
        report
            .route_bounds
            .selected_route_summary
            .as_ref()
            .map(|s| s.publication_count),
        Some(1)
    );
    assert_eq!(
        report
            .route_bounds
            .selected_route_summary
            .as_ref()
            .map(|s| s.normalized_commit_count),
        Some(3)
    );
    assert_eq!(
        report
            .route_bounds
            .selected_route_summary
            .as_ref()
            .map(|s| s.traversed_epoch_count),
        Some(1)
    );
    assert_eq!(
        report
            .route_bounds
            .selected_route_summary
            .as_ref()
            .and_then(|s| {
                s.metrics
                    .iter()
                    .find(|metric| metric.name == SearchRouteMetricName::ScalarCostOrderKey)
                    .map(|metric| metric.value)
            }),
        Some(2)
    );
    assert_eq!(
        report
            .route_bounds
            .selected_route_summary
            .as_ref()
            .and_then(|s| {
                s.metrics
                    .iter()
                    .find(|metric| metric.name == SearchRouteMetricName::PathNodeCount)
                    .map(|metric| metric.value)
            }),
        Some(3)
    );
    assert_eq!(report.route_bounds, replay.route_bounds);
}

#[cfg(feature = "multi-thread")]
#[test]
fn non_exact_profiles_emit_weaker_route_quality_classes_but_keep_observed_discovery_bounds() {
    let mut exact_machine = SearchMachine::new(make_domain(), 1, 0, 3, EpsilonMilli::one());
    let (exact_report, _) = run_with_executor(
        &mut exact_machine,
        &native_executor(2),
        run_config(
            SearchSchedulerProfile::BatchedParallelExact,
            2,
            &[
                SearchFairnessAssumption::DeterministicSchedulerConfluence,
                SearchFairnessAssumption::EventualLiveBatchService,
                SearchFairnessAssumption::NoStarvationWithinLegalWindow,
            ],
        ),
    )
    .expect("exact batched run");
    assert_eq!(
        exact_report.route_bounds.discovery_class,
        SearchRouteDiscoveryBoundClass::ObservedRunBoundWithGoalWindowCertificate
    );
    assert_eq!(
        exact_report.route_bounds.candidate_discovery_bound_steps,
        Some(2)
    );
    assert_eq!(exact_report.route_bounds.goal_service_bound_steps, Some(1));
    assert_eq!(
        exact_report.route_bounds.goal_window_entry_bound_steps,
        Some(3)
    );
    assert_eq!(
        exact_report
            .route_bounds
            .discovery_certificate
            .as_ref()
            .map(|certificate| certificate.class),
        Some(SearchRouteDiscoveryCertificateClass::CertifiedGoalWindowService)
    );
    assert_eq!(
        exact_report
            .route_bounds
            .recovery_bound_steps_after_latest_epoch,
        Some(2)
    );
    assert_eq!(
        exact_report.route_bounds.quality_class,
        SearchRouteQualityClass::PremisedWindowBounded
    );
    assert_eq!(exact_report.route_bounds.selected_route_cost, Some(2));
    assert_eq!(exact_report.route_bounds.optimality_gap, None);
    assert_eq!(exact_report.route_bounds.approximation_ratio_milli, None);
    assert_eq!(exact_report.route_bounds.admissible_upper_bound, Some(2));
    assert_eq!(
        exact_report
            .route_bounds
            .selected_route_summary
            .as_ref()
            .map(|s| s.hop_count),
        Some(2)
    );
    assert_eq!(
        exact_report
            .route_bounds
            .selected_route_summary
            .as_ref()
            .map(|s| s.normalized_commit_count),
        Some(3)
    );
    assert_eq!(
        exact_report
            .route_bounds
            .selected_route_summary
            .as_ref()
            .and_then(|s| {
                s.metrics
                    .iter()
                    .find(|metric| metric.name == SearchRouteMetricName::HopCount)
                    .map(|metric| metric.value)
            }),
        Some(2)
    );

    let mut envelope_machine = SearchMachine::new(make_domain(), 1, 0, 3, EpsilonMilli::one());
    let (envelope_report, _) = run_with_executor(
        &mut envelope_machine,
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
    .expect("envelope run");
    assert_eq!(
        envelope_report.route_bounds.discovery_class,
        SearchRouteDiscoveryBoundClass::ObservedRunBound
    );
    assert_eq!(
        envelope_report.route_bounds.candidate_discovery_bound_steps,
        Some(2)
    );
    assert_eq!(envelope_report.route_bounds.goal_service_bound_steps, None);
    assert_eq!(
        envelope_report.route_bounds.goal_window_entry_bound_steps,
        Some(3)
    );
    assert_eq!(envelope_report.route_bounds.discovery_certificate, None);
    assert_eq!(
        envelope_report
            .route_bounds
            .recovery_bound_steps_after_latest_epoch,
        Some(2)
    );
    assert_eq!(
        envelope_report.route_bounds.quality_class,
        SearchRouteQualityClass::PremiseOnly
    );
    assert_eq!(envelope_report.route_bounds.selected_route_cost, Some(2));
    assert_eq!(envelope_report.route_bounds.optimality_gap, None);
    assert_eq!(envelope_report.route_bounds.approximation_ratio_milli, None);
    assert_eq!(envelope_report.route_bounds.admissible_upper_bound, Some(2));
}

#[test]
fn latest_epoch_recovery_bound_is_reported_after_reconfiguration() {
    let domain = make_domain();
    let mut machine = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
    machine.step_once().expect("first step");
    commit_epoch_reconfiguration(&mut machine, EpochReconfigurationRequest { next_epoch: 2 });
    let (report, _) = run_with_executor(
        &mut machine,
        &SerialProposalExecutor,
        run_config(
            SearchSchedulerProfile::CanonicalSerial,
            1,
            &[SearchFairnessAssumption::DeterministicSchedulerConfluence],
        ),
    )
    .expect("post-reconfiguration run");
    assert_eq!(report.observation.graph_epoch_trace, vec![1, 2]);
    assert_eq!(report.route_bounds.candidate_discovery_bound_steps, Some(2));
    assert_eq!(report.route_bounds.goal_window_entry_bound_steps, Some(4));
    assert_eq!(
        report.route_bounds.recovery_bound_steps_after_latest_epoch,
        Some(2)
    );
    assert_eq!(
        report
            .route_bounds
            .selected_route_summary
            .as_ref()
            .map(|summary| summary.traversed_epoch_count),
        Some(2)
    );
    assert_eq!(
        report
            .route_bounds
            .selected_route_summary
            .as_ref()
            .map(|summary| summary.normalized_commit_count),
        Some(6)
    );
    assert_eq!(
        report
            .route_bounds
            .selected_route_summary
            .as_ref()
            .and_then(|summary| {
                summary
                    .metrics
                    .iter()
                    .find(|metric| metric.name == SearchRouteMetricName::TraversedEpochCount)
                    .map(|metric| metric.value)
            }),
        Some(2)
    );
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

#[test]
fn fairness_artifact_classifies_profiles_with_the_expected_scope() {
    let canonical =
        fairness_artifact_for_profile::<u8, u64>(SearchSchedulerProfile::CanonicalSerial);
    assert_eq!(
        canonical.claim_class,
        SearchFairnessClaimClass::ExactOneStep
    );
    assert_eq!(
        canonical.certificate.class,
        SearchFairnessCertificateClass::CurrentMinKeyBatch
    );
    assert_eq!(canonical.certificate.service_bound_steps, Some(1));
    assert!(canonical.exact_commit_trace_refines_canonical);
    assert!(canonical.exact_state_slice_refines_canonical);
    assert!(canonical.exact_observation_equivalent_to_canonical);
    assert_eq!(
        canonical.certificate.normalization_mode,
        SearchDeterminismMode::Full
    );
    assert_eq!(canonical.certificate.certified_epoch, None);
    assert_eq!(canonical.certificate.certified_phase, None);
    assert_eq!(
        canonical.certificate.certified_observables,
        theorem_backed_observables(SearchSchedulerProfile::CanonicalSerial)
    );
    assert!(canonical.certificate.certified_batch_nodes.is_empty());
    assert!(canonical
        .certificate
        .certified_normalized_commits
        .is_empty());

    let threaded =
        fairness_artifact_for_profile::<u8, u64>(SearchSchedulerProfile::ThreadedExactSingleLane);
    assert_eq!(
        threaded.claim_class,
        SearchFairnessClaimClass::ExactOneStepViaThreadedRefinement
    );
    assert_eq!(
        threaded.certificate.class,
        SearchFairnessCertificateClass::CurrentMinKeyBatchViaThreadedRefinement
    );
    assert_eq!(threaded.certificate.service_bound_steps, Some(1));
    assert!(threaded.exact_commit_trace_refines_canonical);
    assert!(threaded.exact_state_slice_refines_canonical);
    assert!(threaded.exact_observation_equivalent_to_canonical);
    assert_eq!(
        threaded.certificate.normalization_mode,
        SearchDeterminismMode::Full
    );
    assert_eq!(
        threaded.certificate.certified_observables,
        theorem_backed_observables(SearchSchedulerProfile::ThreadedExactSingleLane)
    );

    let batched_exact =
        fairness_artifact_for_profile::<u8, u64>(SearchSchedulerProfile::BatchedParallelExact);
    assert_eq!(
        batched_exact.claim_class,
        SearchFairnessClaimClass::PremisedWindowBounded
    );
    assert_eq!(
        batched_exact.certificate.class,
        SearchFairnessCertificateClass::CertifiedCurrentMinKeyWindow
    );
    assert_eq!(batched_exact.certificate.service_bound_steps, Some(1));
    assert!(!batched_exact.exact_commit_trace_refines_canonical);
    assert!(!batched_exact.exact_state_slice_refines_canonical);
    assert!(!batched_exact.exact_observation_equivalent_to_canonical);
    assert_eq!(
        batched_exact.certificate.normalization_mode,
        SearchDeterminismMode::ModuloCommutativity
    );
    assert_eq!(
        batched_exact.certificate.certified_observables,
        theorem_backed_observables(SearchSchedulerProfile::BatchedParallelExact)
    );
    assert!(batched_exact
        .certificate
        .required_fairness
        .contains(&SearchFairnessAssumption::EventualLiveBatchService));
    assert!(batched_exact
        .certificate
        .required_fairness
        .contains(&SearchFairnessAssumption::NoStarvationWithinLegalWindow));

    let envelope = fairness_artifact_for_profile::<u8, u64>(
        SearchSchedulerProfile::BatchedParallelEnvelopeBounded,
    );
    assert_eq!(envelope.claim_class, SearchFairnessClaimClass::PremiseOnly);
    assert_eq!(
        envelope.certificate.class,
        SearchFairnessCertificateClass::None
    );
    assert_eq!(envelope.certificate.service_bound_steps, None);
    assert!(!envelope.exact_commit_trace_refines_canonical);
    assert!(!envelope.exact_state_slice_refines_canonical);
    assert!(!envelope.exact_observation_equivalent_to_canonical);
    assert_eq!(
        envelope.certificate.normalization_mode,
        SearchDeterminismMode::Replay
    );
    assert_eq!(envelope.certificate.certified_observables.len(), 0);
}

#[test]
fn fairness_classification_function_matches_reported_artifacts() {
    for profile in [
        SearchSchedulerProfile::CanonicalSerial,
        SearchSchedulerProfile::ThreadedExactSingleLane,
        SearchSchedulerProfile::BatchedParallelExact,
        SearchSchedulerProfile::BatchedParallelEnvelopeBounded,
    ] {
        assert_eq!(
            classify_fairness_claim(profile),
            fairness_artifact_for_profile::<u8, u64>(profile).claim_class
        );
    }
}

#[test]
fn replay_artifact_carries_the_same_public_fairness_surface_as_the_report() {
    let mut machine = SearchMachine::new(make_domain(), 1, 0, 3, EpsilonMilli::one());
    let (report, replay) = run_with_executor(
        &mut machine,
        &SerialProposalExecutor,
        run_config(
            SearchSchedulerProfile::CanonicalSerial,
            1,
            &[SearchFairnessAssumption::DeterministicSchedulerConfluence],
        ),
    )
    .expect("canonical run");
    assert_eq!(report.fairness, replay.fairness);
    assert_eq!(report.fairness.certificate.service_bound_steps, Some(1));
    assert_eq!(
        report.fairness.certificate.certified_batch_nodes,
        replay.rounds.first().expect("replay round").batch_nodes
    );
    assert_eq!(
        report.fairness.certificate.certified_normalized_commits,
        replay.rounds.first().expect("replay round").commits
    );
    assert_eq!(
        report.fairness.certificate.certified_epoch,
        replay.rounds.first().map(|round| round.epoch)
    );
    assert_eq!(
        report.fairness.certificate.certified_phase,
        replay.rounds.first().map(|round| round.phase)
    );
    assert_eq!(
        report.fairness_certificate_trace,
        replay.fairness_certificate_trace
    );
    assert_eq!(report.final_state, replay.final_state);
    assert_eq!(report.theorem_pack, replay.theorem_pack);
    assert_eq!(report.route_bounds, replay.route_bounds);
    assert_eq!(validate_fairness_certificate_trace(&replay), Ok(()));
}

#[cfg(feature = "multi-thread")]
#[test]
fn batched_exact_run_emits_representative_certified_window_payload() {
    let mut machine = SearchMachine::new(make_domain(), 1, 0, 3, EpsilonMilli::one());
    let (report, replay) = run_with_executor(
        &mut machine,
        &native_executor(2),
        run_config(
            SearchSchedulerProfile::BatchedParallelExact,
            2,
            &[
                SearchFairnessAssumption::DeterministicSchedulerConfluence,
                SearchFairnessAssumption::EventualLiveBatchService,
                SearchFairnessAssumption::NoStarvationWithinLegalWindow,
            ],
        ),
    )
    .expect("batched exact run");
    assert_eq!(
        report.fairness.certificate.class,
        SearchFairnessCertificateClass::CertifiedCurrentMinKeyWindow
    );
    assert_eq!(
        report.fairness.certificate.certified_batch_nodes,
        replay.rounds.first().expect("replay round").batch_nodes
    );
    assert_eq!(
        report.fairness.certificate.certified_normalized_commits,
        replay.rounds.first().expect("replay round").commits
    );
    assert_eq!(
        report.fairness.certificate.certified_epoch,
        replay.rounds.first().map(|round| round.epoch)
    );
    assert_eq!(
        report.fairness.certificate.certified_phase,
        replay.rounds.first().map(|round| round.phase)
    );
    assert_eq!(report.fairness_certificate_trace.len(), replay.rounds.len());
    assert!(report
        .fairness_certificate_trace
        .iter()
        .all(|certificate| certificate.class
            == SearchFairnessCertificateClass::CertifiedCurrentMinKeyWindow));
    assert!(!report.fairness.exact_observation_equivalent_to_canonical);
}

#[test]
fn theorem_pack_artifact_matches_the_expected_inventory_and_gate() {
    let artifact = search_theorem_pack_artifact();
    assert_eq!(artifact.canonical_service_bound_steps, 1);
    assert_eq!(artifact.gate, "just check-search-fairness");
    let inventory = artifact
        .inventory
        .iter()
        .map(|entry| (entry.name.as_str(), entry.present))
        .collect::<std::collections::BTreeMap<_, _>>();
    assert_eq!(
        inventory.get("search_threaded_exact_single_lane_state_slice_refines_canonical"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_threaded_exact_single_lane_observation_equivalent_to_canonical"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_batched_parallel_exact_bounded_dynamic_starvation_freedom"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_batched_parallel_exact_certified_window_trace_valid"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_threaded_exact_single_lane_state_artifact_refines_canonical"),
        Some(&true)
    );
    assert_eq!(
        inventory.get(
            "search_threaded_exact_single_lane_multi_step_state_artifact_trace_refines_canonical"
        ),
        Some(&true)
    );
}

#[cfg(feature = "multi-thread")]
#[test]
fn theorem_backed_observables_align_with_public_observation_comparison() {
    let domain = make_domain();
    let fairness = [SearchFairnessAssumption::DeterministicSchedulerConfluence];

    let mut serial = SearchMachine::new(domain.clone(), 1, 0, 3, EpsilonMilli::one());
    let (serial_report, _) = run_with_executor(
        &mut serial,
        &SerialProposalExecutor,
        run_config(SearchSchedulerProfile::CanonicalSerial, 1, &fairness),
    )
    .expect("serial run");

    let mut threaded = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
    let (threaded_report, _) = run_with_executor(
        &mut threaded,
        &native_executor(1),
        run_config(
            SearchSchedulerProfile::ThreadedExactSingleLane,
            1,
            &fairness,
        ),
    )
    .expect("threaded exact run");

    let required = theorem_backed_observables(SearchSchedulerProfile::ThreadedExactSingleLane)
        .into_iter()
        .collect::<Vec<SearchObservableClass>>();
    let comparison = compare_observations(
        &serial_report.observation,
        &threaded_report.observation,
        SearchDeterminismMode::Full,
        &required,
    );
    assert_eq!(comparison.relation, ObservationRelation::Exact);
    assert!(comparison.mismatches.is_empty());
}

#[cfg(feature = "multi-thread")]
#[test]
fn exact_threaded_multi_step_state_trace_matches_canonical_serial() {
    let domain = make_domain();
    let fairness = [SearchFairnessAssumption::DeterministicSchedulerConfluence];

    let mut serial = SearchMachine::new(domain.clone(), 1, 0, 3, EpsilonMilli::one());
    let (serial_report, serial_replay) = run_with_executor(
        &mut serial,
        &SerialProposalExecutor,
        run_config(SearchSchedulerProfile::CanonicalSerial, 1, &fairness),
    )
    .expect("serial run");

    let mut threaded = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
    let (threaded_report, threaded_replay) = run_with_executor(
        &mut threaded,
        &native_executor(1),
        run_config(
            SearchSchedulerProfile::ThreadedExactSingleLane,
            1,
            &fairness,
        ),
    )
    .expect("threaded exact run");

    assert_eq!(
        serial_replay
            .rounds
            .iter()
            .map(|round| &round.state_after_round)
            .collect::<Vec<_>>(),
        threaded_replay
            .rounds
            .iter()
            .map(|round| &round.state_after_round)
            .collect::<Vec<_>>()
    );
    assert_eq!(serial_report.final_state, threaded_report.final_state);
    assert_eq!(
        serial_report
            .fairness_certificate_trace
            .iter()
            .map(|certificate| &certificate.certified_normalized_commits)
            .collect::<Vec<_>>(),
        threaded_report
            .fairness_certificate_trace
            .iter()
            .map(|certificate| &certificate.certified_normalized_commits)
            .collect::<Vec<_>>()
    );
}

#[test]
fn invalid_certificate_trace_is_rejected_fail_closed() {
    let mut machine = SearchMachine::new(make_domain(), 1, 0, 3, EpsilonMilli::one());
    let (_, mut replay) = run_with_executor(
        &mut machine,
        &SerialProposalExecutor,
        run_config(
            SearchSchedulerProfile::CanonicalSerial,
            1,
            &[SearchFairnessAssumption::DeterministicSchedulerConfluence],
        ),
    )
    .expect("canonical run");
    replay.fairness_certificate_trace[0].certified_phase = Some(99);
    assert_eq!(
        validate_fairness_certificate_trace(&replay),
        Err(SearchFairnessTraceValidationError::PhaseMismatch)
    );
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
