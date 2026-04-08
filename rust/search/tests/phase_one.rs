//! Smoke tests for the initial `telltale-search` scaffold.

use telltale_search::{
    compare_observations, runtime::SearchRuntimeMarker, EpsilonMilli, ObservationComparison,
    SearchBudgetState, SearchDUser, SearchDeterminismMode, SearchFairnessAssumption,
    SearchObservableClass, SearchSchedulerProfile, SearchTraceState, CRATE_SCOPE,
};

#[test]
fn phase_one_scaffold_exports_compile() {
    let _ = SearchRuntimeMarker::default();
    let _ = EpsilonMilli::one();
    let _ = SearchBudgetState::default();
    let _ = SearchTraceState::default();
    let _ = SearchDUser {
        required_observables: vec![SearchObservableClass::IncumbentCost],
        required_profiles: vec![SearchDeterminismMode::Full],
        required_scheduler_profiles: vec![SearchSchedulerProfile::CanonicalSerial],
        required_fairness: vec![SearchFairnessAssumption::DeterministicSchedulerConfluence],
        required_commutativity_region: telltale_search::CommutativityRegionClass::None,
        max_batch_width: 1,
        require_frozen_epoch_replay: false,
        replay_required: false,
    };
    let _: fn(
        &telltale_search::SearchObservationArtifact<u8, u64, u64>,
        &telltale_search::SearchObservationArtifact<u8, u64, u64>,
        SearchDeterminismMode,
        &[SearchObservableClass],
    ) -> ObservationComparison = compare_observations;
    assert!(CRATE_SCOPE.contains("weighted-graph-plus-epoch"));
}
