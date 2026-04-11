//! Smoke tests for the initial `telltale-search` scaffold.

use std::collections::BTreeSet;

use telltale_search::{
    compare_observations, runtime::SearchRuntimeMarker, EpsilonMilli, ObservationComparison,
    SearchBudgetState, SearchClaimClass, SearchDUser, SearchDeterminismMode,
    SearchFairnessAssumption, SearchObservableClass, SearchSchedulerProfile, SearchTraceState,
    CRATE_SCOPE,
};

type CompareFn = fn(
    &telltale_search::SearchObservationArtifact<u8, u64, u64>,
    &telltale_search::SearchObservationArtifact<u8, u64, u64>,
    SearchDeterminismMode,
    &[SearchObservableClass],
) -> ObservationComparison;

#[test]
fn phase_one_scaffold_exports_compile() {
    let _ = SearchRuntimeMarker;
    assert_eq!(EpsilonMilli::one().0, 1_000);
    let _ = SearchBudgetState::default();
    let _ = SearchTraceState::default();
    let _ = SearchDUser {
        required_claim_classes: BTreeSet::from([SearchClaimClass::GenericMachine]),
        required_observables: BTreeSet::from([SearchObservableClass::SelectedResultCost]),
        required_profiles: BTreeSet::from([SearchDeterminismMode::Full]),
        required_scheduler_profiles: BTreeSet::from([SearchSchedulerProfile::CanonicalSerial]),
        required_fairness: BTreeSet::from([
            SearchFairnessAssumption::DeterministicSchedulerConfluence,
        ]),
        required_commutativity_region: telltale_search::CommutativityRegionClass::None,
        max_batch_width: 1,
        require_frozen_epoch_replay: false,
        replay_required: false,
    };
    let _: CompareFn = compare_observations;
    assert!(CRATE_SCOPE.contains("weighted-graph-plus-epoch"));
}
