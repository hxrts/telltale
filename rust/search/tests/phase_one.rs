//! Smoke tests for the initial `telltale-search` scaffold.

use telltale_search::{
    admission::SearchAdmissionMarker, observe::SearchObservationMarker,
    runtime::SearchRuntimeMarker, EpsilonMilli, SearchBudgetState, SearchTraceState, CRATE_SCOPE,
};

#[test]
fn phase_one_scaffold_exports_compile() {
    let _ = SearchAdmissionMarker::default();
    let _ = SearchObservationMarker::default();
    let _ = SearchRuntimeMarker::default();
    let _ = EpsilonMilli::one();
    let _ = SearchBudgetState::default();
    let _ = SearchTraceState::default();
    assert!(CRATE_SCOPE.contains("weighted-graph-plus-epoch"));
}
