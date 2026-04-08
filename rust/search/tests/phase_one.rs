//! Smoke tests for the initial `telltale-search` scaffold.

use telltale_search::{
    admission::SearchAdmissionMarker, cost::EpsilonMarker, machine::SearchMachineMarker,
    observe::SearchObservationMarker, runtime::SearchRuntimeMarker, CRATE_SCOPE,
};

#[test]
fn phase_one_scaffold_exports_compile() {
    let _ = SearchAdmissionMarker::default();
    let _ = SearchMachineMarker::default();
    let _ = SearchObservationMarker::default();
    let _ = SearchRuntimeMarker::default();
    let _ = EpsilonMarker;
    assert!(CRATE_SCOPE.contains("weighted-graph-plus-epoch"));
}
