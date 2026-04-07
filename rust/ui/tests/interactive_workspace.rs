//! Interaction-level checks for the graph/time-travel workspace.

use telltale_ui::{demo_workspace, InteractiveViewerState, ViewerPage};

#[test]
fn step_navigation_and_jump_are_deterministic() {
    let workspace = demo_workspace();
    let mut state = InteractiveViewerState::from_workspace(workspace);
    state.set_page(ViewerPage::Graph);
    state.select_projection(2);

    state.step_forward();
    state.step_forward();
    assert_eq!(state.workspace.graph.active_step, 2);

    state.step_backward();
    assert_eq!(state.workspace.graph.active_step, 1);

    state.jump_to_step(99);
    assert_eq!(state.workspace.graph.active_step, 2);
}

#[test]
fn branch_commands_update_lineage_and_diff_snapshot() {
    let workspace = demo_workspace();
    let mut state = InteractiveViewerState::from_workspace(workspace);
    state.set_page(ViewerPage::Graph);
    state.select_projection(3);
    state.jump_to_step(2);
    state.fork_branch_from_current_step();
    state.update_active_branch();

    assert_eq!(state.workspace.graph.active_branch, "branch/1");
    assert_eq!(state.workspace.graph.command_log.len(), 2);
    assert_eq!(
        state.workspace.insights.run_diff.candidate_branch,
        "branch/1"
    );
    assert!(state
        .workspace
        .graph
        .projections
        .iter()
        .find(|projection| projection.kind == telltale_viewer::GraphProjectionKind::BranchLineage)
        .expect("branch lineage projection")
        .nodes
        .iter()
        .any(|node| node.id == "branch/1"));
}

#[test]
fn search_reload_and_bookmark_state_are_stable() {
    let workspace = demo_workspace();
    let mut state = InteractiveViewerState::from_workspace(workspace);
    state.set_page(ViewerPage::Graph);
    state.search("alpha");
    state.add_bookmark();
    state.reload_archive();

    assert_eq!(state.workspace.graph.search_query, "alpha");
    assert!(!state.workspace.graph.search_results.is_empty());
    assert_eq!(state.workspace.insights.bookmarks.len(), 2);
    assert!(state.workspace.insights.archive_status.contains("reloaded"));
}

#[test]
fn deterministic_layout_and_provenance_snapshots_are_stable() {
    let first = demo_workspace();
    let second = demo_workspace();

    assert_eq!(first.graph.layout, second.graph.layout);
    assert_eq!(first.insights.provenance.run_id, "demo-run");
    assert_eq!(first.insights.run_diff.baseline_branch, "root");
    assert_eq!(first.insights.watch_expressions.len(), 2);
}

#[test]
fn sweep_filter_and_drilldown_are_deterministic() {
    let workspace = demo_workspace();
    let mut state = InteractiveViewerState::from_workspace(workspace);
    state.set_page(ViewerPage::Sweeps);
    state.filter_sweeps("observed");

    assert_eq!(state.workspace.sweeps.explorer.visible_cases.len(), 1);
    let case_id = state.workspace.sweeps.explorer.visible_cases[0]
        .case_id
        .clone();
    state.drill_into_sweep_case(&case_id);

    assert_eq!(
        state.workspace.sweeps.selected_case.as_deref(),
        Some(case_id.as_str())
    );
    assert!(state.workspace.diagnostics.active_artifact.is_some());
}

#[test]
fn mocked_rerun_and_minimization_commands_append_effect_logs() {
    let workspace = demo_workspace();
    let mut state = InteractiveViewerState::from_workspace(workspace);
    state.set_page(ViewerPage::Effects);
    state.request_mocked_rerun();
    state.request_minimization();

    assert_eq!(state.workspace.effects.mock_command_log.len(), 2);
    assert!(state.workspace.effects.mock_command_log[0].contains("RequestMockedRerun"));
    assert!(state.workspace.effects.mock_command_log[1].contains("RequestMinimization"));
}
