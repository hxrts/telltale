//! Sidebar overlay controls for each viewer page.

use crate::components::*;
use crate::types::*;
use dioxus::prelude::*;
use telltale_macros::observed_only;

#[observed_only]
#[component]
pub(crate) fn GraphControlsOverlay(
    state: InteractiveViewerState,
    on_select_projection: EventHandler<usize>,
    on_step_forward: EventHandler<()>,
    on_step_backward: EventHandler<()>,
    on_jump_to_step: EventHandler<u64>,
    on_fork_branch: EventHandler<()>,
    on_update_branch: EventHandler<()>,
    on_delete_branch: EventHandler<()>,
    on_search: EventHandler<String>,
) -> Element {
    let max_step = state.projection_step_limit();
    rsx! {
        section {
            class: "tt-shell__overlay",
                SidebarSection {
                    title: "Time Travel",
                    children: rsx! {
                        div {
                            class: "flex flex-wrap gap-1",
                            SidebarButton { label: "Step -", onclick: move |_| on_step_backward.call(()) }
                            SidebarButton { label: "Step +", onclick: move |_| on_step_forward.call(()) }
                        }
                        div {
                            class: "flex flex-wrap gap-1 mt-1.5",
                            for step in 0..=max_step {
                                button {
                                    r#type: "button",
                                    class: nav_tab_class(step == state.workspace.graph.active_step),
                                    onclick: move |_| on_jump_to_step.call(step),
                                    "{step}"
                                }
                            }
                        }
                    }
                }
                SidebarSection {
                    title: "Projections",
                    children: rsx! {
                        div {
                            class: "space-y-0.5",
                            for (index, projection) in state.workspace.graph.projections.iter().enumerate() {
                                div {
                                    onclick: move |_| on_select_projection.call(index),
                                    SidebarListItem {
                                        label: format!("{:?}", projection.kind),
                                        active: index == state.workspace.graph.active_projection,
                                    }
                                }
                            }
                        }
                    }
                }
                SidebarSection {
                    title: "Branches",
                    children: rsx! {
                        div {
                            class: "space-y-1",
                            SidebarButton { label: "Fork Here", onclick: move |_| on_fork_branch.call(()) }
                            SidebarButton { label: "Update Branch", onclick: move |_| on_update_branch.call(()) }
                            SidebarButton { label: "Delete Branch", onclick: move |_| on_delete_branch.call(()) }
                        }
                    }
                }
                SidebarSection {
                    title: "Search",
                    children: rsx! {
                        div {
                            class: "space-y-1",
                            SidebarButton { label: "Find alpha", onclick: move |_| on_search.call("alpha".to_string()) }
                            SidebarButton { label: "Find branch", onclick: move |_| on_search.call("branch".to_string()) }
                        }
                    }
                }
        }
    }
}

#[observed_only]
#[component]
pub(crate) fn InsightControlsOverlay(
    state: InteractiveViewerState,
    on_reload_archive: EventHandler<()>,
    on_add_bookmark: EventHandler<()>,
) -> Element {
    rsx! {
        section {
            class: "tt-shell__overlay",
                SidebarSection {
                    title: "Archive",
                    children: rsx! {
                        div {
                            class: "space-y-1",
                            SidebarButton { label: "Reload Archive", onclick: move |_| on_reload_archive.call(()) }
                            SidebarButton { label: "Bookmark Step", onclick: move |_| on_add_bookmark.call(()) }
                        }
                    }
                }
                SidebarSection {
                    title: "Active Branch",
                    children: rsx! {
                        KeyValueLine { label: "Branch".to_string(), value: state.workspace.graph.active_branch.clone() }
                        KeyValueLine { label: "Step".to_string(), value: state.workspace.graph.active_step.to_string() }
                    }
                }
        }
    }
}

#[observed_only]
#[component]
pub(crate) fn SweepControlsOverlay(
    state: InteractiveViewerState,
    on_filter_sweeps: EventHandler<String>,
    on_drill_sweep_case: EventHandler<String>,
) -> Element {
    let first_case_id = state
        .workspace
        .sweeps
        .explorer
        .visible_cases
        .first()
        .map(|case| case.case_id.clone());
    rsx! {
        section {
            class: "tt-shell__overlay",
                SidebarSection {
                    title: "Sweeps",
                    children: rsx! {
                        div {
                            class: "space-y-1",
                            SidebarButton { label: "Filter baseline", onclick: move |_| on_filter_sweeps.call("baseline".to_string()) }
                            SidebarButton { label: "Clear Filter", onclick: move |_| on_filter_sweeps.call(String::new()) }
                            if let Some(case_id) = first_case_id.clone() {
                                SidebarButton { label: "Open case", onclick: move |_| on_drill_sweep_case.call(case_id.clone()) }
                            }
                        }
                    }
                }
        }
    }
}

#[observed_only]
#[component]
pub(crate) fn EffectControlsOverlay(
    state: InteractiveViewerState,
    on_request_mocked_rerun: EventHandler<()>,
    on_request_minimization: EventHandler<()>,
) -> Element {
    rsx! {
        section {
            class: "tt-shell__overlay",
                SidebarSection {
                    title: "Effects",
                    children: rsx! {
                        div {
                            class: "space-y-1",
                            SidebarButton { label: "Mock Rerun", onclick: move |_| on_request_mocked_rerun.call(()) }
                            SidebarButton { label: "Minimize", onclick: move |_| on_request_minimization.call(()) }
                        }
                    }
                }
                SidebarSection {
                    title: "Active Target",
                    children: rsx! {
                        KeyValueLine { label: "Artifact".to_string(), value: state.workspace.effects.effect_trace.artifact_id.clone() }
                        KeyValueLine { label: "Branch".to_string(), value: state.workspace.effects.effect_trace.branch_id.clone() }
                    }
                }
        }
    }
}
