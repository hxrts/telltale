//! Top-level shell, navigation, and sidebar layout.

use crate::components::*;
use crate::overlays::*;
use crate::pages::*;
use crate::types::*;
use dioxus::prelude::*;
use dioxus_shadcn::components::scroll_area::{ScrollArea, ScrollAreaViewport};
use telltale_macros::observed_only;

#[component]
pub fn TelltaleUiRoot(workspace: ViewerWorkspace) -> Element {
    let mut state = use_signal(|| InteractiveViewerState::from_workspace(workspace));
    rsx! {
        InteractiveViewerFrame {
            state: state(),
            on_navigate: move |page| {
                let mut next = state();
                next.set_page(page);
                state.set(next);
            },
            on_select_artifact: move |artifact_id: String| {
                let mut next = state();
                next.select_artifact(artifact_id);
                state.set(next);
            },
            on_select_projection: move |index| {
                let mut next = state();
                next.select_projection(index);
                state.set(next);
            },
            on_step_forward: move |_| {
                let mut next = state();
                next.step_forward();
                state.set(next);
            },
            on_step_backward: move |_| {
                let mut next = state();
                next.step_backward();
                state.set(next);
            },
            on_jump_to_step: move |step| {
                let mut next = state();
                next.jump_to_step(step);
                state.set(next);
            },
            on_fork_branch: move |_| {
                let mut next = state();
                next.fork_branch_from_current_step();
                state.set(next);
            },
            on_update_branch: move |_| {
                let mut next = state();
                next.update_active_branch();
                state.set(next);
            },
            on_delete_branch: move |_| {
                let mut next = state();
                next.delete_active_branch();
                state.set(next);
            },
            on_search: move |query: String| {
                let mut next = state();
                next.search(&query);
                state.set(next);
            },
            on_reload_archive: move |_| {
                let mut next = state();
                next.reload_archive();
                state.set(next);
            },
            on_add_bookmark: move |_| {
                let mut next = state();
                next.add_bookmark();
                state.set(next);
            },
            on_filter_sweeps: move |needle: String| {
                let mut next = state();
                next.filter_sweeps(&needle);
                state.set(next);
            },
            on_drill_sweep_case: move |case_id: String| {
                let mut next = state();
                next.drill_into_sweep_case(&case_id);
                state.set(next);
            },
            on_request_mocked_rerun: move |_| {
                let mut next = state();
                next.request_mocked_rerun();
                state.set(next);
            },
            on_request_minimization: move |_| {
                let mut next = state();
                next.request_minimization();
                state.set(next);
            },
        }
    }
}

#[observed_only]
#[component]
pub(crate) fn InteractiveViewerFrame(
    state: InteractiveViewerState,
    on_navigate: EventHandler<ViewerPage>,
    on_select_artifact: EventHandler<String>,
    on_select_projection: EventHandler<usize>,
    on_step_forward: EventHandler<()>,
    on_step_backward: EventHandler<()>,
    on_jump_to_step: EventHandler<u64>,
    on_fork_branch: EventHandler<()>,
    on_update_branch: EventHandler<()>,
    on_delete_branch: EventHandler<()>,
    on_search: EventHandler<String>,
    on_reload_archive: EventHandler<()>,
    on_add_bookmark: EventHandler<()>,
    on_filter_sweeps: EventHandler<String>,
    on_drill_sweep_case: EventHandler<String>,
    on_request_mocked_rerun: EventHandler<()>,
    on_request_minimization: EventHandler<()>,
) -> Element {
    let overlay = match state.active_page {
        ViewerPage::Graph => rsx! {
            GraphControlsOverlay {
                state: state.clone(),
                on_select_projection,
                on_step_forward,
                on_step_backward,
                on_jump_to_step,
                on_fork_branch,
                on_update_branch,
                on_delete_branch,
                on_search,
            }
        },
        ViewerPage::Insight => rsx! {
            InsightControlsOverlay {
                state: state.clone(),
                on_reload_archive,
                on_add_bookmark,
            }
        },
        ViewerPage::Sweeps => rsx! {
            SweepControlsOverlay {
                state: state.clone(),
                on_filter_sweeps,
                on_drill_sweep_case,
            }
        },
        ViewerPage::Effects => rsx! {
            EffectControlsOverlay {
                state: state.clone(),
                on_request_mocked_rerun,
                on_request_minimization,
            }
        },
        _ => rsx! {},
    };
    rsx! {
        ViewerFrame {
            workspace: state.workspace.clone(),
            active_page: state.active_page,
            on_navigate,
            on_select_artifact,
            sidebar_overlay: overlay,
        }
    }
}

#[observed_only]
#[component]
pub fn ViewerFrame(
    workspace: ViewerWorkspace,
    active_page: ViewerPage,
    on_navigate: EventHandler<ViewerPage>,
    on_select_artifact: EventHandler<String>,
    sidebar_overlay: Element,
) -> Element {
    let publication = ViewerPublicationDiagnostics {
        active_page,
        ..workspace.diagnostics.clone()
    };
    let shell_mode = match publication.harness_mode {
        HarnessMode::Normal => "normal",
        HarnessMode::Deterministic => "deterministic",
    };
    rsx! {
        main {
            id: "tt-app-shell",
            class: "tt-shell",
            "data-harness-mode": "{shell_mode}",
            "data-readiness": "{publication.readiness.label()}",
            TopNav { pages: workspace.pages.clone(), active_page, on_navigate }
            div {
                class: "tt-shell__body",
                div {
                    class: "tt-shell__sidebar",
                    ScrollArea {
                        ScrollAreaViewport {
                            SidebarControls { workspace: workspace.clone(), publication: publication.clone(), on_select_artifact }
                            {sidebar_overlay}
                        }
                    }
                }
                section {
                    class: "tt-shell__content",
                    ScrollArea {
                        ScrollAreaViewport {
                            match active_page {
                                ViewerPage::Overview => rsx! { OverviewPage { workspace: workspace.clone(), on_select_artifact } },
                                ViewerPage::Graph => rsx! { GraphPage { workspace: workspace.clone() } },
                                ViewerPage::Insight => rsx! { InsightPage { workspace: workspace.clone() } },
                                ViewerPage::Sweeps => rsx! { SweepsPage { workspace: workspace.clone() } },
                                ViewerPage::Effects => rsx! { EffectsPage { workspace: workspace.clone() } },
                            }
                        }
                    }
                }
            }
        }
    }
}

#[component]
pub(crate) fn SidebarControls(
    workspace: ViewerWorkspace,
    publication: ViewerPublicationDiagnostics,
    on_select_artifact: EventHandler<String>,
) -> Element {
    let active_artifact = publication
        .active_artifact
        .clone()
        .unwrap_or_else(|| "none".to_string());
    rsx! {
        div {
            class: "mb-4",
            StatusBadge {
                tone: publication.status_tone(),
                label: format!("{} artifacts / {} scenarios", publication.artifact_count, publication.scenario_count)
            }
        }
        SidebarSection {
            title: "Selection",
            children: rsx! {
                KeyValueLine { label: "Artifact".to_string(), value: active_artifact.clone() }
            }
        }
        SidebarSection {
            title: "Artifacts",
            children: rsx! {
                div {
                    class: "space-y-0.5",
                    for artifact in workspace.report.artifacts.iter().take(8) {
                        {
                            let artifact_id = artifact.artifact_id.clone();
                            let is_active = Some(&artifact.artifact_id) == publication.active_artifact.as_ref();
                            rsx! {
                                div {
                                    onclick: move |_| on_select_artifact.call(artifact_id.clone()),
                                    SidebarListItem { label: artifact.label.clone(), active: is_active }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

#[component]
pub(crate) fn TopNav(
    pages: Vec<ViewerPage>,
    active_page: ViewerPage,
    on_navigate: EventHandler<ViewerPage>,
) -> Element {
    rsx! {
        nav {
            id: "tt-top-nav",
            class: "flex items-center border-b border-border bg-background/95 backdrop-blur px-6 pt-3 pb-2 shrink-0",
            div {
                class: "flex items-center gap-3 mr-auto",
                span {
                    class: "text-xs font-sans font-bold uppercase tracking-[0.12em] text-foreground",
                    "TELLTALE"
                }
            }
            div {
                class: "flex items-center justify-center gap-2",
                for page in pages {
                    button {
                        r#type: "button",
                        class: nav_tab_class(page == active_page),
                        onclick: move |_| on_navigate.call(page),
                        "{page.label()}"
                    }
                }
            }
            div { class: "ml-auto w-24" }
        }
    }
}
