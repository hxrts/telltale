//! SSR checks for the shared viewer shell.

use dioxus::prelude::*;
use dioxus_ssr::render_element;
use telltale_ui::{demo_workspace, ViewerFrame, ViewerPage};

#[component]
fn RenderHarness(page: ViewerPage) -> Element {
    let workspace = demo_workspace();
    rsx! {
        ViewerFrame {
            workspace,
            active_page: page,
            on_navigate: move |_| {}
        }
    }
}

fn render_page(page: ViewerPage) -> String {
    render_element(rsx! {
        RenderHarness { page }
    })
}

#[test]
fn shell_renders_sidebar_nav_and_summary_cards() {
    let html = render_page(ViewerPage::Overview);
    assert!(html.contains("tt-app-shell"));
    assert!(html.contains("tt-top-nav"));
    assert!(html.contains("Artifact Inventory"));
    assert!(html.contains("demo_mesh"));
}

#[test]
fn deterministic_harness_mode_disables_implicit_shell_drift() {
    let html = render_page(ViewerPage::Graph);
    assert!(html.contains("data-harness-mode=\"deterministic\""));
    assert!(html.contains("Graph Workspace"));
}

#[test]
fn every_primary_page_reuses_the_global_shell() {
    for page in [ViewerPage::Overview, ViewerPage::Graph, ViewerPage::Insight] {
        let html = render_page(page);
        assert_eq!(html.matches("id=\"tt-app-shell\"").count(), 1);
        assert_eq!(html.matches("id=\"tt-top-nav\"").count(), 1);
    }
}

#[test]
fn insight_page_renders_diff_and_provenance_surfaces() {
    let html = render_page(ViewerPage::Insight);
    assert!(html.contains("Run Diff"));
    assert!(html.contains("Causality"));
    assert!(html.contains("Provenance"));
}

#[test]
fn insight_page_renders_regime_watch_and_bookmark_surfaces() {
    let html = render_page(ViewerPage::Insight);
    assert!(html.contains("Execution regime"));
    assert!(html.contains("Watch Expressions"));
    assert!(html.contains("Bookmarks"));
    assert!(html.contains("initial step"));
}
