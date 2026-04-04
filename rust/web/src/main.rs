//! Thin browser shell for the shared Telltale viewer UI.

use dioxus::prelude::*;
use telltale_ui::{demo_workspace, TelltaleUiRoot};

#[cfg(target_arch = "wasm32")]
fn main() {
    dioxus::launch(App);
}

#[cfg(not(target_arch = "wasm32"))]
fn main() {
    eprintln!("telltale-web targets the browser. Use `dx serve rust/web` for local development.");
}

#[component]
fn App() -> Element {
    let workspace = demo_workspace();
    rsx! {
        TelltaleUiRoot { workspace }
    }
}
