#![allow(missing_docs)]
//! Export the current search theorem-pack artifact as JSON.

use telltale_search::search_theorem_pack_artifact;

fn main() {
    println!(
        "{}",
        serde_json::to_string_pretty(&search_theorem_pack_artifact())
            .expect("serialize search theorem pack")
    );
}
