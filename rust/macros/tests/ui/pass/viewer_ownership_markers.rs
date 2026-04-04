//! Pass: viewer ownership marker attribute macros.
use telltale_macros::{
    actor_owned, authoritative_source, observed_only, strong_reference, weak_identifier,
};

#[observed_only]
fn project_view() -> &'static str {
    "observed"
}

#[actor_owned("viewer_shell")]
struct ShellWorker;

#[authoritative_source("viewer_query_surface")]
type ViewerQuerySurface = &'static str;

#[strong_reference("artifact_service")]
struct ArtifactService;

#[weak_identifier("artifact_id")]
type ArtifactId = &'static str;

fn main() {
    let _ = project_view();
    let _ = ShellWorker;
    let _surface: ViewerQuerySurface = "query";
    let _ = ArtifactService;
    let _id: ArtifactId = "artifact";
}
