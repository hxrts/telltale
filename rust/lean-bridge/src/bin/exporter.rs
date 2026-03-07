//! Choreography Exporter CLI Tool
//!
//! Exports choreography DSL files to JSON for Lean verification.
//!
//! # Usage
//!
//! ```bash
//! lean-bridge-exporter --input protocol.choreo --role Alice \
//!     --choreography-out choreo.json --program-out program.json
//! ```

use std::fs;
use std::path::PathBuf;

use anyhow::{anyhow, Context, Result};
use bpaf::Bpaf;
use serde_json::json;

use telltale_choreography::ast::convert::choreography_to_global;
use telltale_choreography::compiler::parse_choreography_str;
use telltale_lean_bridge::export::{global_to_json, local_to_json};
use telltale_theory::projection::project as theory_project;

#[derive(Debug, Clone, Bpaf)]
#[bpaf(
    options,
    version("3.0.0"),
    descr("Export choreography DSL files to Lean bridge JSON payloads"),
    footer("Example: lean-bridge-exporter --input protocol.choreo --role Alice --choreography-out choreo.json --program-out program.json")
)]
struct Cli {
    /// Input choreography DSL file.
    #[bpaf(long)]
    input: PathBuf,

    /// Role to project for program output.
    #[bpaf(long)]
    role: String,

    /// Output path for choreography JSON payload.
    #[bpaf(long("choreography-out"))]
    choreography_out: PathBuf,

    /// Output path for projected program JSON payload.
    #[bpaf(long("program-out"))]
    program_out: PathBuf,
}

fn main() -> Result<()> {
    let cli = cli().run();

    let source = fs::read_to_string(&cli.input)
        .with_context(|| format!("Failed to read choreography file {}", cli.input.display()))?;

    let choreography = parse_choreography_str(&source)?;

    let global = choreography_to_global(&choreography)
        .map_err(|e| anyhow!("Failed to convert choreography to GlobalType: {e}"))?;

    let global_json = global_to_json(&global);

    if !global.roles().contains(&cli.role) {
        return Err(anyhow!("Unknown role {}", cli.role));
    }
    let local_r = theory_project(&global, &cli.role)
        .map_err(|e| anyhow!("Failed to project local type from global type: {e:?}"))?;

    let program_json = json!({
        "role": cli.role,
        "local_type": local_to_json(&local_r)
    });

    fs::write(
        &cli.choreography_out,
        serde_json::to_string_pretty(&global_json)?,
    )
    .with_context(|| format!("Failed to write {}", cli.choreography_out.display()))?;

    fs::write(
        &cli.program_out,
        serde_json::to_string_pretty(&program_json)?,
    )
    .with_context(|| format!("Failed to write {}", cli.program_out.display()))?;

    Ok(())
}
