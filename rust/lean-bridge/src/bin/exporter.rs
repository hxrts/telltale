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

use std::env;
use std::fs;
use std::path::PathBuf;

use anyhow::{anyhow, Context, Result};
use serde_json::json;

use telltale_choreography::ast::convert::{choreography_to_global, local_to_local_r};
use telltale_choreography::compiler::{parse_choreography_str, project};
use telltale_lean_bridge::export::{global_to_json, local_to_json};

struct Config {
    input: PathBuf,
    role: String,
    choreography_out: PathBuf,
    program_out: PathBuf,
}

fn main() -> Result<()> {
    let args: Vec<String> = env::args().collect();
    let config = parse_args(&args)?;

    let source = fs::read_to_string(&config.input).with_context(|| {
        format!(
            "Failed to read choreography file {}",
            config.input.display()
        )
    })?;

    let choreography = parse_choreography_str(&source)?;

    let global = choreography_to_global(&choreography).map_err(|e| {
        anyhow!(
            "Failed to convert choreography to GlobalType: {}",
            e.to_string()
        )
    })?;

    let global_json = global_to_json(&global);

    let role = choreography
        .roles
        .iter()
        .find(|role| *role.name() == config.role)
        .ok_or_else(|| anyhow!("Unknown role {}", config.role))?;

    let local_type = project(&choreography, role)?;
    let local_r = local_to_local_r(&local_type).map_err(|e| {
        anyhow!(
            "Failed to convert local type to LocalTypeR: {}",
            e.to_string()
        )
    })?;

    let program_json = json!({
        "role": role.name().to_string(),
        "local_type": local_to_json(&local_r)
    });

    fs::write(
        &config.choreography_out,
        serde_json::to_string_pretty(&global_json)?,
    )
    .with_context(|| format!("Failed to write {}", config.choreography_out.display()))?;

    fs::write(&config.program_out, serde_json::to_string_pretty(&program_json)?)
        .with_context(|| format!("Failed to write {}", config.program_out.display()))?;

    Ok(())
}

fn parse_args(args: &[String]) -> Result<Config> {
    let mut config = Config {
        input: PathBuf::new(),
        role: String::new(),
        choreography_out: PathBuf::new(),
        program_out: PathBuf::new(),
    };

    let mut iter = args.iter().skip(1);
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--input" => {
                config.input = iter
                    .next()
                    .map(PathBuf::from)
                    .ok_or_else(|| anyhow!("Missing value for --input"))?
            }
            "--role" => config.role.clone_from(
                iter.next()
                    .ok_or_else(|| anyhow!("Missing value for --role"))?,
            ),
            "--choreography-out" => {
                config.choreography_out = iter
                    .next()
                    .map(PathBuf::from)
                    .ok_or_else(|| anyhow!("Missing value for --choreography-out"))?
            }
            "--program-out" => {
                config.program_out = iter
                    .next()
                    .map(PathBuf::from)
                    .ok_or_else(|| anyhow!("Missing value for --program-out"))?
            }
            _ => return Err(anyhow!("Unknown argument {arg}")),
        }
    }

    if config.input.as_os_str().is_empty()
        || config.role.is_empty()
        || config.choreography_out.as_os_str().is_empty()
        || config.program_out.as_os_str().is_empty()
    {
        return Err(anyhow!(
            "Usage: lean-bridge-exporter --input <dsl> --role <role> --choreography-out <path> --program-out <path>"
        ));
    }

    Ok(config)
}
