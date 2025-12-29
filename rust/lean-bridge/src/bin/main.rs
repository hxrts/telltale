//! Lean Bridge CLI Tool
//!
//! Provides command-line utilities for converting between Rust session types
//! and Lean-compatible JSON format.
//!
//! # Usage
//!
//! ```bash
//! # Convert JSON to Rust types (validation)
//! lean-bridge validate --input protocol.json
//!
//! # Export GlobalType to JSON
//! lean-bridge export --output protocol.json
//!
//! # Import JSON and display Rust representation
//! lean-bridge import --input protocol.json --type global
//! ```

use clap::{Parser, Subcommand};
use rumpsteak_lean_bridge::{global_to_json, json_to_global, json_to_local, local_to_json};
use rumpsteak_types::{GlobalType, Label, LocalTypeR};
use std::fs;
use std::io::{self, Read, Write};
use std::path::PathBuf;

/// Lean Bridge CLI - Convert between Rust session types and Lean JSON format
#[derive(Parser)]
#[command(name = "lean-bridge")]
#[command(version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Export a sample GlobalType/LocalTypeR to JSON
    Export {
        /// Output file (stdout if not specified)
        #[arg(short, long)]
        output: Option<PathBuf>,

        /// Type to export: global or local
        #[arg(short = 't', long, default_value = "global")]
        type_name: String,

        /// Pretty-print the JSON output
        #[arg(short, long)]
        pretty: bool,
    },

    /// Import JSON and parse it into Rust types
    Import {
        /// Input JSON file (stdin if not specified)
        #[arg(short, long)]
        input: Option<PathBuf>,

        /// Type to import: global or local
        #[arg(short = 't', long, default_value = "global")]
        type_name: String,
    },

    /// Validate JSON format and test round-trip conversion
    Validate {
        /// Input JSON file (stdin if not specified)
        #[arg(short, long)]
        input: Option<PathBuf>,

        /// Type to validate: global or local
        #[arg(short = 't', long, default_value = "global")]
        type_name: String,

        /// Verbose output
        #[arg(short, long)]
        verbose: bool,
    },

    /// Generate a sample protocol JSON for testing
    Sample {
        /// Output file (stdout if not specified)
        #[arg(short, long)]
        output: Option<PathBuf>,

        /// Sample type: ping-pong, calculator, ring
        #[arg(short, long, default_value = "ping-pong")]
        sample: String,

        /// Pretty-print the JSON output
        #[arg(short, long)]
        pretty: bool,
    },
}

fn main() {
    let cli = Cli::parse();

    let result = match cli.command {
        Commands::Export {
            output,
            type_name,
            pretty,
        } => run_export(output, &type_name, pretty),

        Commands::Import { input, type_name } => run_import(input, &type_name),

        Commands::Validate {
            input,
            type_name,
            verbose,
        } => run_validate(input, &type_name, verbose),

        Commands::Sample {
            output,
            sample,
            pretty,
        } => run_sample(output, &sample, pretty),
    };

    if let Err(e) = result {
        eprintln!("Error: {}", e);
        std::process::exit(1);
    }
}

fn run_export(output: Option<PathBuf>, type_name: &str, pretty: bool) -> Result<(), String> {
    // Create a sample type to export
    let json = match type_name {
        "global" => {
            let g = GlobalType::comm(
                "Client",
                "Server",
                vec![(Label::new("request"), GlobalType::End)],
            );
            global_to_json(&g)
        }
        "local" => {
            let lt = LocalTypeR::send("Server", Label::new("request"), LocalTypeR::End);
            local_to_json(&lt)
        }
        _ => {
            return Err(format!(
                "Unknown type: {}. Use 'global' or 'local'",
                type_name
            ))
        }
    };

    let output_str = if pretty {
        serde_json::to_string_pretty(&json).map_err(|e| e.to_string())?
    } else {
        serde_json::to_string(&json).map_err(|e| e.to_string())?
    };

    write_output(output, &output_str)
}

fn run_import(input: Option<PathBuf>, type_name: &str) -> Result<(), String> {
    let json_str = read_input(input)?;
    let json: serde_json::Value =
        serde_json::from_str(&json_str).map_err(|e| format!("Invalid JSON: {}", e))?;

    match type_name {
        "global" => {
            let g =
                json_to_global(&json).map_err(|e| format!("Failed to parse GlobalType: {}", e))?;
            println!("Successfully parsed GlobalType:");
            println!("{:#?}", g);
        }
        "local" => {
            let lt =
                json_to_local(&json).map_err(|e| format!("Failed to parse LocalTypeR: {}", e))?;
            println!("Successfully parsed LocalTypeR:");
            println!("{:#?}", lt);
        }
        _ => {
            return Err(format!(
                "Unknown type: {}. Use 'global' or 'local'",
                type_name
            ))
        }
    }

    Ok(())
}

fn run_validate(input: Option<PathBuf>, type_name: &str, verbose: bool) -> Result<(), String> {
    let json_str = read_input(input)?;
    let json: serde_json::Value =
        serde_json::from_str(&json_str).map_err(|e| format!("Invalid JSON: {}", e))?;

    match type_name {
        "global" => {
            // Parse JSON to Rust
            let g =
                json_to_global(&json).map_err(|e| format!("Failed to parse GlobalType: {}", e))?;

            if verbose {
                println!("Parsed GlobalType:");
                println!("{:#?}", g);
            }

            // Convert back to JSON
            let roundtrip_json = global_to_json(&g);

            // Parse again
            let g2 =
                json_to_global(&roundtrip_json).map_err(|e| format!("Round-trip failed: {}", e))?;

            // Compare
            if g == g2 {
                println!("✓ Round-trip validation successful for GlobalType");
            } else {
                return Err("Round-trip validation failed: types don't match".to_string());
            }
        }
        "local" => {
            // Parse JSON to Rust
            let lt =
                json_to_local(&json).map_err(|e| format!("Failed to parse LocalTypeR: {}", e))?;

            if verbose {
                println!("Parsed LocalTypeR:");
                println!("{:#?}", lt);
            }

            // Convert back to JSON
            let roundtrip_json = local_to_json(&lt);

            // Parse again
            let lt2 =
                json_to_local(&roundtrip_json).map_err(|e| format!("Round-trip failed: {}", e))?;

            // Compare
            if lt == lt2 {
                println!("✓ Round-trip validation successful for LocalTypeR");
            } else {
                return Err("Round-trip validation failed: types don't match".to_string());
            }
        }
        _ => {
            return Err(format!(
                "Unknown type: {}. Use 'global' or 'local'",
                type_name
            ))
        }
    }

    Ok(())
}

fn run_sample(output: Option<PathBuf>, sample: &str, pretty: bool) -> Result<(), String> {
    let g = match sample {
        "ping-pong" => GlobalType::comm(
            "Client",
            "Server",
            vec![(
                Label::new("ping"),
                GlobalType::comm(
                    "Server",
                    "Client",
                    vec![(Label::new("pong"), GlobalType::End)],
                ),
            )],
        ),
        "calculator" => GlobalType::comm(
            "Client",
            "Server",
            vec![
                (
                    Label::new("add"),
                    GlobalType::comm(
                        "Server",
                        "Client",
                        vec![(Label::new("result"), GlobalType::End)],
                    ),
                ),
                (Label::new("quit"), GlobalType::End),
            ],
        ),
        "ring" => GlobalType::mu(
            "loop",
            GlobalType::comm(
                "A",
                "B",
                vec![(
                    Label::new("token"),
                    GlobalType::comm(
                        "B",
                        "C",
                        vec![(
                            Label::new("token"),
                            GlobalType::comm(
                                "C",
                                "A",
                                vec![(Label::new("token"), GlobalType::var("loop"))],
                            ),
                        )],
                    ),
                )],
            ),
        ),
        _ => {
            return Err(format!(
                "Unknown sample: {}. Use 'ping-pong', 'calculator', or 'ring'",
                sample
            ))
        }
    };

    let json = global_to_json(&g);

    let output_str = if pretty {
        serde_json::to_string_pretty(&json).map_err(|e| e.to_string())?
    } else {
        serde_json::to_string(&json).map_err(|e| e.to_string())?
    };

    write_output(output, &output_str)
}

fn read_input(input: Option<PathBuf>) -> Result<String, String> {
    match input {
        Some(path) => fs::read_to_string(&path)
            .map_err(|e| format!("Failed to read {}: {}", path.display(), e)),
        None => {
            let mut buffer = String::new();
            io::stdin()
                .read_to_string(&mut buffer)
                .map_err(|e| format!("Failed to read stdin: {}", e))?;
            Ok(buffer)
        }
    }
}

fn write_output(output: Option<PathBuf>, content: &str) -> Result<(), String> {
    match output {
        Some(path) => {
            fs::write(&path, content)
                .map_err(|e| format!("Failed to write {}: {}", path.display(), e))?;
            println!("Wrote to {}", path.display());
        }
        None => {
            io::stdout()
                .write_all(content.as_bytes())
                .map_err(|e| format!("Failed to write stdout: {}", e))?;
            println!();
        }
    }
    Ok(())
}
