//! Golden File Management CLI
//!
//! This tool manages golden files for Rust ↔ Lean equivalence testing.
//!
//! # Commands
//!
//! - `regenerate` - Regenerate all golden files from Lean
//! - `check` - Check for golden file drift (fails if outdated)
//! - `add <name> <json>` - Add a new test case
//! - `list` - List all golden test cases
//!
//! # Examples
//!
//! ```bash
//! # Regenerate all golden files
//! cargo run -p telltale-lean-bridge --bin golden -- regenerate
//!
//! # Check for drift (CI)
//! cargo run -p telltale-lean-bridge --bin golden -- check
//!
//! # Add a new test case
//! cargo run -p telltale-lean-bridge --bin golden -- add my_protocol '{"kind":"comm",...}'
//! ```

use clap::{Parser, Subcommand};
use telltale_lean_bridge::equivalence::EquivalenceChecker;
use telltale_lean_bridge::import::json_to_global;
use telltale_lean_bridge::runner::LeanRunner;
use std::path::PathBuf;

#[derive(Parser)]
#[command(name = "golden")]
#[command(about = "Golden file management for Rust-Lean equivalence testing")]
struct Cli {
    #[command(subcommand)]
    command: Commands,

    /// Path to the golden files directory
    #[arg(long, default_value = "golden")]
    golden_dir: PathBuf,
}

#[derive(Subcommand)]
enum Commands {
    /// Regenerate all golden files from Lean
    Regenerate,

    /// Check for golden file drift (exits with error if drift detected)
    Check,

    /// Add a new test case
    Add {
        /// Name for the test case
        name: String,
        /// GlobalType as JSON string
        json: String,
    },

    /// List all golden test cases
    List,
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();

    // Resolve golden dir relative to manifest dir if not absolute
    let golden_dir = if cli.golden_dir.is_absolute() {
        cli.golden_dir
    } else {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(&cli.golden_dir)
    };

    match cli.command {
        Commands::Regenerate => cmd_regenerate(&golden_dir),
        Commands::Check => cmd_check(&golden_dir),
        Commands::Add { name, json } => cmd_add(&golden_dir, &name, &json),
        Commands::List => cmd_list(&golden_dir),
    }
}

/// Regenerate all golden files from Lean.
fn cmd_regenerate(golden_dir: &PathBuf) -> anyhow::Result<()> {
    require_lean()?;

    let checker = EquivalenceChecker::with_lean(golden_dir)?;
    let projection_dir = golden_dir.join("projection");

    if !projection_dir.exists() {
        println!("No golden files to regenerate");
        return Ok(());
    }

    let mut count = 0;

    for entry in std::fs::read_dir(&projection_dir)? {
        let entry = entry?;
        if !entry.file_type()?.is_dir() {
            continue;
        }

        let test_name = entry.file_name().to_string_lossy().to_string();
        let input_path = entry.path().join("input.json");

        if !input_path.exists() {
            println!("Skipping {} (no input.json)", test_name);
            continue;
        }

        // Load input
        let input: serde_json::Value =
            serde_json::from_str(&std::fs::read_to_string(&input_path)?)?;
        let global = json_to_global(&input)?;

        // Generate and write golden bundle
        let bundle = checker.generate_golden_bundle(&global)?;
        checker.write_golden_bundle(&test_name, &bundle)?;

        println!("Regenerated: {}", test_name);
        count += 1;
    }

    println!("\nRegenerated {} test cases", count);
    Ok(())
}

/// Check for golden file drift.
fn cmd_check(golden_dir: &PathBuf) -> anyhow::Result<()> {
    require_lean()?;

    let checker = EquivalenceChecker::with_lean(golden_dir)?;
    let drifted = checker.check_golden_drift()?;

    if drifted.is_empty() {
        println!("✓ All golden files are up-to-date");
        Ok(())
    } else {
        println!("✗ Golden file drift detected:");
        for item in &drifted {
            println!("  - {}", item);
        }
        println!("\nRun 'cargo run -p telltale-lean-bridge --bin golden -- regenerate' to update");
        std::process::exit(1);
    }
}

/// Add a new test case.
fn cmd_add(golden_dir: &PathBuf, name: &str, json: &str) -> anyhow::Result<()> {
    require_lean()?;

    // Parse the GlobalType
    let input: serde_json::Value = serde_json::from_str(json)?;
    let global = json_to_global(&input)?;

    // Generate golden bundle from Lean
    let checker = EquivalenceChecker::with_lean(golden_dir)?;
    let bundle = checker.generate_golden_bundle(&global)?;

    // Write to disk
    checker.write_golden_bundle(name, &bundle)?;

    println!("Added test case: {}", name);
    println!(
        "  Roles: {}",
        bundle
            .projections
            .keys()
            .cloned()
            .collect::<Vec<_>>()
            .join(", ")
    );
    Ok(())
}

/// List all golden test cases.
fn cmd_list(golden_dir: &std::path::Path) -> anyhow::Result<()> {
    let projection_dir = golden_dir.join("projection");

    if !projection_dir.exists() {
        println!("No golden files found at {:?}", projection_dir);
        return Ok(());
    }

    println!("Golden test cases:");
    println!();

    for entry in std::fs::read_dir(&projection_dir)? {
        let entry = entry?;
        if !entry.file_type()?.is_dir() {
            continue;
        }

        let test_name = entry.file_name().to_string_lossy().to_string();

        // Count role files
        let mut roles = Vec::new();
        for file in std::fs::read_dir(entry.path())? {
            let file = file?;
            let name = file.file_name().to_string_lossy().to_string();
            if name.ends_with(".expected.json") {
                roles.push(name.trim_end_matches(".expected.json").to_string());
            }
        }

        println!("  {} (roles: {})", test_name, roles.join(", "));
    }

    Ok(())
}

/// Require that Lean is available, or exit with helpful message.
fn require_lean() -> anyhow::Result<()> {
    if !LeanRunner::is_available() {
        eprintln!("Error: Lean runner not available");
        eprintln!();
        eprintln!("Build the Lean runner first:");
        eprintln!("  cd lean && lake build telltale_runner");
        eprintln!();
        eprintln!("Or with Nix:");
        eprintln!("  nix develop --command bash -c \"cd lean && lake build\"");
        std::process::exit(1);
    }
    Ok(())
}
