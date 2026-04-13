use std::path::Path;
use std::process::Command;

use anyhow::{bail, Result};

pub fn run(repo_root: &Path) -> Result<()> {
    let status = Command::new("cargo")
        .args([
            "test",
            "-p",
            "telltale-bridge",
            "--test",
            "scale_budget_contracts",
            "--",
            "--nocapture",
        ])
        .env("TELLTALE_REQUIRE_LEAN_VALIDATOR", "1")
        .current_dir(repo_root)
        .status()?;
    if !status.success() {
        bail!("scale-budgets: cargo test failed");
    }
    println!("scale-budgets: ok");
    Ok(())
}
