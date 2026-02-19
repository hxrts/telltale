use std::env;
use std::fs;
use std::io::{self, Read};

use anyhow::{bail, Context, Result};
use telltale_choreography::compiler::explain_lowering;
use telltale_choreography::format_choreography_str;

fn main() -> Result<()> {
    let mut write = false;
    let mut explain = false;
    let mut files = Vec::new();

    for arg in env::args().skip(1) {
        match arg.as_str() {
            "-w" | "--write" => write = true,
            "--explain-lowering" => explain = true,
            "-h" | "--help" => {
                print_usage();
                return Ok(());
            }
            _ => files.push(arg),
        }
    }

    if write && explain {
        bail!("--write and --explain-lowering cannot be used together");
    }

    if files.is_empty() {
        let input = read_stdin()?;
        if explain {
            let report = explain_lowering(&input).map_err(anyhow::Error::msg)?;
            print!("{report}");
        } else {
            let formatted = format_choreography_str(&input).map_err(anyhow::Error::msg)?;
            print!("{formatted}");
        }
        return Ok(());
    }

    for file in files {
        if file == "-" {
            let input = read_stdin()?;
            if explain {
                let report = explain_lowering(&input).map_err(anyhow::Error::msg)?;
                print!("{report}");
            } else {
                let formatted = format_choreography_str(&input).map_err(anyhow::Error::msg)?;
                print!("{formatted}");
            }
            continue;
        }

        let input =
            fs::read_to_string(&file).with_context(|| format!("failed to read {}", file))?;
        if explain {
            println!("==> {file} <==");
            let report = explain_lowering(&input).map_err(anyhow::Error::msg)?;
            print!("{report}");
            if !report.ends_with('\n') {
                println!();
            }
            continue;
        }
        let formatted = format_choreography_str(&input).map_err(anyhow::Error::msg)?;

        if write {
            if formatted != input {
                fs::write(&file, formatted).with_context(|| format!("failed to write {}", file))?;
            }
        } else {
            println!("==> {file} <==");
            print!("{formatted}");
            if !formatted.ends_with('\n') {
                println!();
            }
        }
    }

    Ok(())
}

fn read_stdin() -> Result<String> {
    let mut buf = String::new();
    io::stdin().read_to_string(&mut buf)?;
    if buf.trim().is_empty() {
        bail!("no input provided");
    }
    Ok(buf)
}

fn print_usage() {
    println!("choreo-fmt [-w|--write] [--explain-lowering] [FILE...]");
    println!("  -w, --write   overwrite files in place");
    println!("  --explain-lowering  print canonical lowering report");
    println!("  -            read from stdin");
}
