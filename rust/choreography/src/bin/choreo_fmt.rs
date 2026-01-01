use std::env;
use std::fs;
use std::io::{self, Read};

use anyhow::{bail, Context, Result};
use rumpsteak_aura_choreography::format_choreography_str;

fn main() -> Result<()> {
    let mut write = false;
    let mut files = Vec::new();

    for arg in env::args().skip(1) {
        match arg.as_str() {
            "-w" | "--write" => write = true,
            "-h" | "--help" => {
                print_usage();
                return Ok(());
            }
            _ => files.push(arg),
        }
    }

    if files.is_empty() {
        let input = read_stdin()?;
        let formatted = format_choreography_str(&input).map_err(anyhow::Error::msg)?;
        print!("{formatted}");
        return Ok(());
    }

    for file in files {
        if file == "-" {
            let input = read_stdin()?;
            let formatted = format_choreography_str(&input).map_err(anyhow::Error::msg)?;
            print!("{formatted}");
            continue;
        }

        let input =
            fs::read_to_string(&file).with_context(|| format!("failed to read {}", file))?;
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
    println!("choreo-fmt [-w|--write] [FILE...]");
    println!("  -w, --write   overwrite files in place");
    println!("  -            read from stdin");
}
