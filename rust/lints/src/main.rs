//! Repo-local AST lint checks for Telltale boundary policies.

mod common;
mod session_ingress;
mod style;
mod time_domain;

use std::env;
use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    SessionIngress,
    TimeDomain,
    Style,
}

impl Mode {
    fn parse(raw: &str) -> Result<Self, String> {
        match raw {
            "session-ingress" => Ok(Self::SessionIngress),
            "time-domain" => Ok(Self::TimeDomain),
            "style" => Ok(Self::Style),
            other => Err(format!("unknown lint mode: {other}")),
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::SessionIngress => "session-ingress",
            Self::TimeDomain => "time-domain",
            Self::Style => "style",
        }
    }
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut args = env::args().skip(1);
    let mode = args
        .next()
        .ok_or_else(|| "usage: telltale-lints <mode> <path> [<path> ...]".to_string())
        .and_then(|value| Mode::parse(&value))?;
    let paths = args.map(PathBuf::from).collect::<Vec<_>>();
    if paths.is_empty() {
        return Err("expected at least one path to scan".to_string());
    }

    let mut rust_files = Vec::new();
    for path in &paths {
        collect_rust_files(path, &mut rust_files)?;
    }
    rust_files.sort();
    rust_files.dedup();

    let mut violations = Vec::new();
    for file in &rust_files {
        let source = fs::read_to_string(file)
            .map_err(|error| format!("failed to read {}: {error}", file.display()))?;
        let syntax = syn::parse_file(&source)
            .map_err(|error| format!("failed to parse {}: {error}", file.display()))?;
        let file_violations = match mode {
            Mode::SessionIngress => session_ingress::scan(file, &syntax),
            Mode::TimeDomain => time_domain::scan(file, &syntax),
            Mode::Style => style::scan(file, &source, &syntax),
        };
        violations.extend(file_violations);
    }

    if !violations.is_empty() {
        for violation in violations {
            eprintln!("{violation}");
        }
        return Err(format!("{} violations remain", mode.name()));
    }

    println!("{}: clean", mode.name());
    Ok(())
}

fn collect_rust_files(path: &Path, files: &mut Vec<PathBuf>) -> Result<(), String> {
    if path.is_file() {
        if path.extension() == Some(OsStr::new("rs")) {
            files.push(path.to_path_buf());
        }
        return Ok(());
    }
    if !path.is_dir() {
        return Err(format!("path does not exist: {}", path.display()));
    }

    for entry in fs::read_dir(path)
        .map_err(|error| format!("failed to read directory {}: {error}", path.display()))?
    {
        let entry = entry.map_err(|error| {
            format!("failed to read directory entry {}: {error}", path.display())
        })?;
        let entry_path = entry.path();
        if entry_path.is_dir() {
            collect_rust_files(&entry_path, files)?;
        } else if entry_path.extension() == Some(OsStr::new("rs")) {
            files.push(entry_path);
        }
    }

    Ok(())
}
