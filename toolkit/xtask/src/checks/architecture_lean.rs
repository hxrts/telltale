use std::path::Path;
use std::process::Command;

use anyhow::{bail, Result};

/// Run rg in the lean dir and return matching lines, or empty string if no matches.
fn scan(pattern: &str, lean_dir: &Path) -> Result<String> {
    let output = Command::new("rg")
        .args([
            "-n",
            "--pcre2",
            pattern,
            lean_dir.to_str().unwrap(),
            "-g",
            "*.lean",
            "-g",
            "!.lake/**",
            "-g",
            "!**/.lake/**",
            "-g",
            "!target/**",
        ])
        .output()?;
    Ok(String::from_utf8_lossy(&output.stdout).to_string())
}

fn count_hits(hits: &str) -> usize {
    hits.lines().filter(|l| !l.is_empty()).count()
}

pub fn run(repo_root: &Path) -> Result<()> {
    let lean_dir = repo_root.join("lean");
    let mut errors: usize = 0;
    let mut warnings: usize = 0;

    // ── Escape Hatches ───────────────────────────────────────

    println!("\n== Lean Escape Hatches ==");

    let sorry_hits = scan(r"\bsorry\b", &lean_dir)?;
    let sorry_count = count_hits(&sorry_hits);
    if sorry_count > 0 {
        eprintln!("VIOLATION  No sorry proofs ({sorry_count})");
        eprintln!("{sorry_hits}");
        errors += sorry_count;
    } else {
        println!("OK  No sorry proofs");
    }

    let axiom_hits = scan(r"^[[:space:]]*axiom\b", &lean_dir)?;
    let axiom_count = count_hits(&axiom_hits);
    if axiom_count > 0 {
        eprintln!("VIOLATION  No bare axiom declarations ({axiom_count})");
        eprintln!("{axiom_hits}");
        errors += axiom_count;
    } else {
        println!("OK  No bare axiom declarations");
    }

    // ── Style-Guide Conformance ───────────────────────────────

    println!("\n== Lean Style-Guide Conformance ==");

    let placeholder_hits = scan(r"\bProp\s*:=\s*True\b", &lean_dir)?;
    let placeholder_count = count_hits(&placeholder_hits);
    if placeholder_count > 0 {
        eprintln!("VIOLATION  No Prop := True placeholder contracts ({placeholder_count})");
        eprintln!("{placeholder_hits}");
        errors += placeholder_count;
    } else {
        println!("OK  No Prop := True placeholder contracts in production paths");
    }

    let todo_hits = scan(r"\b(TODO|FIXME|HACK|XXX|WIP|REVISIT)\b", &lean_dir)?;
    let todo_count = count_hits(&todo_hits);
    if todo_count > 0 {
        println!("WARNING  Technical debt markers in source ({todo_count})");
        warnings += todo_count;
    } else {
        println!("OK  Technical debt markers in source");
    }

    let placeholder_comment_hits = scan(
        r"(--|/-[^!]).*\b(stub|placeholder|dummy|temporary|temp fix|for now|hardcoded|hard-coded|in a real implementation|not yet implemented|needs to be (implemented|fixed|replaced|updated)|will be (implemented|replaced)|should (eventually|later)|come back to this)\b",
        &lean_dir,
    )?;
    let placeholder_comment_count = count_hits(&placeholder_comment_hits);
    if placeholder_comment_count > 0 {
        println!("WARNING  Placeholder/stub indicators in comments ({placeholder_comment_count})");
        warnings += placeholder_comment_count;
    } else {
        println!("OK  Placeholder/stub indicators in comments");
    }

    // Root import checks (specific facade files)
    let root_facades = &[
        lean_dir.join("SessionTypes.lean"),
        lean_dir.join("Choreography.lean"),
        lean_dir.join("Protocol.lean"),
        lean_dir.join("Runtime.lean"),
    ];
    let mut root_import_hits = String::new();
    for facade in root_facades {
        if !facade.exists() {
            continue;
        }
        let output = Command::new("rg")
            .args([
                "-n",
                "--pcre2",
                r"^(import .*\b(MutualTest|LocalTypeDBExamples|Examples|Tests)\b)",
                facade.to_str().unwrap(),
            ])
            .output()?;
        root_import_hits.push_str(&String::from_utf8_lossy(&output.stdout));
    }
    let root_import_count = count_hits(&root_import_hits);
    if root_import_count > 0 {
        eprintln!("VIOLATION  Root facades avoid debug/example/test imports ({root_import_count})");
        eprintln!("{root_import_hits}");
        errors += root_import_count;
    } else {
        println!("OK  Root facades avoid debug/example/test imports");
    }

    // Legacy projection import check
    let legacy_proj_output = Command::new("rg")
        .args([
            "-n",
            "--pcre2",
            r"^import[[:space:]]+Choreography\.Projection\.(Trans|Projectb|ProjectProps|Embed|EmbedProps|Erasure|Regression)\b",
            lean_dir.to_str().unwrap(),
            "-g",
            "*.lean",
            "-g",
            "!.lake/**",
            "-g",
            "!target/**",
        ])
        .output()?;
    let legacy_proj_raw = String::from_utf8_lossy(&legacy_proj_output.stdout).to_string();
    // Filter out files in /Choreography/Projection/ and /Runtime/Tests/
    let legacy_proj_hits: String = legacy_proj_raw
        .lines()
        .filter(|l| !l.contains("/Choreography/Projection/") && !l.contains("/Runtime/Tests/"))
        .map(|l| format!("{l}\n"))
        .collect();
    let legacy_proj_count = count_hits(&legacy_proj_hits);
    if legacy_proj_count > 0 {
        eprintln!("VIOLATION  No deprecated legacy projection imports in production modules ({legacy_proj_count})");
        eprintln!("{legacy_proj_hits}");
        errors += legacy_proj_count;
    } else {
        println!("OK  No deprecated legacy projection imports in production modules");
    }

    // Legacy TheoremPack import check
    let legacy_tp_output = Command::new("rg")
        .args([
            "-n",
            "--pcre2",
            r"^import[[:space:]]+Runtime\.Proofs\.TheoremPack$",
            lean_dir.to_str().unwrap(),
            "-g",
            "*.lean",
            "-g",
            "!.lake/**",
            "-g",
            "!target/**",
        ])
        .output()?;
    let legacy_tp_raw = String::from_utf8_lossy(&legacy_tp_output.stdout).to_string();
    let legacy_tp_hits: String = legacy_tp_raw
        .lines()
        .filter(|l| {
            !l.contains("/Runtime/Proofs/Examples/")
                && !l.contains("/Runtime/Proofs/TheoremPack/Artifacts.lean:")
        })
        .map(|l| format!("{l}\n"))
        .collect();
    let legacy_tp_count = count_hits(&legacy_tp_hits);
    if legacy_tp_count > 0 {
        eprintln!("VIOLATION  No direct Runtime.Proofs.TheoremPack imports outside migration shims/examples ({legacy_tp_count})");
        eprintln!("{legacy_tp_hits}");
        errors += legacy_tp_count;
    } else {
        println!(
            "OK  No direct Runtime.Proofs.TheoremPack imports outside migration shims/examples"
        );
    }

    // File length, problem headers, section headers, module docs - use rg to find long files
    // (We use the filesystem approach for these style metrics)
    let long_files = collect_long_files(&lean_dir, 500)?;
    if !long_files.is_empty() {
        let n = long_files.len();
        println!("WARNING  Files stay within style-guide length target (<= 500 lines) ({n})");
        warnings += n;
    } else {
        println!("OK  Files stay within style-guide length target (<= 500 lines)");
    }

    // ── Summary ──────────────────────────────────────────────

    println!("\n== Summary ==");
    println!("Errors:   {errors}");
    println!("Warnings: {warnings}");

    if errors > 0 {
        bail!("Lean architecture/style check failed: {errors} error(s), {warnings} warning(s).");
    }

    if warnings > 0 {
        println!("Lean architecture/style check passed with warnings: {warnings} warning(s).");
    } else {
        println!("Lean architecture/style check passed.");
    }

    Ok(())
}

fn collect_long_files(lean_dir: &Path, threshold: usize) -> Result<Vec<String>> {
    let mut results = Vec::new();
    for entry in walkdir::WalkDir::new(lean_dir)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| {
            e.file_type().is_file() && e.path().extension().and_then(|s| s.to_str()) == Some("lean")
        })
    {
        let path = entry.path();
        let path_str = path.to_str().unwrap_or("");
        if path_str.contains("/.lake/") || path_str.contains("/target/") {
            continue;
        }
        if path_str.contains("/Tests/")
            || path_str.contains("/Examples/")
            || path_str.contains("MutualTest")
        {
            continue;
        }
        let text = std::fs::read_to_string(path)?;
        let line_count = text.lines().count();
        if line_count > threshold {
            results.push(format!("{}:{line_count}", path.display()));
        }
    }
    Ok(results)
}
