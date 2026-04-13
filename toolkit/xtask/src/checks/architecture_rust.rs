use std::path::Path;
use std::process::Command;

use anyhow::{bail, Result};

fn scan_rg(pattern: &str, paths: &[&Path], extra_args: &[&str]) -> Result<String> {
    let mut cmd = Command::new("rg");
    cmd.arg("-n").arg("--pcre2").arg(pattern);
    for p in paths {
        cmd.arg(p);
    }
    for a in extra_args {
        cmd.arg(a);
    }
    let output = cmd.output()?;
    Ok(String::from_utf8_lossy(&output.stdout).to_string())
}

fn count_hits(hits: &str) -> usize {
    hits.lines().filter(|l| !l.is_empty()).count()
}

pub fn run(repo_root: &Path) -> Result<()> {
    let rust_dir = repo_root.join("rust");

    let determinism_runtime = &[rust_dir.join("machine/src"), rust_dir.join("simulator/src")];
    let vm_kernel = &[
        rust_dir.join("machine/src/kernel.rs"),
        rust_dir.join("machine/src/engine"),
        rust_dir.join("machine/src/threaded"),
        rust_dir.join("machine/src/scheduler"),
        rust_dir.join("machine/src/session"),
        rust_dir.join("machine/src/coroutine.rs"),
        rust_dir.join("machine/src/exec"),
    ];
    let core_runtime = &[rust_dir.join("machine/src"), rust_dir.join("simulator/src")];

    let mut errors: usize = 0;
    let mut warnings: usize = 0;

    println!("\n== Rust Safety and Determinism ==");

    // Unsafe usage in determinism scope
    let unsafe_hits = scan_rg(
        r"unsafe\s*\{",
        &determinism_runtime
            .iter()
            .map(|p| p.as_path())
            .collect::<Vec<_>>(),
        &["-g", "*.rs", "-g", "!**/tests/**"],
    )?;
    let unsafe_count = count_hits(&unsafe_hits);
    if unsafe_count > 0 {
        eprintln!(
            "VIOLATION  No unsafe blocks in determinism-critical runtime scope ({unsafe_count})"
        );
        eprintln!("{unsafe_hits}");
        errors += unsafe_count;
    } else {
        println!("OK  No unsafe blocks in determinism-critical runtime scope");
    }

    // HashMap in determinism scope (non-deterministic ordering)
    let hashmap_hits = scan_rg(
        r"\bHashMap\b",
        &determinism_runtime
            .iter()
            .map(|p| p.as_path())
            .collect::<Vec<_>>(),
        &["-g", "*.rs"],
    )?;
    let hashmap_count = count_hits(&hashmap_hits);
    if hashmap_count > 0 {
        eprintln!(
            "VIOLATION  No HashMap in determinism-critical scope (use BTreeMap) ({hashmap_count})"
        );
        eprintln!("{hashmap_hits}");
        errors += hashmap_count;
    } else {
        println!("OK  No HashMap in determinism-critical scope");
    }

    // HashSet in determinism scope
    let hashset_hits = scan_rg(
        r"\bHashSet\b",
        &determinism_runtime
            .iter()
            .map(|p| p.as_path())
            .collect::<Vec<_>>(),
        &["-g", "*.rs"],
    )?;
    let hashset_count = count_hits(&hashset_hits);
    if hashset_count > 0 {
        eprintln!(
            "VIOLATION  No HashSet in determinism-critical scope (use BTreeSet) ({hashset_count})"
        );
        eprintln!("{hashset_hits}");
        errors += hashset_count;
    } else {
        println!("OK  No HashSet in determinism-critical scope");
    }

    // f32/f64 in VM kernel
    let float_hits = scan_rg(
        r"\b(f32|f64)\b",
        &vm_kernel
            .iter()
            .filter(|p| p.exists())
            .map(|p| p.as_path())
            .collect::<Vec<_>>(),
        &["-g", "*.rs"],
    )?;
    let float_count = count_hits(&float_hits);
    if float_count > 0 {
        eprintln!("VIOLATION  No f32/f64 in VM kernel (numeric instability) ({float_count})");
        eprintln!("{float_hits}");
        errors += float_count;
    } else {
        println!("OK  No f32/f64 in VM kernel");
    }

    // unwrap() in core runtime (non-test)
    let unwrap_hits = scan_rg(
        r"\.unwrap\(\)",
        &core_runtime.iter().map(|p| p.as_path()).collect::<Vec<_>>(),
        &["-g", "*.rs", "-g", "!**/tests/**", "-g", "!**/benches/**"],
    )?;
    let unwrap_count = count_hits(&unwrap_hits);
    if unwrap_count > 0 {
        println!("WARNING  unwrap() calls in core runtime ({unwrap_count})");
        warnings += unwrap_count;
    } else {
        println!("OK  unwrap() calls in core runtime");
    }

    // TODO/FIXME in production runtime
    let todo_hits = scan_rg(
        r"\b(TODO|FIXME|HACK|XXX)\b",
        &core_runtime.iter().map(|p| p.as_path()).collect::<Vec<_>>(),
        &["-g", "*.rs", "-g", "!**/tests/**"],
    )?;
    let todo_count = count_hits(&todo_hits);
    if todo_count > 0 {
        println!("WARNING  Technical debt markers in production runtime ({todo_count})");
        warnings += todo_count;
    } else {
        println!("OK  Technical debt markers in production runtime");
    }

    // Check deprecated thread::sleep in runtime
    let sleep_hits = scan_rg(
        r"thread::sleep",
        &core_runtime.iter().map(|p| p.as_path()).collect::<Vec<_>>(),
        &["-g", "*.rs", "-g", "!**/tests/**"],
    )?;
    let sleep_count = count_hits(&sleep_hits);
    if sleep_count > 0 {
        eprintln!("VIOLATION  No thread::sleep in runtime (use timer abstraction) ({sleep_count})");
        eprintln!("{sleep_hits}");
        errors += sleep_count;
    } else {
        println!("OK  No thread::sleep in runtime");
    }

    // ── Summary ──────────────────────────────────────────────

    println!("\n== Summary ==");
    println!("Errors:   {errors}");
    println!("Warnings: {warnings}");

    if errors > 0 {
        bail!("Rust architecture/style check failed: {errors} error(s), {warnings} warning(s).");
    }

    if warnings > 0 {
        println!("Rust architecture/style check passed with warnings: {warnings} warning(s).");
    } else {
        println!("Rust architecture/style check passed.");
    }

    Ok(())
}
