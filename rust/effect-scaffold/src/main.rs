//! Generate deterministic `EffectHandler` integration stubs.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

const DEFAULT_OUT_DIR: &str = "target/effect_handler_scaffold";
const DEFAULT_STRUCT_NAME: &str = "HostEffectHandler";
const DEFAULT_WITH_SIMULATOR: bool = true;
const STRUCT_NAME_TEMPLATE_TOKEN: &str = "{{STRUCT_NAME}}";

#[derive(Debug, Clone)]
struct GeneratedFile {
    name: &'static str,
    kind: &'static str,
    content: String,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("error: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let args: Vec<String> = env::args().skip(1).collect();
    let parsed = parse_args(&args)?;
    if parsed.help {
        print_help();
        return Ok(());
    }

    if !is_valid_rust_identifier(&parsed.struct_name) {
        return Err("struct name must be a valid Rust identifier".to_string());
    }

    let out_dir = PathBuf::from(&parsed.out_dir);
    let generated = generate_scaffold(&out_dir, &parsed.struct_name, parsed.with_simulator)?;

    for path in generated {
        println!("generated: {}", path.display());
    }
    Ok(())
}

#[derive(Debug, Clone)]
struct ParsedArgs {
    out_dir: String,
    struct_name: String,
    with_simulator: bool,
    help: bool,
}

fn parse_args(args: &[String]) -> Result<ParsedArgs, String> {
    let mut parsed = ParsedArgs {
        out_dir: DEFAULT_OUT_DIR.to_string(),
        struct_name: DEFAULT_STRUCT_NAME.to_string(),
        with_simulator: DEFAULT_WITH_SIMULATOR,
        help: false,
    };
    let mut positionals = Vec::new();

    let mut i = 0;
    while i < args.len() {
        let consumed = parse_arg_token(&mut parsed, &mut positionals, args, i)?;
        i += consumed;
    }

    apply_positional_args(&mut parsed, &positionals)?;
    Ok(parsed)
}

fn parse_arg_token(
    parsed: &mut ParsedArgs,
    positionals: &mut Vec<String>,
    args: &[String],
    idx: usize,
) -> Result<usize, String> {
    let token = args[idx].as_str();
    match token {
        "-h" | "--help" => {
            parsed.help = true;
            Ok(1)
        }
        "--out" => {
            parsed.out_dir = required_flag_value(args, idx, "--out")?.to_string();
            Ok(2)
        }
        "--name" => {
            parsed.struct_name = required_flag_value(args, idx, "--name")?.to_string();
            Ok(2)
        }
        "--with-simulator" => {
            parsed.with_simulator = true;
            Ok(1)
        }
        "--no-simulator" => {
            parsed.with_simulator = false;
            Ok(1)
        }
        _ if token.starts_with("out=") => {
            parsed.out_dir = token.trim_start_matches("out=").to_string();
            Ok(1)
        }
        _ if token.starts_with("name=") => {
            parsed.struct_name = token.trim_start_matches("name=").to_string();
            Ok(1)
        }
        _ if token.starts_with("simulator=") => {
            let value = token.trim_start_matches("simulator=");
            parsed.with_simulator = parse_bool_token(value)?;
            Ok(1)
        }
        _ if token.starts_with('-') => Err(format!("unknown flag: {token}")),
        _ => {
            positionals.push(token.to_string());
            Ok(1)
        }
    }
}

fn required_flag_value<'a>(args: &'a [String], idx: usize, flag: &str) -> Result<&'a str, String> {
    args.get(idx + 1)
        .map(std::string::String::as_str)
        .ok_or_else(|| format!("missing value after {flag}"))
}

fn apply_positional_args(parsed: &mut ParsedArgs, positionals: &[String]) -> Result<(), String> {
    if positionals.len() > 2 {
        return Err(
            "too many positional arguments; expected at most: <out_dir> <struct_name>".to_string(),
        );
    }
    if let Some(out_dir) = positionals.first() {
        parsed.out_dir = out_dir.clone();
    }
    if let Some(struct_name) = positionals.get(1) {
        parsed.struct_name = struct_name.clone();
    }
    Ok(())
}

fn parse_bool_token(input: &str) -> Result<bool, String> {
    match input {
        "true" | "1" | "yes" | "on" => Ok(true),
        "false" | "0" | "no" | "off" => Ok(false),
        _ => Err(format!("invalid boolean value: {input}")),
    }
}

fn print_help() {
    println!("effect-scaffold");
    println!();
    println!("Generate deterministic EffectHandler + test stubs for VM integration.");
    println!();
    println!("USAGE:");
    println!("  cargo run -p effect-scaffold -- [OUT_DIR] [STRUCT_NAME]");
    println!("  cargo run -p effect-scaffold -- --out OUT_DIR --name STRUCT_NAME");
    println!("  cargo run -p effect-scaffold -- --out OUT_DIR --name STRUCT_NAME --no-simulator");
    println!();
    println!("DEFAULTS:");
    println!("  OUT_DIR: {DEFAULT_OUT_DIR}");
    println!("  STRUCT_NAME: {DEFAULT_STRUCT_NAME}");
    println!(
        "  SIMULATOR_HARNESS: {}",
        if DEFAULT_WITH_SIMULATOR {
            "enabled"
        } else {
            "disabled"
        }
    );
}

fn build_generated_files(struct_name: &str, with_simulator: bool) -> Vec<GeneratedFile> {
    let mut files = vec![
        GeneratedFile {
            name: "effect_handler.rs",
            kind: "handler stub",
            content: render_handler_template(struct_name),
        },
        GeneratedFile {
            name: "effect_handler_test.rs",
            kind: "test stub",
            content: render_test_template(struct_name),
        },
    ];

    if with_simulator {
        files.push(GeneratedFile {
            name: "simulator_harness_test.rs",
            kind: "simulator harness test stub",
            content: render_simulator_test_template(struct_name),
        });
    }

    files.push(GeneratedFile {
        name: "README.md",
        kind: "scaffold README",
        content: render_readme_template(struct_name, with_simulator),
    });

    files
}

fn generate_scaffold(
    out_dir: &Path,
    struct_name: &str,
    with_simulator: bool,
) -> Result<Vec<PathBuf>, String> {
    fs::create_dir_all(out_dir).map_err(|e| {
        format!(
            "failed to create output directory '{}': {e}",
            out_dir.display()
        )
    })?;

    let files = build_generated_files(struct_name, with_simulator);
    preflight_absent_targets(out_dir, &files)?;
    write_files_transactionally(out_dir, &files)
}

fn preflight_absent_targets(out_dir: &Path, files: &[GeneratedFile]) -> Result<(), String> {
    for file in files {
        let path = out_dir.join(file.name);
        if path.exists() {
            return Err(format!(
                "{} already exists at '{}'; use a new output directory or remove existing files",
                file.kind,
                path.display()
            ));
        }
    }
    Ok(())
}

fn write_files_transactionally(out_dir: &Path, files: &[GeneratedFile]) -> Result<Vec<PathBuf>, String> {
    let stage_dir = out_dir.join(format!(
        ".effect_scaffold_stage_{}_{}",
        std::process::id(),
        now_nanos()
    ));
    fs::create_dir_all(&stage_dir)
        .map_err(|e| format!("failed to create staging directory '{}': {e}", stage_dir.display()))?;

    for file in files {
        let stage_path = stage_dir.join(file.name);
        if let Err(err) = fs::write(&stage_path, &file.content) {
            drop(fs::remove_dir_all(&stage_dir));
            return Err(format!("failed to write staging file '{}': {err}", stage_path.display()));
        }
    }

    let mut moved = Vec::new();
    for file in files {
        let stage_path = stage_dir.join(file.name);
        let target_path = out_dir.join(file.name);
        if let Err(err) = fs::rename(&stage_path, &target_path) {
            rollback_moved_files(&moved);
            drop(fs::remove_dir_all(&stage_dir));
            return Err(format!(
                "failed to finalize '{}' from staging '{}': {err}",
                target_path.display(),
                stage_path.display()
            ));
        }
        moved.push(target_path);
    }

    if let Err(err) = fs::remove_dir(&stage_dir) {
        return Err(format!(
            "generated files but failed to clean staging directory '{}': {err}",
            stage_dir.display()
        ));
    }

    Ok(moved)
}

fn rollback_moved_files(paths: &[PathBuf]) {
    for path in paths {
        drop(fs::remove_file(path));
    }
}

fn now_nanos() -> u128 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos())
}

fn is_valid_rust_identifier(input: &str) -> bool {
    let mut chars = input.chars();
    match chars.next() {
        Some(c) if c == '_' || c.is_ascii_alphabetic() => {}
        _ => return false,
    }
    chars.all(|c| c == '_' || c.is_ascii_alphanumeric())
}

fn render_handler_template(struct_name: &str) -> String {
    render_struct_name_template(
        include_str!("../templates/effect_handler.rs.tmpl"),
        struct_name,
    )
}

fn render_test_template(struct_name: &str) -> String {
    render_struct_name_template(
        include_str!("../templates/effect_handler_test.rs.tmpl"),
        struct_name,
    )
}

fn render_simulator_test_template(struct_name: &str) -> String {
    render_struct_name_template(
        include_str!("../templates/simulator_harness_test.rs.tmpl"),
        struct_name,
    )
}

fn render_struct_name_template(template: &str, struct_name: &str) -> String {
    template.replace(STRUCT_NAME_TEMPLATE_TOKEN, struct_name)
}

fn render_readme_template(struct_name: &str, with_simulator: bool) -> String {
    let mut lines = vec![
        "# Effect Handler Scaffold".to_string(),
        "".to_string(),
        "This folder contains generated host integration stubs.".to_string(),
        "".to_string(),
        "## Files".to_string(),
        "".to_string(),
        "- `effect_handler.rs`: deterministic `EffectHandler` template.".to_string(),
        "- `effect_handler_test.rs`: VM smoke test for handler callbacks.".to_string(),
    ];

    if with_simulator {
        lines.push(
            "- `simulator_harness_test.rs`: simulator harness smoke test with contract checks."
                .to_string(),
        );
    }

    lines.extend([
        "".to_string(),
        "## Next Steps".to_string(),
        "".to_string(),
        format!(
            "1. Copy `effect_handler.rs` into your crate and rename `{struct_name}` if needed."
        ),
        "2. Add the generated test files to your test module.".to_string(),
        "3. Adapt protocol fixtures and role names to your integration.".to_string(),
    ]);

    if with_simulator {
        lines.push(
            "4. Keep the simulator contract test in CI to check replay and trace invariants."
                .to_string(),
        );
    }

    lines.push("".to_string());
    lines.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accepts_flag_and_positional_forms() {
        let parsed = parse_args(&[
            "--out".to_string(),
            "tmp/out".to_string(),
            "--name".to_string(),
            "MyHandler".to_string(),
        ])
        .expect("parse flag form");
        assert_eq!(parsed.out_dir, "tmp/out");
        assert_eq!(parsed.struct_name, "MyHandler");

        let parsed = parse_args(&["tmp/pos".to_string(), "PosHandler".to_string()])
            .expect("parse positional form");
        assert_eq!(parsed.out_dir, "tmp/pos");
        assert_eq!(parsed.struct_name, "PosHandler");
    }

    #[test]
    fn accepts_assignment_tokens_for_just_compatibility() {
        let parsed = parse_args(&[
            "out=tmp/assignment".to_string(),
            "name=AssignHandler".to_string(),
        ])
        .expect("parse assignment form");
        assert_eq!(parsed.out_dir, "tmp/assignment");
        assert_eq!(parsed.struct_name, "AssignHandler");
        assert!(parsed.with_simulator);
    }

    #[test]
    fn simulator_toggle_flags_are_supported() {
        let parsed = parse_args(&["--no-simulator".to_string()]).expect("parse no-simulator");
        assert!(!parsed.with_simulator);

        let parsed = parse_args(&["simulator=false".to_string()]).expect("parse simulator=false");
        assert!(!parsed.with_simulator);

        let parsed = parse_args(&["simulator=yes".to_string()]).expect("parse simulator=yes");
        assert!(parsed.with_simulator);
    }

    #[test]
    fn identifier_validation_matches_expected_examples() {
        assert!(is_valid_rust_identifier("HostEffectHandler"));
        assert!(is_valid_rust_identifier("_Internal"));
        assert!(!is_valid_rust_identifier("9bad"));
        assert!(!is_valid_rust_identifier("bad-name"));
        assert!(!is_valid_rust_identifier(""));
    }

    #[test]
    fn handler_template_fails_closed_on_missing_payload() {
        let rendered = render_handler_template("MyHandler");
        assert!(rendered.contains("missing payload in send_decision"));
        assert!(!rendered.contains("unwrap_or(Value::Unit)"));
    }

    #[test]
    fn scaffold_generation_writes_expected_files() {
        let out_dir = unique_temp_dir("effect_scaffold_ok");
        let generated = generate_scaffold(&out_dir, "MyHandler", true).expect("generation succeeds");

        assert_eq!(generated.len(), 4);
        assert!(out_dir.join("effect_handler.rs").exists());
        assert!(out_dir.join("effect_handler_test.rs").exists());
        assert!(out_dir.join("simulator_harness_test.rs").exists());
        assert!(out_dir.join("README.md").exists());

        drop(fs::remove_dir_all(out_dir));
    }

    #[test]
    fn preflight_rejects_existing_files_without_partial_writes() {
        let out_dir = unique_temp_dir("effect_scaffold_preflight");
        fs::create_dir_all(&out_dir).expect("create out dir");
        fs::write(out_dir.join("effect_handler_test.rs"), "already here")
            .expect("seed existing file");

        let error = generate_scaffold(&out_dir, "MyHandler", true).expect_err("preflight should fail");
        assert!(error.contains("effect_handler_test.rs"));
        assert!(!out_dir.join("effect_handler.rs").exists());
        assert!(!out_dir.join("simulator_harness_test.rs").exists());
        assert!(!out_dir.join("README.md").exists());

        drop(fs::remove_dir_all(out_dir));
    }

    fn unique_temp_dir(prefix: &str) -> PathBuf {
        let mut path = env::temp_dir();
        path.push(format!("{prefix}_{}_{}", std::process::id(), now_nanos()));
        path
    }
}
