//! Generate deterministic `EffectHandler` integration stubs.

use std::env;
use std::fs::{self, OpenOptions};
use std::io::{ErrorKind, Write};
use std::path::{Path, PathBuf};

const DEFAULT_OUT_DIR: &str = "target/effect_handler_scaffold";
const DEFAULT_STRUCT_NAME: &str = "HostEffectHandler";
const DEFAULT_WITH_SIMULATOR: bool = true;
const STRUCT_NAME_TEMPLATE_TOKEN: &str = "{{STRUCT_NAME}}";

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
    let handler_path = out_dir.join("effect_handler.rs");
    let test_path = out_dir.join("effect_handler_test.rs");
    let simulator_test_path = out_dir.join("simulator_harness_test.rs");
    let readme_path = out_dir.join("README.md");

    fs::create_dir_all(&out_dir).map_err(|e| {
        format!(
            "failed to create output directory '{}': {e}",
            out_dir.display()
        )
    })?;

    write_new_file(
        &handler_path,
        &render_handler_template(&parsed.struct_name),
        "handler stub",
    )?;
    write_new_file(
        &test_path,
        &render_test_template(&parsed.struct_name),
        "test stub",
    )?;
    if parsed.with_simulator {
        write_new_file(
            &simulator_test_path,
            &render_simulator_test_template(&parsed.struct_name),
            "simulator harness test stub",
        )?;
    }
    write_new_file(
        &readme_path,
        &render_readme_template(&parsed.struct_name, parsed.with_simulator),
        "scaffold README",
    )?;

    println!("generated: {}", handler_path.display());
    println!("generated: {}", test_path.display());
    if parsed.with_simulator {
        println!("generated: {}", simulator_test_path.display());
    }
    println!("generated: {}", readme_path.display());
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

fn write_new_file(path: &Path, content: &str, kind: &str) -> Result<(), String> {
    let mut file = match OpenOptions::new().write(true).create_new(true).open(path) {
        Ok(file) => file,
        Err(err) if err.kind() == ErrorKind::AlreadyExists => {
            return Err(format!(
                "{kind} already exists at '{}'; use a new output directory or remove existing files",
                path.display()
            ));
        }
        Err(err) => {
            return Err(format!("failed to create '{}': {err}", path.display()));
        }
    };
    file.write_all(content.as_bytes())
        .map_err(|e| format!("failed to write '{}': {e}", path.display()))
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
}
