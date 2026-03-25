//! Generate Rust effect interfaces and simulator scaffolds from Telltale DSL declarations.

use std::env;
use std::fs;
use std::path::PathBuf;

use telltale_choreography::compiler::parser::parse_choreography_str;
use telltale_parser::{generate_effect_interface_scaffold, generated_effect_families};

const DEFAULT_OUT_DIR: &str = "target/effect_handler_scaffold";
const DEFAULT_WITH_SIMULATOR: bool = true;

#[derive(Debug, Clone)]
struct ParsedArgs {
    out_dir: String,
    dsl_path: Option<String>,
    with_simulator: bool,
    help: bool,
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

    let out_dir = PathBuf::from(&parsed.out_dir);
    let dsl_path = parsed
        .dsl_path
        .as_ref()
        .ok_or_else(|| "missing required `--dsl path/to/protocol.tell`".to_string())?;
    let dsl_src =
        fs::read_to_string(dsl_path).map_err(|e| format!("failed to read '{dsl_path}': {e}"))?;
    let choreography =
        parse_choreography_str(&dsl_src).map_err(|e| format!("failed to parse DSL: {e}"))?;
    let families = generated_effect_families(&choreography);
    if families.is_empty() {
        return Err("DSL does not declare any effect interfaces".to_string());
    }

    let generated = generate_effect_interface_scaffold(&out_dir, &families, parsed.with_simulator)?;
    for path in generated {
        println!("generated: {}", path.display());
    }

    Ok(())
}

fn parse_args(args: &[String]) -> Result<ParsedArgs, String> {
    let mut parsed = ParsedArgs {
        out_dir: DEFAULT_OUT_DIR.to_string(),
        dsl_path: None,
        with_simulator: DEFAULT_WITH_SIMULATOR,
        help: false,
    };

    let mut i = 0;
    while i < args.len() {
        let consumed = parse_arg_token(&mut parsed, args, i)?;
        i += consumed;
    }

    Ok(parsed)
}

fn parse_arg_token(parsed: &mut ParsedArgs, args: &[String], idx: usize) -> Result<usize, String> {
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
        "--dsl" => {
            parsed.dsl_path = Some(required_flag_value(args, idx, "--dsl")?.to_string());
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
        _ if token.starts_with('-') => Err(format!("unknown flag: {token}")),
        _ => Err(format!(
            "unexpected positional argument: {token}; use --out <dir> and --dsl <file>"
        )),
    }
}

fn required_flag_value<'a>(args: &'a [String], idx: usize, flag: &str) -> Result<&'a str, String> {
    args.get(idx + 1)
        .map(std::string::String::as_str)
        .ok_or_else(|| format!("missing value after {flag}"))
}

fn print_help() {
    println!("effect-scaffold");
    println!();
    println!("Generate Rust effect interfaces and simulator scaffolds from Telltale effect declarations.");
    println!();
    println!("USAGE:");
    println!("  cargo run -p telltale-choreography --bin effect-scaffold -- --out OUT_DIR --dsl path/to/protocol.tell");
    println!("  cargo run -p telltale-choreography --bin effect-scaffold -- --out OUT_DIR --dsl path/to/protocol.tell --no-simulator");
    println!();
    println!("DEFAULTS:");
    println!("  OUT_DIR: {DEFAULT_OUT_DIR}");
    println!(
        "  SIMULATOR_HARNESS: {}",
        if DEFAULT_WITH_SIMULATOR {
            "enabled"
        } else {
            "disabled"
        }
    );
}
