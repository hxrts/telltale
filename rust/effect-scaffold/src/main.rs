//! Generate deterministic `EffectHandler` integration stubs.

use std::env;
use std::fs::{self, OpenOptions};
use std::io::{ErrorKind, Write};
use std::path::{Path, PathBuf};

const DEFAULT_OUT_DIR: &str = "work/effect_handler_scaffold";
const DEFAULT_STRUCT_NAME: &str = "HostEffectHandler";

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

    println!("generated: {}", handler_path.display());
    println!("generated: {}", test_path.display());
    Ok(())
}

#[derive(Debug, Clone)]
struct ParsedArgs {
    out_dir: String,
    struct_name: String,
    help: bool,
}

fn parse_args(args: &[String]) -> Result<ParsedArgs, String> {
    let mut out_dir = DEFAULT_OUT_DIR.to_string();
    let mut struct_name = DEFAULT_STRUCT_NAME.to_string();
    let mut help = false;
    let mut positionals = Vec::new();

    let mut i = 0;
    while i < args.len() {
        let token = args[i].as_str();
        match token {
            "-h" | "--help" => {
                help = true;
                i += 1;
            }
            "--out" => {
                let Some(next) = args.get(i + 1) else {
                    return Err("missing value after --out".to_string());
                };
                out_dir = next.clone();
                i += 2;
            }
            "--name" => {
                let Some(next) = args.get(i + 1) else {
                    return Err("missing value after --name".to_string());
                };
                struct_name = next.clone();
                i += 2;
            }
            _ if token.starts_with("out=") => {
                out_dir = token.trim_start_matches("out=").to_string();
                i += 1;
            }
            _ if token.starts_with("name=") => {
                struct_name = token.trim_start_matches("name=").to_string();
                i += 1;
            }
            _ if token.starts_with('-') => {
                return Err(format!("unknown flag: {token}"));
            }
            _ => {
                positionals.push(token.to_string());
                i += 1;
            }
        }
    }

    if !positionals.is_empty() {
        out_dir = positionals[0].clone();
    }
    if positionals.len() > 1 {
        struct_name = positionals[1].clone();
    }
    if positionals.len() > 2 {
        return Err(
            "too many positional arguments; expected at most: <out_dir> <struct_name>".to_string(),
        );
    }

    Ok(ParsedArgs {
        out_dir,
        struct_name,
        help,
    })
}

fn print_help() {
    println!("effect-scaffold");
    println!();
    println!("Generate deterministic EffectHandler + test stubs for VM integration.");
    println!();
    println!("USAGE:");
    println!("  cargo run -p effect-scaffold -- [OUT_DIR] [STRUCT_NAME]");
    println!("  cargo run -p effect-scaffold -- --out OUT_DIR --name STRUCT_NAME");
    println!();
    println!("DEFAULTS:");
    println!("  OUT_DIR: {DEFAULT_OUT_DIR}");
    println!("  STRUCT_NAME: {DEFAULT_STRUCT_NAME}");
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
    format!(
        "use telltale_vm::coroutine::Value;
use telltale_vm::effect::{{
    AcquireDecision, EffectHandler, SendDecision, SendDecisionFastPathInput, SendDecisionInput,
    TopologyPerturbation,
}};
use telltale_vm::output_condition::OutputConditionHint;
use telltale_vm::session::SessionId;

/// Deterministic host integration scaffold.
pub struct {struct_name};

impl EffectHandler for {struct_name} {{
    fn handler_identity(&self) -> String {{
        \"{struct_name}\".to_string()
    }}

    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> Result<Value, String> {{
        Ok(Value::Unit)
    }}

    fn send_decision_fast_path(
        &self,
        _fast_path: SendDecisionFastPathInput<'_>,
        _state: &[Value],
        _payload: Option<&Value>,
    ) -> Option<Result<SendDecision, String>> {{
        None
    }}

    fn send_decision(&self, input: SendDecisionInput<'_>) -> Result<SendDecision, String> {{
        Ok(SendDecision::Deliver(input.payload.unwrap_or(Value::Unit)))
    }}

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<Value>,
        _payload: &Value,
    ) -> Result<(), String> {{
        Ok(())
    }}

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[Value],
    ) -> Result<String, String> {{
        labels
            .first()
            .cloned()
            .ok_or_else(|| \"no labels available\".to_string())
    }}

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {{
        Ok(())
    }}

    fn handle_acquire(
        &self,
        _sid: SessionId,
        _role: &str,
        _layer: &str,
        _state: &[Value],
    ) -> Result<AcquireDecision, String> {{
        Ok(AcquireDecision::Grant(Value::Unit))
    }}

    fn handle_release(
        &self,
        _sid: SessionId,
        _role: &str,
        _layer: &str,
        _evidence: &Value,
        _state: &[Value],
    ) -> Result<(), String> {{
        Ok(())
    }}

    fn topology_events(&self, _tick: u64) -> Result<Vec<TopologyPerturbation>, String> {{
        Ok(Vec::new())
    }}

    fn output_condition_hint(
        &self,
        _sid: SessionId,
        _role: &str,
        _state: &[Value],
    ) -> Option<OutputConditionHint> {{
        None
    }}
}}

// Integration checklist:
// - [ ] Keep all callback results deterministic for equal inputs.
// - [ ] Keep handler_identity stable for the full runtime lifetime.
// - [ ] Do not mutate shared host state outside explicit callback boundaries.
// - [ ] Validate host assumptions for topology ordering and session ownership.
"
    )
}

fn render_test_template(struct_name: &str) -> String {
    format!(
        "use telltale_vm::loader::CodeImage;
use telltale_vm::vm::{{EffectTraceCaptureMode, VMConfig, VM}};
use telltale_types::{{GlobalType, Label, LocalTypeR}};

use std::collections::BTreeMap;

use crate::effect_handler::{struct_name};

fn simple_send_recv_image() -> CodeImage {{
    let mut local_types = BTreeMap::new();
    local_types.insert(
        \"A\".to_string(),
        LocalTypeR::Send {{
            partner: \"B\".into(),
            branches: vec![(Label::new(\"msg\"), None, LocalTypeR::End)],
        }},
    );
    local_types.insert(
        \"B\".to_string(),
        LocalTypeR::Recv {{
            partner: \"A\".into(),
            branches: vec![(Label::new(\"msg\"), None, LocalTypeR::End)],
        }},
    );

    let global = GlobalType::send(\"A\", \"B\", Label::new(\"msg\"), GlobalType::End);
    CodeImage::from_local_types(&local_types, &global)
}}

#[test]
fn host_handler_smoke_test() {{
    let image = simple_send_recv_image();
    let mut vm = VM::new(VMConfig {{
        effect_trace_capture_mode: EffectTraceCaptureMode::Full,
        host_contract_assertions: true,
        ..VMConfig::default()
    }});
    vm.load_choreography(&image).expect(\"load choreography\");
    vm.run(&{struct_name}, 100).expect(\"run should succeed\");
}}
"
    )
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
