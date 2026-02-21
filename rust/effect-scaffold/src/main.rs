//! Generate deterministic `EffectHandler` integration stubs.

use std::env;
use std::fs::{self, OpenOptions};
use std::io::{ErrorKind, Write};
use std::path::{Path, PathBuf};

const DEFAULT_OUT_DIR: &str = "work/effect_handler_scaffold";
const DEFAULT_STRUCT_NAME: &str = "HostEffectHandler";
const DEFAULT_WITH_SIMULATOR: bool = true;

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
    let mut out_dir = DEFAULT_OUT_DIR.to_string();
    let mut struct_name = DEFAULT_STRUCT_NAME.to_string();
    let mut with_simulator = DEFAULT_WITH_SIMULATOR;
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
            "--with-simulator" => {
                with_simulator = true;
                i += 1;
            }
            "--no-simulator" => {
                with_simulator = false;
                i += 1;
            }
            _ if token.starts_with("out=") => {
                out_dir = token.trim_start_matches("out=").to_string();
                i += 1;
            }
            _ if token.starts_with("name=") => {
                struct_name = token.trim_start_matches("name=").to_string();
                i += 1;
            }
            _ if token.starts_with("simulator=") => {
                let value = token.trim_start_matches("simulator=");
                with_simulator = parse_bool_token(value)?;
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
        with_simulator,
        help,
    })
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

fn render_simulator_test_template(struct_name: &str) -> String {
    format!(
        "use std::collections::BTreeMap;

use telltale_simulator::contracts::{{assert_contracts, ContractCheckConfig}};
use telltale_simulator::harness::{{DirectAdapter, HarnessSpec, SimulationHarness}};
use telltale_simulator::material::{{MaterialParams, MeanFieldParams}};
use telltale_simulator::scenario::{{OutputConfig, Scenario}};
use telltale_types::{{FixedQ32, GlobalType, Label, LocalTypeR}};

use crate::effect_handler::{struct_name};

fn simulator_smoke_spec() -> HarnessSpec {{
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

    let global_type = GlobalType::send(\"A\", \"B\", Label::new(\"msg\"), GlobalType::End);
    let scenario = Scenario {{
        name: \"scaffold_sim_smoke\".to_string(),
        roles: vec![\"A\".to_string(), \"B\".to_string()],
        steps: 8,
        concurrency: 1,
        seed: 0,
        network: None,
        material: MaterialParams::MeanField(MeanFieldParams {{
            beta: FixedQ32::one(),
            species: vec![\"up\".into(), \"down\".into()],
            initial_state: vec![FixedQ32::half(), FixedQ32::half()],
            step_size: FixedQ32::from_ratio(1, 100).expect(\"0.01\"),
        }}),
        events: Vec::new(),
        properties: None,
        checkpoint_interval: None,
        output: OutputConfig::default(),
    }};

    HarnessSpec::new(local_types, global_type, scenario)
}}

#[test]
fn simulator_harness_contract_smoke_test() {{
    let adapter = DirectAdapter::new(&{struct_name});
    let harness = SimulationHarness::new(&adapter);
    let result = harness.run(&simulator_smoke_spec()).expect(\"harness run should succeed\");
    assert_contracts(&result, &ContractCheckConfig::default()).expect(\"contracts should pass\");
}}
"
    )
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
