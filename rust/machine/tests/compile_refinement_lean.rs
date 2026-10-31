#![allow(missing_docs)]
#![cfg(not(target_arch = "wasm32"))]
//! Refinement parity: the Rust bytecode compiler (`telltale_machine::compiler::compile`,
//! `CodeImage::from_local_types`) must emit the same instruction streams as the Lean
//! compiler `compileLocalTypeR` / `CodeImage.fromLocalTypes`, which is the compiler the
//! Lean `compile_refines` / `fromLocalTypes_refines` theorems are stated about.
//!
//! The Lean side is the `compile_local_type_export` executable
//! (`lean/Runtime/Tests/CompileLocalTypeExport.lean`). When it is absent the tests skip,
//! unless `TELLTALE_REQUIRE_COMPILE_LOCAL_TYPE_EXPORT` is set (non-`0`), in which case
//! they fail.

use std::collections::BTreeMap;
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

use serde_json::{json, Value};
use telltale_bridge::export::local_to_json;
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::Instr;
use telltale_types::{GlobalType, Label, LocalTypeR, ValType};

fn strict_export_required() -> bool {
    std::env::var("TELLTALE_REQUIRE_COMPILE_LOCAL_TYPE_EXPORT")
        .map(|value| value != "0")
        .unwrap_or(false)
}

fn export_path() -> Option<PathBuf> {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for _ in 0..5 {
        if path.join("lean/.lake").is_dir() {
            let candidate = path.join("lean/.lake/build/bin/compile_local_type_export");
            return candidate.exists().then_some(candidate);
        }
        if !path.pop() {
            break;
        }
    }
    None
}

/// Locate the Lean exporter, or skip (`None`) / panic in strict mode.
fn require_export() -> Option<PathBuf> {
    match export_path() {
        Some(path) => Some(path),
        None if strict_export_required() => {
            panic!("compile_local_type_export binary required but not found")
        }
        None => {
            eprintln!("SKIPPED: lean/.lake/build/bin/compile_local_type_export not built");
            None
        }
    }
}

/// Normalized instruction encoding shared with the Lean exporter.
fn instr_json(instr: &Instr) -> Value {
    match instr {
        Instr::Send { chan, val } => json!(["send", chan, val]),
        Instr::Receive { chan, dst } => json!(["receive", chan, dst]),
        Instr::Offer { chan, label } => json!(["offer", chan, label]),
        Instr::Choose { chan, table } => {
            let table: Vec<Value> = table.iter().map(|(l, pc)| json!([l, pc])).collect();
            json!(["choose", chan, table])
        }
        Instr::Jump { target } => json!(["jump", target]),
        Instr::Halt => json!(["halt"]),
        Instr::Invoke { .. } => json!(["invoke"]),
        _ => json!(["unsupported"]),
    }
}

fn code_json(code: &[Instr]) -> Value {
    Value::Array(code.iter().map(instr_json).collect())
}

/// Shift jump/choose targets by `offset` (Lean `relocateInstr`).
fn relocate(instr: &Instr, offset: usize) -> Instr {
    match instr {
        Instr::Choose { chan, table } => Instr::Choose {
            chan: *chan,
            table: table
                .iter()
                .map(|(l, pc)| (l.clone(), pc + offset))
                .collect(),
        },
        Instr::Jump { target } => Instr::Jump {
            target: target + offset,
        },
        other => other.clone(),
    }
}

fn run_export(binary: &PathBuf, locals: &[(&str, LocalTypeR)]) -> Value {
    let entries: Vec<Value> = locals
        .iter()
        .map(|(role, lt)| json!([role, local_to_json(lt)]))
        .collect();
    let input = json!({ "local_types": entries }).to_string();
    let mut child = Command::new(binary)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn compile_local_type_export");
    child
        .stdin
        .take()
        .expect("stdin")
        .write_all(input.as_bytes())
        .expect("write stdin");
    let output = child.wait_with_output().expect("wait exporter");
    assert!(
        output.status.success(),
        "exporter failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).expect("exporter JSON")
}

fn lean_program(out: &Value, role: &str) -> Value {
    out["programs"]
        .as_array()
        .expect("programs")
        .iter()
        .find(|entry| entry[0] == role)
        .map(|entry| entry[1].clone())
        .expect("role program")
}

fn lbl(name: &str) -> Label {
    Label::new(name)
}

fn nat() -> Option<ValType> {
    Some(ValType::Nat)
}

fn send(partner: &str, branches: Vec<(&str, Option<ValType>, LocalTypeR)>) -> LocalTypeR {
    LocalTypeR::Send {
        partner: partner.into(),
        branches: branches
            .into_iter()
            .map(|(l, vt, c)| (lbl(l), vt, c))
            .collect(),
    }
}

fn recv(partner: &str, branches: Vec<(&str, Option<ValType>, LocalTypeR)>) -> LocalTypeR {
    LocalTypeR::Recv {
        partner: partner.into(),
        branches: branches
            .into_iter()
            .map(|(l, vt, c)| (lbl(l), vt, c))
            .collect(),
    }
}

/// Corpus of single-role local types on which the compilers must agree.
fn corpus() -> Vec<(&'static str, LocalTypeR)> {
    use LocalTypeR::{End, Var};
    vec![
        ("send_value", send("B", vec![("m", nat(), End)])),
        ("recv_value", recv("A", vec![("m", nat(), End)])),
        // Label-only single branches compile exactly like value branches.
        ("send_label_only", send("B", vec![("m", None, End)])),
        ("recv_label_only", recv("A", vec![("m", None, End)])),
        (
            "multi_branch_send",
            send(
                "B",
                vec![
                    ("yes", None, send("B", vec![("v", nat(), End)])),
                    ("no", None, End),
                ],
            ),
        ),
        (
            "multi_branch_recv_table",
            recv(
                "A",
                vec![
                    ("a", None, recv("A", vec![("v", nat(), End)])),
                    ("b", None, End),
                    ("c", None, send("A", vec![("w", nat(), End)])),
                ],
            ),
        ),
        (
            "mu_loop_send_recv",
            LocalTypeR::mu(
                "t",
                send(
                    "B",
                    vec![(
                        "ping",
                        nat(),
                        recv("B", vec![("pong", nat(), Var("t".into()))]),
                    )],
                ),
            ),
        ),
        (
            "nested_mu_var_jump",
            LocalTypeR::mu(
                "t",
                send(
                    "B",
                    vec![(
                        "x",
                        nat(),
                        LocalTypeR::mu(
                            "s",
                            recv(
                                "B",
                                vec![
                                    ("inner", None, Var("s".into())),
                                    ("outer", None, Var("t".into())),
                                    ("stop", None, End),
                                ],
                            ),
                        ),
                    )],
                ),
            ),
        ),
        (
            "loop_exit_via_choice",
            LocalTypeR::mu(
                "t",
                recv(
                    "A",
                    vec![
                        ("more", None, recv("A", vec![("v", nat(), Var("t".into()))])),
                        ("done", None, End),
                    ],
                ),
            ),
        ),
        (
            "unbound_var",
            send("B", vec![("m", nat(), Var("nowhere".into()))]),
        ),
        ("empty_send_branches", send("B", vec![])),
        ("end", End),
    ]
}

#[test]
fn compile_refinement_corpus_matches_lean() {
    let Some(binary) = require_export() else {
        return;
    };
    let corpus = corpus();
    assert!(corpus.len() >= 8);
    let locals: Vec<(&str, LocalTypeR)> = corpus.iter().map(|(n, lt)| (*n, lt.clone())).collect();
    let out = run_export(&binary, &locals);
    for (name, lt) in &corpus {
        let rust = code_json(&telltale_machine::compiler::compile(lt));
        let lean = lean_program(&out, name);
        assert_eq!(rust, lean, "compiler divergence on corpus case `{name}`");
    }
}

#[test]
fn compile_refinement_multi_role_image_matches_lean() {
    let Some(binary) = require_export() else {
        return;
    };
    use LocalTypeR::{End, Var};
    let a = LocalTypeR::mu(
        "t",
        send(
            "B",
            vec![
                ("go", None, send("C", vec![("v", nat(), Var("t".into()))])),
                ("stop", None, End),
            ],
        ),
    );
    let b = LocalTypeR::mu(
        "t",
        recv(
            "A",
            vec![("go", None, Var("t".into())), ("stop", None, End)],
        ),
    );
    let c = LocalTypeR::mu("t", recv("A", vec![("v", nat(), Var("t".into()))]));
    // Label-only single-branch handshake (compiled as value send/receive).
    let d = send(
        "E",
        vec![("ping", None, recv("E", vec![("pong", None, End)]))],
    );
    let e = recv(
        "D",
        vec![("ping", None, send("D", vec![("pong", None, End)]))],
    );
    // Deliberately unsorted input: both sides order roles lexicographically.
    let locals = vec![("E", e), ("C", c), ("A", a), ("D", d), ("B", b)];
    let local_types: BTreeMap<String, LocalTypeR> = locals
        .iter()
        .map(|(r, lt)| ((*r).to_string(), lt.clone()))
        .collect();
    let image = CodeImage::from_local_types(&local_types, &GlobalType::End);
    let out = run_export(&binary, &locals);

    // Per-role programs agree.
    for (role, program) in &image.programs {
        assert_eq!(
            code_json(program),
            lean_program(&out, role),
            "per-role divergence for `{role}`"
        );
    }

    // Lean flattens roles in sorted order with relocated targets; rebuild that from Rust.
    let mut flat = Vec::new();
    let mut entries = Vec::new();
    for (role, program) in &image.programs {
        let offset = flat.len();
        entries.push(json!([role, offset]));
        flat.extend(program.iter().map(|i| relocate(i, offset)));
    }
    assert_eq!(
        code_json(&flat),
        out["image_code"],
        "flat image code differs"
    );
    assert_eq!(Value::Array(entries), out["image_entry_points"]);
}
