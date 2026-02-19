use std::io::Write;
use std::process::{Command, Stdio};

fn sample_protocol() -> &'static str {
    r#"
proof_bundle Spec requires [speculation]
protocol Demo =
  roles A, B
  fork ghost0
  A -> B : Ping
"#
}

#[test]
fn test_choreo_fmt_explain_lowering_from_stdin() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_choreo-fmt"))
        .arg("--explain-lowering")
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn choreo-fmt");

    {
        let stdin = child.stdin.as_mut().expect("stdin available");
        stdin
            .write_all(sample_protocol().as_bytes())
            .expect("write stdin");
    }

    let output = child.wait_with_output().expect("wait output");
    assert!(
        output.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("Protocol:"));
    assert!(stdout.contains("Lowering:"));
}

#[test]
fn test_choreo_fmt_rejects_write_with_explain_lowering() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_choreo-fmt"))
        .arg("--write")
        .arg("--explain-lowering")
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn choreo-fmt");

    {
        let stdin = child.stdin.as_mut().expect("stdin available");
        stdin
            .write_all(sample_protocol().as_bytes())
            .expect("write stdin");
    }

    let output = child.wait_with_output().expect("wait output");
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("--write and --explain-lowering cannot be used together"));
}
