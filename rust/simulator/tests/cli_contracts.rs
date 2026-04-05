//! CLI contract tests for simulator run and replay binaries.

use std::collections::BTreeMap;
use std::process::Command;

use telltale_machine::model::durability::{
    AgreementWalArtifact, AgreementWalEntry, EvidenceOutcomeCacheArtifact,
    PersistedDurabilityArtifact,
};
use telltale_simulator::contracts::ContractCheckConfig;
use telltale_simulator::harness::{HarnessConfig, HarnessSpec};
use telltale_simulator::scenario::{DurabilityMode, ExecutionRegime, Scenario};
use telltale_types::{GlobalType, Label, LocalTypeR};
use tempfile::tempdir;

fn finite_protocol() -> (GlobalType, BTreeMap<String, LocalTypeR>) {
    let global = GlobalType::send(
        "A",
        "B",
        Label::new("msg"),
        GlobalType::send("B", "A", Label::new("ack"), GlobalType::End),
    );

    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::Send {
            partner: "B".into(),
            branches: vec![(
                Label::new("msg"),
                None,
                LocalTypeR::Recv {
                    partner: "B".into(),
                    branches: vec![(Label::new("ack"), None, LocalTypeR::End)],
                },
            )],
        },
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::Recv {
            partner: "A".into(),
            branches: vec![(
                Label::new("msg"),
                None,
                LocalTypeR::Send {
                    partner: "A".into(),
                    branches: vec![(Label::new("ack"), None, LocalTypeR::End)],
                },
            )],
        },
    );

    (global, local_types)
}

fn cli_scenario(name: &str) -> Scenario {
    let toml = format!(
        r#"
name = "{name}"
roles = ["A", "B"]
steps = 6
seed = 11
checkpoint_interval = 2

[execution]
backend = "canonical"
scheduler_concurrency = 1
worker_threads = 1

[network]
base_latency_ms = 1
latency_variance = "0.0"
loss_probability = "0.0"

[field]
layer = "mean_field"

[field.params]
beta = "1.0"
species = ["up", "down"]
initial_state = ["0.5", "0.5"]
step_size = "0.01"
"#
    );
    Scenario::parse(&toml).expect("parse cli scenario")
}

fn durable_cli_scenario(name: &str) -> Scenario {
    let mut scenario = cli_scenario(name);
    scenario.durability.mode = DurabilityMode::Wal;
    scenario
}

#[test]
fn run_and_replay_binaries_emit_expected_json_contracts() {
    let tmp = tempdir().expect("tempdir");
    let (global_type, local_types) = finite_protocol();
    let scenario = cli_scenario("cli_contracts");
    let config = HarnessConfig {
        spec: HarnessSpec::new(local_types, global_type, scenario.clone()),
        contracts: ContractCheckConfig::default(),
    };

    let config_path = tmp.path().join("config.json");
    std::fs::write(
        &config_path,
        serde_json::to_vec_pretty(&config).expect("serialize config"),
    )
    .expect("write config");
    let scenario_path = tmp.path().join("scenario.toml");
    std::fs::write(
        &scenario_path,
        toml::to_string(&scenario).expect("serialize scenario"),
    )
    .expect("write scenario");

    let run_output_path = tmp.path().join("run.json");
    let run = Command::new(env!("CARGO_BIN_EXE_run"))
        .current_dir(tmp.path())
        .args([
            "--config",
            config_path.to_str().expect("config path utf8"),
            "--output",
            run_output_path.to_str().expect("run output path utf8"),
            "--pretty",
        ])
        .output()
        .expect("run simulator binary");
    assert!(
        run.status.success(),
        "run binary failed: stdout={}\nstderr={}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );

    let run_json: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&run_output_path).expect("read run output"))
            .expect("parse run output");
    assert_eq!(
        run_json["stats"]["execution_regime"],
        serde_json::json!(ExecutionRegime::CanonicalExact)
    );
    assert!(run_json["stats"]["theorem_profile"].is_object());
    assert!(run_json["replay"]["environment_trace"].is_object());
    assert!(run_json["analysis"]["normalized_observability"].is_object());

    let checkpoint_path = tmp
        .path()
        .join("artifacts")
        .join("cli_contracts")
        .join("checkpoint_2.cbor");
    assert!(
        checkpoint_path.exists(),
        "expected checkpoint file at {}",
        checkpoint_path.display()
    );

    let replay_output_path = tmp.path().join("replay.json");
    let replay = Command::new(env!("CARGO_BIN_EXE_replay"))
        .current_dir(tmp.path())
        .args([
            "--checkpoint",
            checkpoint_path.to_str().expect("checkpoint path utf8"),
            "--scenario",
            scenario_path.to_str().expect("scenario path utf8"),
            "--json",
            "--output",
            replay_output_path
                .to_str()
                .expect("replay output path utf8"),
        ])
        .output()
        .expect("run replay binary");
    assert!(
        replay.status.success(),
        "replay binary failed: stdout={}\nstderr={}",
        String::from_utf8_lossy(&replay.stdout),
        String::from_utf8_lossy(&replay.stderr)
    );

    let replay_json: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&replay_output_path).expect("read replay output"))
            .expect("parse replay output");
    assert_eq!(
        replay_json["stats"]["execution_regime"],
        serde_json::json!(ExecutionRegime::CanonicalExact)
    );
    assert!(replay_json["stats"]["theorem_profile"].is_object());
    assert_eq!(
        replay_json["replay"]["checkpoint_tick"],
        serde_json::json!(2)
    );
    assert!(replay_json["analysis"]["normalized_observability"].is_object());
}

#[test]
fn replay_binary_fails_closed_on_invalid_checkpoint_artifact() {
    let tmp = tempdir().expect("tempdir");
    let scenario = cli_scenario("cli_bad_checkpoint");
    let scenario_path = tmp.path().join("scenario.toml");
    std::fs::write(
        &scenario_path,
        toml::to_string(&scenario).expect("serialize scenario"),
    )
    .expect("write scenario");
    let checkpoint_path = tmp.path().join("bad_checkpoint.cbor");
    std::fs::write(&checkpoint_path, b"not a persisted replay artifact").expect("write checkpoint");

    let replay = Command::new(env!("CARGO_BIN_EXE_replay"))
        .current_dir(tmp.path())
        .args([
            "--checkpoint",
            checkpoint_path.to_str().expect("checkpoint path utf8"),
            "--scenario",
            scenario_path.to_str().expect("scenario path utf8"),
            "--json",
        ])
        .output()
        .expect("run replay binary");

    assert!(!replay.status.success(), "invalid checkpoint should fail");
    assert!(
        String::from_utf8_lossy(&replay.stderr).contains("decode persisted replay artifact"),
        "stderr should expose the typed persisted replay decode failure"
    );
}

#[test]
fn durable_binary_projects_wal_cache_and_recovery_summary() {
    let tmp = tempdir().expect("tempdir");
    let (global_type, local_types) = finite_protocol();
    let scenario = durable_cli_scenario("cli_durable");
    let config = HarnessConfig {
        spec: HarnessSpec::new(local_types, global_type, scenario.clone()),
        contracts: ContractCheckConfig::default(),
    };

    let config_path = tmp.path().join("config.json");
    std::fs::write(
        &config_path,
        serde_json::to_vec_pretty(&config).expect("serialize config"),
    )
    .expect("write config");
    let scenario_path = tmp.path().join("scenario.toml");
    std::fs::write(
        &scenario_path,
        toml::to_string(&scenario).expect("serialize scenario"),
    )
    .expect("write scenario");

    let run = Command::new(env!("CARGO_BIN_EXE_run"))
        .current_dir(tmp.path())
        .args(["--config", config_path.to_str().expect("config path utf8")])
        .output()
        .expect("run simulator binary");
    assert!(
        run.status.success(),
        "run binary failed: stdout={}\nstderr={}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );

    let checkpoint_path = tmp
        .path()
        .join("artifacts")
        .join("cli_durable")
        .join("checkpoint_2.cbor");
    assert!(checkpoint_path.exists(), "checkpoint should exist");

    let wal_path = tmp.path().join("wal.cbor");
    PersistedDurabilityArtifact::agreement_wal(AgreementWalArtifact {
        entries: vec![AgreementWalEntry::Escalation {
            operation_id: "cli:durable".to_string(),
            previous_level: telltale_machine::AgreementLevel::Provisional,
            new_level: telltale_machine::AgreementLevel::SoftSafe,
            evidence_id: Some("cli#1".to_string()),
            tick: 3,
        }],
    })
    .write_to_path(&wal_path)
    .expect("write wal artifact");
    let cache_path = tmp.path().join("cache.cbor");
    PersistedDurabilityArtifact::evidence_outcome_cache(EvidenceOutcomeCacheArtifact::default())
        .write_to_path(&cache_path)
        .expect("write cache artifact");

    let durable_output_path = tmp.path().join("durable.json");
    let durable = Command::new(env!("CARGO_BIN_EXE_durable"))
        .current_dir(tmp.path())
        .args([
            "--wal",
            wal_path.to_str().expect("wal path utf8"),
            "--cache",
            cache_path.to_str().expect("cache path utf8"),
            "--checkpoint",
            checkpoint_path.to_str().expect("checkpoint path utf8"),
            "--scenario",
            scenario_path.to_str().expect("scenario path utf8"),
            "--json",
            "--output",
            durable_output_path
                .to_str()
                .expect("durable output path utf8"),
        ])
        .output()
        .expect("run durable binary");
    assert!(
        durable.status.success(),
        "durable binary failed: stdout={}\nstderr={}",
        String::from_utf8_lossy(&durable.stdout),
        String::from_utf8_lossy(&durable.stderr)
    );

    let durable_json: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&durable_output_path).expect("read durable output"))
            .expect("parse durable output");
    assert_eq!(
        durable_json["wal_entries"][0]["operation_id"],
        "cli:durable"
    );
    assert!(durable_json["evidence_cache_entries"].is_array());
    assert!(durable_json["recovery"].is_object());
}
