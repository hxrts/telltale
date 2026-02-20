//! Flow-policy serialization compatibility tests.

use std::collections::BTreeSet;

use telltale_vm::vm::{FlowPolicy, FlowPredicate, VMConfig};

fn role_set(values: &[&str]) -> BTreeSet<String> {
    values.iter().map(|v| (*v).to_string()).collect()
}

#[test]
fn flow_policy_json_roundtrip_for_serializable_variants() {
    let cases = vec![
        FlowPolicy::AllowAll,
        FlowPolicy::DenyAll,
        FlowPolicy::AllowRoles(role_set(&["Observer", "Auditor"])),
        FlowPolicy::DenyRoles(role_set(&["Blocked"])),
        FlowPolicy::PredicateExpr(FlowPredicate::All(vec![
            FlowPredicate::TargetRolePrefix("Obs".to_string()),
            FlowPredicate::Any(vec![
                FlowPredicate::FactContains("secret".to_string()),
                FlowPredicate::EndpointRoleMatchesTarget,
            ]),
        ])),
    ];

    for policy in cases {
        let encoded = serde_json::to_string(&policy).expect("serialize flow policy to JSON");
        let decoded: FlowPolicy =
            serde_json::from_str(&encoded).expect("deserialize flow policy from JSON");
        assert_eq!(
            decoded, policy,
            "roundtrip mismatch for JSON payload: {encoded}"
        );
    }
}

#[test]
fn flow_policy_yaml_roundtrip_for_serializable_variants() {
    let cases = vec![
        FlowPolicy::AllowAll,
        FlowPolicy::DenyRoles(role_set(&["Observer"])),
        FlowPolicy::PredicateExpr(FlowPredicate::FactContains("classified".to_string())),
    ];

    for policy in cases {
        // serde_yaml cannot directly serialize nested externally-tagged enums.
        // Roundtrip through JSON Value preserves the canonical config shape.
        let json_value =
            serde_json::to_value(&policy).expect("serialize flow policy to JSON value");
        let encoded =
            serde_yaml::to_string(&json_value).expect("serialize flow policy value to YAML");
        let yaml_as_json: serde_json::Value =
            serde_yaml::from_str(&encoded).expect("deserialize YAML into JSON value");
        let decoded: FlowPolicy =
            serde_json::from_value(yaml_as_json).expect("deserialize flow policy from JSON value");
        assert_eq!(
            decoded, policy,
            "roundtrip mismatch for YAML payload: {encoded}"
        );
    }
}

#[test]
fn dynamic_flow_predicate_is_not_serializable() {
    let policy = FlowPolicy::predicate(|knowledge, target| {
        knowledge.fact.contains("secret") && target.starts_with("Obs")
    });

    let err = serde_json::to_string(&policy).expect_err("closure flow policy must not serialize");
    assert!(
        err.to_string()
            .contains("runtime closure predicate is not serializable"),
        "unexpected serde error: {err}"
    );
}

#[test]
fn vm_config_with_dynamic_flow_predicate_is_not_serializable() {
    let cfg = VMConfig {
        flow_policy: FlowPolicy::predicate(|knowledge, target| {
            knowledge.fact.contains("secret") && target.starts_with("Obs")
        }),
        ..VMConfig::default()
    };

    let err = serde_json::to_string(&cfg)
        .expect_err("config with closure flow policy must not serialize");
    assert!(
        err.to_string()
            .contains("runtime closure predicate is not serializable"),
        "unexpected serde error: {err}"
    );
}

#[test]
fn vm_config_schema_version_defaults_when_missing() {
    let mut encoded =
        serde_json::to_value(VMConfig::default()).expect("serialize default VM config");
    let obj = encoded
        .as_object_mut()
        .expect("VM config JSON value should be an object");
    obj.remove("config_schema_version");

    let decoded: VMConfig =
        serde_json::from_value(encoded).expect("deserialize VM config without schema version");
    assert_eq!(decoded.config_schema_version, 1);
}

#[test]
fn vm_config_optional_hooks_have_deterministic_defaults() {
    let mut encoded =
        serde_json::to_value(VMConfig::default()).expect("serialize default VM config");
    let obj = encoded
        .as_object_mut()
        .expect("VM config JSON value should be an object");
    obj.remove("monitor_mode");
    obj.remove("flow_policy");
    obj.remove("instruction_cost");
    obj.remove("initial_cost_budget");
    obj.remove("config_schema_version");

    let decoded: VMConfig =
        serde_json::from_value(encoded).expect("deserialize VM config without optional hooks");
    let defaults = VMConfig::default();
    assert_eq!(decoded.monitor_mode, defaults.monitor_mode);
    assert_eq!(decoded.flow_policy, defaults.flow_policy);
    assert_eq!(decoded.instruction_cost, defaults.instruction_cost);
    assert_eq!(decoded.initial_cost_budget, defaults.initial_cost_budget);
    assert_eq!(
        decoded.config_schema_version,
        defaults.config_schema_version
    );
}

#[test]
#[should_panic(expected = "max_sessions must be > 0")]
fn vm_new_rejects_invalid_config() {
    let cfg = VMConfig {
        max_sessions: 0,
        ..VMConfig::default()
    };
    drop(telltale_vm::vm::VM::new(cfg));
}

#[cfg(feature = "multi-thread")]
#[test]
#[should_panic(expected = "instruction_cost must be > 0")]
fn threaded_vm_rejects_invalid_config() {
    let cfg = VMConfig {
        instruction_cost: 0,
        ..VMConfig::default()
    };
    drop(telltale_vm::threaded::ThreadedVM::with_workers(cfg, 2));
}
