#![allow(clippy::expect_used)]

#[path = "test_choreographies/mod.rs"]
mod test_choreographies;

use std::collections::BTreeMap;
use std::sync::Arc;

use telltale_bridge::{
    export_protocol_bundle, DistributedClaims, InvariantClaims, ProtocolEnvelopeBridgeConfig,
    ProtocolMachineEnvelopeAdherenceConfig, ProtocolMachineEnvelopeAdmissionConfig,
    QuorumSystemKind,
};
use telltale_machine::output_condition::OutputConditionPolicy;
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::{
    ComposedRuntime, CompositionCertificate, CompositionError, DeterminismCapability, MemoryBudget,
    ProtocolBundle as MachineProtocolBundle, ProtocolMachineConfig, RuntimeContracts,
    SchedulerCapability, TheoremPackCapabilities,
};
use telltale_types::{GlobalType, Label, LocalTypeR};

fn simple_protocol() -> (GlobalType, BTreeMap<String, LocalTypeR>) {
    let global = GlobalType::send("A", "B", Label::new("Ping"), GlobalType::End);
    let mut locals = BTreeMap::new();
    locals.insert(
        "A".to_string(),
        LocalTypeR::send("B", Label::new("Ping"), LocalTypeR::End),
    );
    locals.insert(
        "B".to_string(),
        LocalTypeR::recv("A", Label::new("Ping"), LocalTypeR::End),
    );
    (global, locals)
}

fn simple_image() -> Arc<CodeImage> {
    let (global, locals) = simple_protocol();
    Arc::new(CodeImage::from_local_types(&locals, &global))
}

fn exported_bundle(claims: InvariantClaims) -> telltale_bridge::ProtocolBundle {
    let (global, locals) = simple_protocol();
    export_protocol_bundle(&global, &locals, claims)
}

fn eligibility_value(caps: &TheoremPackCapabilities, key: &str) -> bool {
    caps.execution_profile()
        .theorem_pack_eligibility
        .iter()
        .find_map(|(eligibility_key, enabled)| (eligibility_key == key).then_some(*enabled))
        .unwrap_or(false)
}

fn local_claim_consistency(claims: &InvariantClaims) -> Result<(), &'static str> {
    let distributed = &claims.distributed;

    if let Some(quorum) = &distributed.quorum_geometry {
        if quorum.quorum_size == 0
            || quorum.n == 0
            || quorum.quorum_size > quorum.n
            || quorum.intersection_size > quorum.quorum_size
        {
            return Err("quorum_geometry");
        }
        if matches!(quorum.quorum_system, QuorumSystemKind::Majority)
            && (quorum.intersection_size == 0 || quorum.quorum_size.saturating_mul(2) <= quorum.n)
        {
            return Err("quorum_geometry");
        }
    }

    if let Some(partial_synchrony) = &distributed.partial_synchrony {
        if matches!(
            partial_synchrony.timing,
            telltale_bridge::TimingModel::Asynchronous
        ) && partial_synchrony.delta_bound.is_none()
            && distributed.responsiveness.is_some()
        {
            return Err("partial_synchrony");
        }
    }

    let bridge_enabled = distributed
        .protocol_envelope_bridge
        .as_ref()
        .is_some_and(|config| config.enabled);
    let adherence_enabled = distributed
        .protocol_machine_envelope_adherence
        .as_ref()
        .is_some_and(|config| config.enabled);
    let admission_enabled = distributed
        .protocol_machine_envelope_admission
        .as_ref()
        .is_some_and(|config| config.enabled);
    if bridge_enabled && (!adherence_enabled || !admission_enabled) {
        return Err("protocol_envelope_bridge");
    }

    Ok(())
}

#[test]
fn protocol_bundle_export_and_runtime_admission_agree_on_protocol_machine_capabilities() {
    let theorem_pack = TheoremPackCapabilities::full();
    let claims = InvariantClaims {
        distributed: DistributedClaims {
            protocol_machine_envelope_adherence: Some(ProtocolMachineEnvelopeAdherenceConfig {
                enabled: eligibility_value(&theorem_pack, "protocol_machine_envelope_adherence"),
            }),
            protocol_machine_envelope_admission: Some(ProtocolMachineEnvelopeAdmissionConfig {
                enabled: eligibility_value(&theorem_pack, "protocol_machine_envelope_admission"),
            }),
            protocol_envelope_bridge: Some(ProtocolEnvelopeBridgeConfig {
                enabled: eligibility_value(&theorem_pack, "protocol_envelope_bridge"),
            }),
            ..DistributedClaims::default()
        },
        ..InvariantClaims::default()
    };

    local_claim_consistency(&claims).expect("full capability bundle should be consistent");
    let exported = exported_bundle(claims.clone());
    assert_eq!(
        exported
            .claims
            .distributed
            .protocol_machine_envelope_adherence
            .as_ref()
            .map(|config| config.enabled),
        Some(true)
    );
    assert_eq!(
        exported
            .claims
            .distributed
            .protocol_machine_envelope_admission
            .as_ref()
            .map(|config| config.enabled),
        Some(true)
    );
    assert_eq!(
        exported
            .claims
            .distributed
            .protocol_envelope_bridge
            .as_ref()
            .map(|config| config.enabled),
        Some(true)
    );

    let config = ProtocolMachineConfig {
        output_condition_policy: OutputConditionPolicy::PredicateAllowList(vec![
            "protocol_machine.observable_output".to_string(),
        ]),
        ..ProtocolMachineConfig::default()
    };
    let bundle = MachineProtocolBundle::new(
        simple_image(),
        CompositionCertificate {
            artifact_id: "cert/aligned".to_string(),
            link_ok_full: true,
            theorem_pack,
            runtime_contracts: Some(RuntimeContracts::full()),
        },
    );
    let mut runtime = ComposedRuntime::new(config, MemoryBudget::default());
    runtime
        .admit_bundle(bundle)
        .expect("aligned capability surfaces should admit");
}

#[test]
fn runtime_admission_rejects_bridge_claims_when_certificate_drops_bridge_capability() {
    let theorem_pack = TheoremPackCapabilities {
        determinism: vec![DeterminismCapability::Full],
        schedulers: vec![SchedulerCapability::Cooperative],
        output_condition_gating: false,
    };
    let claims = InvariantClaims {
        distributed: DistributedClaims {
            protocol_machine_envelope_adherence: Some(ProtocolMachineEnvelopeAdherenceConfig {
                enabled: true,
            }),
            protocol_machine_envelope_admission: Some(ProtocolMachineEnvelopeAdmissionConfig {
                enabled: true,
            }),
            protocol_envelope_bridge: Some(ProtocolEnvelopeBridgeConfig { enabled: true }),
            ..DistributedClaims::default()
        },
        ..InvariantClaims::default()
    };

    local_claim_consistency(&claims).expect("bridge claim fixture should be internally consistent");
    let exported = exported_bundle(claims);
    assert_eq!(
        exported
            .claims
            .distributed
            .protocol_envelope_bridge
            .as_ref()
            .map(|config| config.enabled),
        Some(true)
    );
    assert!(
        !eligibility_value(&theorem_pack, "protocol_envelope_bridge"),
        "theorem-pack capability drop should be visible in the execution profile"
    );

    let config = ProtocolMachineConfig {
        output_condition_policy: OutputConditionPolicy::PredicateAllowList(vec![
            "protocol_machine.observable_output".to_string(),
        ]),
        ..ProtocolMachineConfig::default()
    };
    let bundle = MachineProtocolBundle::new(
        simple_image(),
        CompositionCertificate {
            artifact_id: "cert/missing-bridge".to_string(),
            link_ok_full: true,
            theorem_pack,
            runtime_contracts: Some(RuntimeContracts::full()),
        },
    );
    let mut runtime = ComposedRuntime::new(config, MemoryBudget::default());
    let err = runtime
        .admit_bundle(bundle)
        .expect_err("missing bridge capability should reject output-condition admission");
    assert!(matches!(
        err,
        CompositionError::MissingCapability { ref capability, .. }
        if capability == "execution_profile"
    ));
}

#[test]
fn negative_protocol_bundle_fixtures_fail_local_claim_consistency_checks() {
    let bad_quorum = test_choreographies::bad_quorum();
    assert_eq!(
        local_claim_consistency(&bad_quorum.claims),
        Err("quorum_geometry")
    );

    let unbounded_wait = test_choreographies::unbounded_wait();
    assert_eq!(
        local_claim_consistency(&unbounded_wait.claims),
        Err("partial_synchrony")
    );

    let bridge_without_admission = test_choreographies::bridge_without_admission();
    assert_eq!(
        local_claim_consistency(&bridge_without_admission.claims),
        Err("protocol_envelope_bridge")
    );
}
