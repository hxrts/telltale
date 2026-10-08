#![allow(missing_docs)]
#![allow(clippy::expect_used)]
#![cfg(not(target_arch = "wasm32"))]
//! Engine-level communication replay with a pluggable cryptographic hash model.

#[allow(dead_code, unreachable_pub)]
#[path = "support/mod.rs"]
mod test_support;

use telltale_machine::{
    CommunicationNullifierIdentity, CommunicationReplayMode, Hash, HashModel, HashTag,
    ProtocolMachine, ProtocolMachineConfig,
};

use test_support::{recursive_send_recv_image, simple_send_recv_image, PassthroughHandler};

fn blake3_hash(tag: HashTag, bytes: &[u8]) -> Hash {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[tag.domain_byte()]);
    hasher.update(bytes);
    Hash(*hasher.finalize().as_bytes())
}

const BLAKE3_MODEL: HashModel = HashModel::new("test.blake3.v1", blake3_hash);

fn config(identity: CommunicationNullifierIdentity, model: HashModel) -> ProtocolMachineConfig {
    ProtocolMachineConfig {
        communication_replay_mode: CommunicationReplayMode::Nullifier,
        communication_nullifier_identity: identity,
        communication_hash_model: model,
        ..ProtocolMachineConfig::default()
    }
}

fn run_simple(config: ProtocolMachineConfig) -> ProtocolMachine {
    let mut machine = ProtocolMachine::new(config);
    machine
        .load_choreography(&simple_send_recv_image("A", "B", "m"))
        .expect("load choreography");
    machine
        .run(&PassthroughHandler, 64)
        .expect("run simple session");
    machine
}

#[test]
fn crypto_hash_model_drives_nullifier_session_end_to_end() {
    let crypto = run_simple(config(
        CommunicationNullifierIdentity::ContentOnly,
        BLAKE3_MODEL,
    ));
    let default = run_simple(config(
        CommunicationNullifierIdentity::ContentOnly,
        HashModel::DEFAULT,
    ));

    let crypto_artifacts = crypto.communication_consumption_artifacts();
    let default_artifacts = default.communication_consumption_artifacts();
    assert_eq!(crypto_artifacts.len(), 1, "one receive consumed");
    assert_eq!(default_artifacts.len(), 1, "one receive consumed");
    let crypto_artifact = &crypto_artifacts[0];
    assert_eq!(crypto_artifact.mode, CommunicationReplayMode::Nullifier);
    assert_ne!(crypto_artifact.pre_root, crypto_artifact.post_root);

    // The payload digest and replay root come from the configured model.
    assert_ne!(
        crypto_artifact.identity.payload_digest,
        default_artifacts[0].identity.payload_digest
    );
    assert_ne!(
        crypto.communication_replay_root(),
        default.communication_replay_root()
    );

    // Same configuration is deterministic.
    let again = run_simple(config(
        CommunicationNullifierIdentity::ContentOnly,
        BLAKE3_MODEL,
    ));
    assert_eq!(
        again.communication_consumption_artifacts(),
        crypto_artifacts
    );
    assert_eq!(
        again.communication_replay_root(),
        crypto.communication_replay_root()
    );
}

#[test]
fn content_only_identity_rejects_resent_content_with_fresh_sequence() {
    // The recursive loop resends identical content (`Nat(42)`) on the same edge
    // and label with an incremented sequence number.
    let image = recursive_send_recv_image("A", "B", "m");

    let mut sequence_bound = ProtocolMachine::new(config(
        CommunicationNullifierIdentity::SequenceBound,
        BLAKE3_MODEL,
    ));
    sequence_bound.load_choreography(&image).expect("load");
    sequence_bound
        .run(&PassthroughHandler, 64)
        .expect("sequence-bound loop runs within the step budget");
    assert!(
        sequence_bound.communication_consumption_artifacts().len() > 2,
        "sequence-bound identity accepts repeated content with fresh sequence numbers"
    );

    let mut content_only = ProtocolMachine::new(config(
        CommunicationNullifierIdentity::ContentOnly,
        BLAKE3_MODEL,
    ));
    content_only.load_choreography(&image).expect("load");
    let outcome = content_only.run(&PassthroughHandler, 64);
    let consumed = content_only.communication_consumption_artifacts();
    assert_eq!(
        consumed.len(),
        2,
        "content-only identity admits each direction once, then rejects the resend: {outcome:?}"
    );
}

#[test]
fn custom_hash_model_is_not_silently_restored_from_serialized_config() {
    let encoded = serde_json::to_string(&config(
        CommunicationNullifierIdentity::ContentOnly,
        BLAKE3_MODEL,
    ))
    .expect("serialize config");
    let err = serde_json::from_str::<ProtocolMachineConfig>(&encoded)
        .expect_err("custom hash model must not deserialize");
    assert!(err.to_string().contains("test.blake3.v1"));

    let default_encoded =
        serde_json::to_string(&ProtocolMachineConfig::default()).expect("serialize default");
    let decoded: ProtocolMachineConfig =
        serde_json::from_str(&default_encoded).expect("default model roundtrips");
    assert_eq!(decoded.communication_hash_model, HashModel::DEFAULT);
    assert_eq!(
        decoded.communication_nullifier_identity,
        CommunicationNullifierIdentity::SequenceBound
    );
}
