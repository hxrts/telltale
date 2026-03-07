#![allow(missing_docs)]

use criterion::{black_box, BatchSize, Criterion};
use serde::Serialize;
use telltale_vm::communication_replay::{
    CommunicationConsumeResult, CommunicationConsumption, CommunicationIdentity,
    CommunicationReplayMode, CommunicationReplayState, CommunicationStepKind,
    DefaultCommunicationConsumption,
};
use telltale_vm::coroutine::Value;
use telltale_vm::instr::Endpoint;
use telltale_vm::session::Edge;
use telltale_vm::verification::{
    signing_key_for_endpoint, verifying_key_for_endpoint, AuthTree, DefaultVerificationModel, Hash,
    HashTag, Nullifier, VerificationModel,
};

use crate::common::{
    choreography_load_allocation_count, session_open_allocation_count, signing_fixture,
};

fn legacy_json_encode<T: Serialize>(value: &T) -> Vec<u8> {
    serde_json::to_vec(value).unwrap_or_default()
}

fn legacy_identity_build(
    edge: &Edge,
    step_kind: CommunicationStepKind,
    label: &str,
    payload: &Value,
    sequence_no: u64,
) -> CommunicationIdentity {
    let payload_bytes = legacy_json_encode(payload);
    CommunicationIdentity {
        domain_tag: telltale_vm::COMM_IDENTITY_DOMAIN_TAG.to_string(),
        sid: edge.sid,
        sender: edge.sender.clone(),
        receiver: edge.receiver.clone(),
        step_kind,
        label: label.to_string(),
        payload_digest: DefaultVerificationModel::hash(HashTag::Value, &payload_bytes),
        sequence_no,
    }
}

fn legacy_replay_root(state: &CommunicationReplayState) -> Hash {
    DefaultVerificationModel::hash(HashTag::Nullifier, &legacy_json_encode(state))
}

fn legacy_nullifier_consume(
    identity: &CommunicationIdentity,
    state: &mut CommunicationReplayState,
) -> Result<CommunicationConsumeResult, ()> {
    let pre_root = legacy_replay_root(state);
    let nullifier = Nullifier(DefaultVerificationModel::hash(
        HashTag::Nullifier,
        &legacy_json_encode(identity),
    ));
    if state.consumed_nullifiers.contains(&nullifier) {
        return Err(());
    }
    state.consumed_nullifiers.insert(nullifier);
    let post_root = legacy_replay_root(state);
    Ok(CommunicationConsumeResult {
        mode: CommunicationReplayMode::Nullifier,
        pre_root,
        post_root,
        consumed_nullifier: Some(nullifier),
    })
}

#[allow(clippy::too_many_lines)]
pub(crate) fn bench_verification_and_allocations(c: &mut Criterion) {
    eprintln!(
        "vm benchmark snapshot session_open_allocations: {}",
        session_open_allocation_count(64)
    );
    eprintln!(
        "vm benchmark snapshot choreography_load_allocations: {}",
        choreography_load_allocation_count(64, 8)
    );

    c.bench_function("vm_sign_value_only", |b| {
        let endpoint = Endpoint {
            sid: 7,
            role: "A".to_string(),
        };
        let payload = Value::Prod(Box::new(Value::Nat(7)), Box::new(Value::Bool(true)));
        let key = signing_key_for_endpoint(&endpoint);
        b.iter(|| black_box(telltale_vm::signValue(black_box(&payload), black_box(&key))));
    });

    c.bench_function("vm_verify_signed_value_only", |b| {
        let endpoint = Endpoint {
            sid: 7,
            role: "A".to_string(),
        };
        let (payload, signature) = signing_fixture();
        let verifying = verifying_key_for_endpoint(&endpoint);
        b.iter(|| {
            black_box(telltale_vm::verifySignedValue(
                black_box(&payload),
                black_box(&signature),
                black_box(&verifying),
            ))
        });
    });

    c.bench_function("vm_auth_tree_append_only", |b| {
        let (payload, signature) = signing_fixture();
        let signed = telltale_vm::buffer::SignedValue {
            payload,
            signature,
            sequence_no: 1,
        };
        let bytes = bincode::serialize(&signed).expect("serialize signed payload");
        let leaf = DefaultVerificationModel::hash(HashTag::MerkleLeaf, &bytes);
        b.iter_batched(
            || {
                let mut tree = AuthTree::new(vec![leaf]);
                tree.append_leaf(leaf);
                tree
            },
            |mut tree| {
                tree.append_leaf(black_box(leaf));
                black_box(tree.root())
            },
            BatchSize::SmallInput,
        );
    });

    c.bench_function("vm_replay_identity_build_binary", |b| {
        let edge = Edge::new(7, "A", "B");
        let payload = Value::Prod(Box::new(Value::Nat(7)), Box::new(Value::Bool(true)));
        b.iter(|| {
            black_box(CommunicationIdentity::from_payload(
                black_box(&edge),
                CommunicationStepKind::Receive,
                black_box("msg"),
                black_box(&payload),
                black_box(3),
            ))
        });
    });

    c.bench_function("vm_replay_identity_build_json_legacy", |b| {
        let edge = Edge::new(7, "A", "B");
        let payload = Value::Prod(Box::new(Value::Nat(7)), Box::new(Value::Bool(true)));
        b.iter(|| {
            black_box(legacy_identity_build(
                black_box(&edge),
                CommunicationStepKind::Receive,
                black_box("msg"),
                black_box(&payload),
                black_box(3),
            ))
        });
    });

    c.bench_function("vm_replay_nullifier_consume_binary", |b| {
        let identity = CommunicationIdentity::from_payload(
            &Edge::new(7, "A", "B"),
            CommunicationStepKind::Receive,
            "msg",
            &Value::Nat(7),
            0,
        );
        b.iter_batched(
            || DefaultCommunicationConsumption::new(CommunicationReplayMode::Nullifier),
            |mut model| {
                black_box(
                    model
                        .consume_receive(black_box(&identity))
                        .expect("consume replay identity"),
                )
            },
            BatchSize::SmallInput,
        );
    });

    c.bench_function("vm_replay_nullifier_consume_json_legacy", |b| {
        let identity = legacy_identity_build(
            &Edge::new(7, "A", "B"),
            CommunicationStepKind::Receive,
            "msg",
            &Value::Nat(7),
            0,
        );
        b.iter_batched(
            CommunicationReplayState::default,
            |mut state| {
                black_box(
                    legacy_nullifier_consume(black_box(&identity), &mut state)
                        .expect("legacy consume replay identity"),
                )
            },
            BatchSize::SmallInput,
        );
    });

    c.bench_function("vm_session_open_allocation_count", |b| {
        b.iter(|| black_box(session_open_allocation_count(black_box(64))));
    });

    c.bench_function("vm_choreography_load_allocation_count", |b| {
        b.iter(|| {
            black_box(choreography_load_allocation_count(
                black_box(64),
                black_box(8),
            ))
        });
    });
}
