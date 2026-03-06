#![allow(missing_docs)]

use criterion::{black_box, BatchSize, Criterion};
use telltale_vm::coroutine::Value;
use telltale_vm::instr::Endpoint;
use telltale_vm::verification::{
    signing_key_for_endpoint, verifying_key_for_endpoint, AuthTree, DefaultVerificationModel,
    HashTag, VerificationModel,
};

use crate::common::{
    choreography_load_allocation_count, session_open_allocation_count, signing_fixture,
};

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
