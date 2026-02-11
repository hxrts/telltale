#![cfg(not(target_arch = "wasm32"))]
#![allow(missing_docs)]

use telltale_vm::coroutine::Value;
use telltale_vm::instr::Endpoint;
use telltale_vm::verification::{
    sign_value, signing_key_for_endpoint, verify_signed_value, AuthProof, AuthTree,
    DefaultVerificationModel, Hash, HashTag, VerificationModel,
};
use telltale_vm::vm::ResourceState;

fn hash_payload(tag: HashTag, bytes: &[u8]) -> Hash {
    DefaultVerificationModel::hash(tag, bytes)
}

#[test]
fn hash_tags_are_domain_separated() {
    let payload = b"same-payload";
    let hashes = [
        hash_payload(HashTag::Value, payload),
        hash_payload(HashTag::SignedValue, payload),
        hash_payload(HashTag::MerkleLeaf, payload),
        hash_payload(HashTag::MerkleNode, payload),
        hash_payload(HashTag::Commitment, payload),
        hash_payload(HashTag::Nullifier, payload),
        hash_payload(HashTag::SigningKey, payload),
    ];

    for i in 0..hashes.len() {
        for j in i + 1..hashes.len() {
            assert_ne!(hashes[i], hashes[j], "hash tags must be domain-separated");
        }
    }
}

#[test]
fn signing_commitment_and_nullifier_vectors_are_deterministic() {
    let endpoint = Endpoint {
        sid: 7,
        role: "Alice".to_string(),
    };
    let payload = Value::Nat(42);
    let signing = signing_key_for_endpoint(&endpoint);

    let sig1 = sign_value(&payload, &signing);
    let sig2 = sign_value(&payload, &signing);
    assert_eq!(sig1, sig2, "signature vectors must be deterministic");

    let verifying = DefaultVerificationModel::deriving(&signing);
    assert!(verify_signed_value(&payload, &sig1, &verifying));

    let commitment = DefaultVerificationModel::commitment(&payload);
    let nullifier = DefaultVerificationModel::nullifier(&payload);
    assert_ne!(
        commitment.0, nullifier.0,
        "commitment/nullifier domains must differ"
    );
}

#[test]
fn auth_tree_rejects_malformed_proofs() {
    let leaves = vec![
        hash_payload(HashTag::MerkleLeaf, b"a"),
        hash_payload(HashTag::MerkleLeaf, b"b"),
        hash_payload(HashTag::MerkleLeaf, b"c"),
    ];
    let tree = AuthTree::new(leaves.clone());
    let proof = tree.prove(1).expect("proof for valid leaf index");
    assert!(AuthTree::verify(tree.root(), leaves[1], &proof));

    let mut wrong_index = proof.clone();
    wrong_index.index = 0;
    assert!(!AuthTree::verify(tree.root(), leaves[1], &wrong_index));

    let mut wrong_orientation = proof.clone();
    if let Some(first) = wrong_orientation.sibling_on_left.first_mut() {
        *first = !*first;
    }
    assert!(!AuthTree::verify(
        tree.root(),
        leaves[1],
        &wrong_orientation
    ));

    let mut wrong_hash = proof;
    if let Some(first) = wrong_hash.siblings.first_mut() {
        first.0[0] ^= 0x01;
    }
    assert!(!AuthTree::verify(tree.root(), leaves[1], &wrong_hash));
}

#[test]
fn nullifier_lifecycle_blocks_replay_consumption() {
    let mut resources = ResourceState::default();
    let payload = Value::Str("token".to_string());

    let _first = resources.consume(&payload).expect("first consume succeeds");
    let second = resources.consume(&payload);
    assert!(
        second.is_err(),
        "second consume should be rejected as replay"
    );
}

#[test]
fn malformed_auth_proof_vector_roundtrips() {
    let proof = AuthProof {
        index: 3,
        siblings: vec![Hash([0_u8; 32]); 2],
        sibling_on_left: vec![true],
    };
    assert!(!AuthTree::verify(
        Hash([0_u8; 32]),
        Hash([0_u8; 32]),
        &proof
    ));
}
