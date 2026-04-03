use serde::Deserialize;
use std::fs;
use telltale_runtime::heap::{
    nullifier_leaf_hash, resource_leaf_hash, DefaultHeapHasher, Direction, Heap, HeapCommitment,
    MerkleTree, Resource, ResourceId,
};

#[derive(Debug, Deserialize)]
struct HeapVectors {
    heap_encoding_version: u16,
    hasher: String,
    resource_fixture: ResourceFixture,
    heap_fixture: HeapFixture,
}

#[derive(Debug, Deserialize)]
struct ResourceFixture {
    kind: String,
    source: String,
    dest: String,
    label: String,
    payload_hex: String,
    seq_no: u64,
    allocation_counter: u64,
    canonical_bytes_hex: String,
    resource_id_digest_hex: String,
    resource_leaf_hex: String,
    nullifier_leaf_hex: String,
}

#[derive(Debug, Deserialize)]
struct HeapFixture {
    consumed_resource_id_hex: String,
    active_resource_id_hex: String,
    proof_leaf_hex: String,
    proof_root_hex: String,
    proof_path: Vec<ProofStepFixture>,
    resource_root_hex: String,
    nullifier_root_hex: String,
    commitment_hash_hex: String,
}

#[derive(Debug, Deserialize)]
struct ProofStepFixture {
    direction: String,
    sibling_hash_hex: String,
}

fn to_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{:02x}", byte)).collect()
}

fn load_vectors() -> HeapVectors {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/data/heap_vectors_v1.json"
    );
    let json = fs::read_to_string(path).expect("heap vector file should exist");
    serde_json::from_str(&json).expect("heap vector file should parse")
}

fn hex_to_bytes(hex: &str) -> Vec<u8> {
    assert_eq!(hex.len() % 2, 0, "hex input must have even length");
    hex.as_bytes()
        .chunks(2)
        .map(|pair| {
            let hi = (pair[0] as char).to_digit(16).expect("valid hex") as u8;
            let lo = (pair[1] as char).to_digit(16).expect("valid hex") as u8;
            (hi << 4) | lo
        })
        .collect()
}

#[test]
fn public_heap_vectors_match_reference_values() {
    let vectors = load_vectors();
    assert_eq!(vectors.heap_encoding_version, 1);
    assert_eq!(vectors.hasher, "blake3");
    assert_eq!(vectors.resource_fixture.kind, "message");

    let resource = Resource::message(
        &vectors.resource_fixture.source,
        &vectors.resource_fixture.dest,
        &vectors.resource_fixture.label,
        hex_to_bytes(&vectors.resource_fixture.payload_hex),
        vectors.resource_fixture.seq_no,
    );
    let resource_bytes = resource.canonical_bytes();
    let resource_id = ResourceId::<DefaultHeapHasher>::from_resource(
        &resource,
        vectors.resource_fixture.allocation_counter,
    );
    let resource_leaf = resource_leaf_hash::<DefaultHeapHasher>(&resource_id, &resource);
    let nullifier_leaf = nullifier_leaf_hash::<DefaultHeapHasher>(&resource_id);

    assert_eq!(
        to_hex(&resource_bytes),
        vectors.resource_fixture.canonical_bytes_hex
    );
    assert_eq!(
        to_hex(resource_id.as_bytes()),
        vectors.resource_fixture.resource_id_digest_hex
    );
    assert_eq!(
        to_hex(resource_leaf.as_ref()),
        vectors.resource_fixture.resource_leaf_hex
    );
    assert_eq!(
        to_hex(nullifier_leaf.as_ref()),
        vectors.resource_fixture.nullifier_leaf_hex
    );

    let heap = Heap::<DefaultHeapHasher>::new();
    let (rid0, heap) = heap.alloc_channel("Alice", "Bob");
    let (_rid1, heap) = heap.alloc_message("Alice", "Bob", "Hello", vec![1, 2, 3], 7);
    let (_rid2, heap) = heap.alloc_session("Alice", 12345);
    let heap = heap.consume(&rid0).unwrap();

    let tree = MerkleTree::<DefaultHeapHasher>::from_heap(&heap);
    let proof = tree.prove(0).expect("proof should exist");
    let commitment = HeapCommitment::<DefaultHeapHasher>::from_heap(&heap);

    assert_eq!(
        to_hex(rid0.as_bytes()),
        vectors.heap_fixture.consumed_resource_id_hex
    );
    assert_eq!(
        to_hex(proof.leaf_hash.as_ref()),
        vectors.heap_fixture.proof_leaf_hex
    );
    assert_eq!(
        to_hex(proof.root.as_ref()),
        vectors.heap_fixture.proof_root_hex
    );
    assert_eq!(proof.path.len(), vectors.heap_fixture.proof_path.len());
    assert_eq!(
        to_hex(resource_id.as_bytes()),
        vectors.heap_fixture.active_resource_id_hex
    );
    let expected_step = &vectors.heap_fixture.proof_path[0];
    assert_eq!(expected_step.direction, "Right");
    assert_eq!(proof.path[0].direction, Direction::Right);
    assert_eq!(
        to_hex(proof.path[0].sibling_hash.as_ref()),
        expected_step.sibling_hash_hex
    );
    assert_eq!(
        to_hex(commitment.resource_root.as_ref()),
        vectors.heap_fixture.resource_root_hex
    );
    assert_eq!(
        to_hex(commitment.nullifier_root.as_ref()),
        vectors.heap_fixture.nullifier_root_hex
    );
    assert_eq!(
        to_hex(commitment.hash().as_ref()),
        vectors.heap_fixture.commitment_hash_hex
    );
}
