#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use serde::Deserialize;
use std::fs;
use std::path::{Path, PathBuf};
use telltale_bridge::HeapParityRunner;
use telltale_runtime::heap::{
    heap_commitment_preimage, merkle_node_preimage, nullifier_leaf_hash, nullifier_leaf_preimage,
    resource_id_preimage, resource_leaf_hash, resource_leaf_preimage, DefaultHeapHasher, Direction,
    Heap, HeapCommitment, MerkleTree, Resource, ResourceId,
};

const STRICT_ENV: &str = "TELLTALE_REQUIRE_LEAN_HEAP_PARITY";

#[derive(Debug, Deserialize)]
struct HeapParityFixture {
    schema_version: String,
    hasher: String,
    resource_fixture: ResourceFixture,
    session_fixture: SessionFixture,
    channel_fixture: ChannelFixture,
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
    resource_id_preimage_hex: String,
    resource_leaf_hex: String,
    resource_leaf_preimage_hex: String,
    nullifier_leaf_hex: String,
    nullifier_leaf_preimage_hex: String,
}

#[derive(Debug, Deserialize)]
struct SessionFixture {
    role: String,
    type_hash: u64,
    allocation_counter: u64,
    canonical_bytes_hex: String,
    resource_id_digest_hex: String,
    resource_id_preimage_hex: String,
    resource_leaf_hex: String,
    resource_leaf_preimage_hex: String,
}

#[derive(Debug, Deserialize)]
struct ChannelFixture {
    sender: String,
    receiver: String,
    allocation_counter: u64,
    canonical_bytes_hex: String,
    resource_id_digest_hex: String,
    resource_id_preimage_hex: String,
    nullifier_leaf_hex: String,
    nullifier_leaf_preimage_hex: String,
}

#[derive(Debug, Deserialize)]
struct HeapFixture {
    active_resource_ids_hex: Vec<String>,
    consumed_resource_ids_hex: Vec<String>,
    proof_index: usize,
    proof_leaf_hex: String,
    proof_root_hex: String,
    proof_path: Vec<ProofStepFixture>,
    resource_root_hex: String,
    nullifier_root_hex: String,
    merkle_node_preimage_hex: String,
    commitment_hash_hex: String,
    commitment_preimage_hex: String,
}

#[derive(Debug, Deserialize)]
struct ProofStepFixture {
    direction: String,
    sibling_hash_hex: String,
}

fn strict_heap_parity_required() -> bool {
    std::env::var(STRICT_ENV)
        .map(|value| value != "0")
        .unwrap_or(false)
}

fn skip_without_heap_lean_runner() -> bool {
    if HeapParityRunner::is_available() {
        return false;
    }
    assert!(
        !strict_heap_parity_required(),
        "strict heap parity is enabled but heap_parity_runner is unavailable"
    );
    eprintln!(
        "SKIPPED: Lean heap parity runner not available. Run `cd lean && lake build heap_parity_runner` to enable."
    );
    true
}

fn fixture_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../runtime/tests/data/heap_lean_parity_v1.json")
}

fn load_fixture() -> HeapParityFixture {
    let json = fs::read_to_string(fixture_path()).expect("heap parity fixture should exist");
    serde_json::from_str(&json).expect("heap parity fixture should parse")
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

fn to_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{:02x}", byte)).collect()
}

#[test]
fn lean_heap_parity_matches_runtime_contract() {
    if skip_without_heap_lean_runner() {
        return;
    }

    let fixture = load_fixture();
    assert_eq!(fixture.schema_version, "heap_parity.v1");
    assert_eq!(fixture.hasher, "blake3");
    assert_eq!(fixture.resource_fixture.kind, "message");

    let runner = HeapParityRunner::new().expect("heap parity runner should exist");
    let lean = runner
        .run_fixture(fixture_path())
        .expect("Lean heap parity runner should succeed");

    let message = Resource::message(
        &fixture.resource_fixture.source,
        &fixture.resource_fixture.dest,
        &fixture.resource_fixture.label,
        hex_to_bytes(&fixture.resource_fixture.payload_hex),
        fixture.resource_fixture.seq_no,
    );
    let message_bytes = message.canonical_bytes();
    let message_id = ResourceId::<DefaultHeapHasher>::from_resource(
        &message,
        fixture.resource_fixture.allocation_counter,
    );
    let message_id_preimage = resource_id_preimage(&message_bytes, fixture.resource_fixture.allocation_counter);
    let message_leaf = resource_leaf_hash::<DefaultHeapHasher>(&message_id, &message);
    let message_leaf_preimage = resource_leaf_preimage(message_id.as_bytes(), &message_bytes);

    let session = Resource::session(
        &fixture.session_fixture.role,
        fixture.session_fixture.type_hash,
    );
    let session_bytes = session.canonical_bytes();
    let session_id = ResourceId::<DefaultHeapHasher>::from_resource(
        &session,
        fixture.session_fixture.allocation_counter,
    );
    let session_id_preimage = resource_id_preimage(&session_bytes, fixture.session_fixture.allocation_counter);
    let session_leaf = resource_leaf_hash::<DefaultHeapHasher>(&session_id, &session);
    let session_leaf_preimage = resource_leaf_preimage(session_id.as_bytes(), &session_bytes);

    let channel = Resource::channel(
        &fixture.channel_fixture.sender,
        &fixture.channel_fixture.receiver,
    );
    let channel_bytes = channel.canonical_bytes();
    let channel_id = ResourceId::<DefaultHeapHasher>::from_resource(
        &channel,
        fixture.channel_fixture.allocation_counter,
    );
    let channel_id_preimage = resource_id_preimage(&channel_bytes, fixture.channel_fixture.allocation_counter);
    let channel_nullifier_leaf = nullifier_leaf_hash::<DefaultHeapHasher>(&channel_id);
    let channel_nullifier_preimage = nullifier_leaf_preimage(channel_id.as_bytes());

    assert_eq!(to_hex(&message_bytes), fixture.resource_fixture.canonical_bytes_hex);
    assert_eq!(to_hex(message_id.as_bytes()), fixture.resource_fixture.resource_id_digest_hex);
    assert_eq!(to_hex(&message_id_preimage), fixture.resource_fixture.resource_id_preimage_hex);
    assert_eq!(to_hex(message_leaf.as_ref()), fixture.resource_fixture.resource_leaf_hex);
    assert_eq!(
        to_hex(&message_leaf_preimage),
        fixture.resource_fixture.resource_leaf_preimage_hex
    );

    assert_eq!(to_hex(&session_bytes), fixture.session_fixture.canonical_bytes_hex);
    assert_eq!(to_hex(session_id.as_bytes()), fixture.session_fixture.resource_id_digest_hex);
    assert_eq!(to_hex(&session_id_preimage), fixture.session_fixture.resource_id_preimage_hex);
    assert_eq!(to_hex(session_leaf.as_ref()), fixture.session_fixture.resource_leaf_hex);
    assert_eq!(
        to_hex(&session_leaf_preimage),
        fixture.session_fixture.resource_leaf_preimage_hex
    );

    assert_eq!(to_hex(&channel_bytes), fixture.channel_fixture.canonical_bytes_hex);
    assert_eq!(to_hex(channel_id.as_bytes()), fixture.channel_fixture.resource_id_digest_hex);
    assert_eq!(to_hex(&channel_id_preimage), fixture.channel_fixture.resource_id_preimage_hex);
    assert_eq!(
        to_hex(channel_nullifier_leaf.as_ref()),
        fixture.channel_fixture.nullifier_leaf_hex
    );
    assert_eq!(
        to_hex(&channel_nullifier_preimage),
        fixture.channel_fixture.nullifier_leaf_preimage_hex
    );
    assert_eq!(
        fixture.resource_fixture.nullifier_leaf_hex,
        fixture.channel_fixture.nullifier_leaf_hex
    );
    assert_eq!(
        fixture.resource_fixture.nullifier_leaf_preimage_hex,
        fixture.channel_fixture.nullifier_leaf_preimage_hex
    );

    let heap = Heap::<DefaultHeapHasher>::new();
    let (rid0, heap) = heap.alloc_channel("Alice", "Bob");
    let (_rid1, heap) = heap.alloc_message("Alice", "Bob", "Hello", vec![1, 2, 3], 7);
    let (_rid2, heap) = heap.alloc_session("Alice", 12345);
    let heap = heap.consume(&rid0).expect("channel should be consumable");
    let tree = MerkleTree::<DefaultHeapHasher>::from_heap(&heap);
    let proof = tree
        .prove(fixture.heap_fixture.proof_index)
        .expect("proof should exist");
    let commitment = HeapCommitment::<DefaultHeapHasher>::from_heap(&heap);
    let merkle_preimage = merkle_node_preimage(message_leaf.as_ref(), session_leaf.as_ref());
    let commitment_preimage = heap_commitment_preimage(
        commitment.resource_root.as_ref(),
        commitment.nullifier_root.as_ref(),
        commitment.counter,
    );

    let active_ids: Vec<String> = heap
        .active_resources()
        .map(|(rid, _)| to_hex(rid.as_bytes()))
        .collect();
    let consumed_ids: Vec<String> = heap
        .consumed_ids()
        .map(|rid| to_hex(rid.as_bytes()))
        .collect();

    assert_eq!(active_ids, fixture.heap_fixture.active_resource_ids_hex);
    assert_eq!(consumed_ids, fixture.heap_fixture.consumed_resource_ids_hex);
    assert_eq!(to_hex(proof.leaf_hash.as_ref()), fixture.heap_fixture.proof_leaf_hex);
    assert_eq!(to_hex(proof.root.as_ref()), fixture.heap_fixture.proof_root_hex);
    assert_eq!(
        to_hex(commitment.resource_root.as_ref()),
        fixture.heap_fixture.resource_root_hex
    );
    assert_eq!(
        to_hex(commitment.nullifier_root.as_ref()),
        fixture.heap_fixture.nullifier_root_hex
    );
    assert_eq!(
        to_hex(commitment.hash().as_ref()),
        fixture.heap_fixture.commitment_hash_hex
    );
    assert_eq!(
        to_hex(&merkle_preimage),
        fixture.heap_fixture.merkle_node_preimage_hex
    );
    assert_eq!(
        to_hex(&commitment_preimage),
        fixture.heap_fixture.commitment_preimage_hex
    );
    assert_eq!(proof.path.len(), fixture.heap_fixture.proof_path.len());
    assert_eq!(proof.path[0].direction, Direction::Right);
    assert_eq!(fixture.heap_fixture.proof_path[0].direction, "Right");
    assert_eq!(
        to_hex(proof.path[0].sibling_hash.as_ref()),
        fixture.heap_fixture.proof_path[0].sibling_hash_hex
    );

    assert_eq!(lean.schema_version, "lean_heap_parity.v1");
    assert_eq!(lean.heap_encoding_version, 1);
    assert_eq!(lean.hasher, "blake3");
    assert_eq!(
        lean.resource_fixture.canonical_bytes_hex,
        fixture.resource_fixture.canonical_bytes_hex
    );
    assert_eq!(
        lean.resource_fixture.canonical_bytes_hex,
        to_hex(&message_bytes)
    );
    assert_eq!(
        lean.resource_fixture.resource_id_preimage_hex,
        fixture.resource_fixture.resource_id_preimage_hex
    );
    assert_eq!(
        lean.resource_fixture.resource_leaf_preimage_hex,
        fixture.resource_fixture.resource_leaf_preimage_hex
    );
    assert_eq!(
        lean.resource_fixture.nullifier_leaf_preimage_hex,
        fixture.channel_fixture.nullifier_leaf_preimage_hex
    );
    assert_eq!(
        lean.resource_fixture.resource_id_digest_hex,
        fixture.resource_fixture.resource_id_digest_hex
    );

    assert_eq!(
        lean.heap_fixture.active_resource_ids_hex,
        fixture.heap_fixture.active_resource_ids_hex
    );
    assert_eq!(
        lean.heap_fixture.consumed_resource_ids_hex,
        fixture.heap_fixture.consumed_resource_ids_hex
    );
    assert_eq!(lean.heap_fixture.proof_index as usize, fixture.heap_fixture.proof_index);
    let lean_resource_proof = lean
        .heap_fixture
        .resource_proof
        .expect("Lean should return a resource proof");
    assert_eq!(lean_resource_proof.leaf_hash_hex, fixture.heap_fixture.proof_leaf_hex);
    assert_eq!(lean_resource_proof.root_hex, fixture.heap_fixture.proof_root_hex);
    assert_eq!(lean_resource_proof.path.len(), fixture.heap_fixture.proof_path.len());
    assert_eq!(lean_resource_proof.path[0].direction, "Right");
    assert_eq!(
        lean_resource_proof.path[0].sibling_hash_hex,
        fixture.heap_fixture.proof_path[0].sibling_hash_hex
    );
    let lean_nullifier_proof = lean
        .heap_fixture
        .nullifier_proof
        .expect("Lean should return a nullifier proof");
    assert_eq!(
        lean_nullifier_proof.leaf_hash_hex,
        fixture.channel_fixture.nullifier_leaf_hex
    );
    assert_eq!(
        lean_nullifier_proof.root_hex,
        fixture.heap_fixture.nullifier_root_hex
    );
    assert!(lean_nullifier_proof.path.is_empty());
    assert_eq!(
        lean.heap_fixture.merkle_node_preimage_hex,
        fixture.heap_fixture.merkle_node_preimage_hex
    );
    assert_eq!(
        lean.heap_fixture.heap_commitment.resource_root_hex,
        fixture.heap_fixture.resource_root_hex
    );
    assert_eq!(
        lean.heap_fixture.heap_commitment.nullifier_root_hex,
        fixture.heap_fixture.nullifier_root_hex
    );
    assert_eq!(lean.heap_fixture.heap_commitment.counter, 3);
    assert_eq!(
        lean.heap_fixture.heap_commitment_preimage_hex,
        fixture.heap_fixture.commitment_preimage_hex
    );
    assert_eq!(
        lean.heap_fixture.commitment_hash_hex,
        fixture.heap_fixture.commitment_hash_hex
    );

    assert!(lean.replay.stable);
    assert!(lean.replay.active_ids_match_fixture);
    assert!(lean.replay.consumed_ids_match_fixture);
    assert_eq!(lean.replay.first_run.counter, 3);
    assert_eq!(lean.replay.second_run.counter, 3);
    assert_eq!(
        lean.replay
            .first_run
            .active_resource_ids
            .iter()
            .map(|rid| rid.digest_hex.clone())
            .collect::<Vec<_>>(),
        fixture.heap_fixture.active_resource_ids_hex
    );
    assert_eq!(
        lean.replay
            .first_run
            .consumed_resource_ids
            .iter()
            .map(|rid| rid.digest_hex.clone())
            .collect::<Vec<_>>(),
        fixture.heap_fixture.consumed_resource_ids_hex
    );
    assert_eq!(lean.replay.first_run, lean.replay.second_run);
}
