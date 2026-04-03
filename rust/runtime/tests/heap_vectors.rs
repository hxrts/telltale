use telltale_runtime::heap::{
    nullifier_leaf_hash, resource_leaf_hash, DefaultHeapHasher, Direction, Heap,
    HeapCommitment, MerkleTree, Resource, ResourceId,
};

fn to_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{:02x}", byte)).collect()
}

#[test]
fn public_heap_vectors_match_reference_values() {
    let resource = Resource::message("Alice", "Bob", "Hello", vec![1, 2, 3], 7);
    let resource_bytes = resource.canonical_bytes();
    let resource_id = ResourceId::<DefaultHeapHasher>::from_resource(&resource, 1);
    let resource_leaf = resource_leaf_hash::<DefaultHeapHasher>(&resource_id, &resource);
    let nullifier_leaf = nullifier_leaf_hash::<DefaultHeapHasher>(&resource_id);

    assert_eq!(
        to_hex(&resource_bytes),
        "545448500100415454485001003005000000416c69636503000000426f62545448500100100500000048656c6c6f030000000102030700000000000000"
    );
    assert_eq!(
        to_hex(resource_id.as_bytes()),
        "5a22a0e61e5faa3ea4c2bee86a92761eea62364727a77a4ed7c3a24c456afd8e"
    );
    assert_eq!(
        to_hex(resource_leaf.as_ref()),
        "7526f89408115ad41ff135f26fd3c0be0ca91c93589c2f17cea2d8115bda9cf3"
    );
    assert_eq!(
        to_hex(nullifier_leaf.as_ref()),
        "c8ff09f3959b1a2d654b86e29d8f12df277db70f05256f0e433bf26a6c98acb1"
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
        to_hex(proof.leaf_hash.as_ref()),
        "7526f89408115ad41ff135f26fd3c0be0ca91c93589c2f17cea2d8115bda9cf3"
    );
    assert_eq!(proof.path.len(), 1);
    assert_eq!(proof.path[0].direction, Direction::Right);
    assert_eq!(
        to_hex(proof.path[0].sibling_hash.as_ref()),
        "981652f6785b2e7147a3ba489d050f3924700e808b9a7b229470754507c5a13c"
    );
    assert_eq!(
        to_hex(commitment.resource_root.as_ref()),
        "1555554394a0a595200d7717fa5c4710ce608dab3ffd793ff3644eecb99df1fa"
    );
    assert_eq!(
        to_hex(commitment.nullifier_root.as_ref()),
        "c045d1ac8bad212b29fffbe54d774d1401242771c75275fc30b6136b007f52d6"
    );
    assert_eq!(
        to_hex(commitment.hash().as_ref()),
        "57d07742f7a22b083e88dcae71804c9f03a727df11fe9d1d4c0aa553a34dac0d"
    );
}
