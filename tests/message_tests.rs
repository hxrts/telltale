//! Behavioral tests for the Message macro.
//!
//! Verifies that generated Message implementations work correctly:
//! - Struct form: identity upcast/downcast
//! - Enum form: correct variant wrapping/unwrapping
//! - Downcast failure returns Err(self)

#![allow(clippy::unwrap_used)]

use telltale::Message;

// ============================================================================
// Single Message Type Tests
// ============================================================================

#[derive(Debug, Message)]
enum SingleLabel {
    Hello(Hello),
}

#[derive(Debug, PartialEq)]
struct Hello(i32);

#[test]
fn test_message_single_upcast() {
    let hello = Hello(42);
    let label: SingleLabel = Message::upcast(hello);

    match label {
        SingleLabel::Hello(h) => assert_eq!(h.0, 42),
    }
}

#[test]
fn test_message_single_downcast() {
    let hello = Hello(42);
    let label: SingleLabel = Message::upcast(hello);

    // Downcast should succeed for matching variant
    let result: Result<Hello, SingleLabel> = label.downcast();
    assert!(result.is_ok());
    assert_eq!(result.unwrap().0, 42);
}

#[test]
fn test_message_roundtrip() {
    let original = Hello(123);
    let label: SingleLabel = Message::upcast(original);
    let recovered: Hello = label.downcast().unwrap();
    assert_eq!(recovered.0, 123);
}

// ============================================================================
// Multiple Message Type Tests
// ============================================================================

#[derive(Debug, Message)]
enum MultiLabel {
    Request(Request),
    Response(Response),
    Error(Error),
}

#[derive(Debug, PartialEq)]
struct Request {
    id: u32,
    data: String,
}

#[derive(Debug, PartialEq)]
struct Response {
    id: u32,
    result: i64,
}

#[derive(Debug, PartialEq)]
struct Error {
    code: u32,
    message: String,
}

#[test]
fn test_message_multi_upcast_request() {
    let req = Request {
        id: 1,
        data: "test".to_string(),
    };
    let label: MultiLabel = Message::upcast(req);

    match label {
        MultiLabel::Request(r) => {
            assert_eq!(r.id, 1);
            assert_eq!(r.data, "test");
        }
        _ => panic!("Expected Request variant"),
    }
}

#[test]
fn test_message_multi_upcast_response() {
    let resp = Response { id: 2, result: 42 };
    let label: MultiLabel = Message::upcast(resp);

    match label {
        MultiLabel::Response(r) => {
            assert_eq!(r.id, 2);
            assert_eq!(r.result, 42);
        }
        _ => panic!("Expected Response variant"),
    }
}

#[test]
fn test_message_multi_upcast_error() {
    let err = Error {
        code: 404,
        message: "Not found".to_string(),
    };
    let label: MultiLabel = Message::upcast(err);

    match label {
        MultiLabel::Error(e) => {
            assert_eq!(e.code, 404);
            assert_eq!(e.message, "Not found");
        }
        _ => panic!("Expected Error variant"),
    }
}

#[test]
fn test_message_downcast_wrong_variant() {
    // Create a Request and upcast it
    let req = Request {
        id: 1,
        data: "test".to_string(),
    };
    let label: MultiLabel = Message::upcast(req);

    // Try to downcast as Response (should fail)
    let result: Result<Response, MultiLabel> = label.downcast();
    assert!(result.is_err());

    // The error should contain the original label
    let label = result.unwrap_err();
    match label {
        MultiLabel::Request(r) => assert_eq!(r.id, 1),
        _ => panic!("Expected Request variant in error"),
    }
}

#[test]
fn test_message_downcast_preserves_on_failure() {
    let err = Error {
        code: 500,
        message: "Server error".to_string(),
    };
    let label: MultiLabel = Message::upcast(err);

    // Try to downcast as Request (should fail)
    let result: Result<Request, MultiLabel> = label.downcast();
    assert!(result.is_err());

    // Try to downcast as Response (should also fail)
    let label = result.unwrap_err();
    let result: Result<Response, MultiLabel> = label.downcast();
    assert!(result.is_err());

    // Finally downcast correctly
    let label = result.unwrap_err();
    let error: Error = label.downcast().unwrap();
    assert_eq!(error.code, 500);
}

// ============================================================================
// Multiple Independent Label Types
// ============================================================================

#[derive(Debug, Message)]
enum ControlLabel {
    Start(Start),
    Stop(Stop),
}

#[derive(Debug, PartialEq)]
struct Start;

#[derive(Debug, PartialEq)]
struct Stop;

#[derive(Debug, Message)]
enum DataLabel {
    Ping(Ping),
    Pong(Pong),
}

#[derive(Debug, PartialEq)]
struct Ping(u64);

#[derive(Debug, PartialEq)]
struct Pong(u64);

#[test]
fn test_multiple_label_types_independent() {
    // Control labels work independently
    let start: ControlLabel = Message::upcast(Start);
    let stop: ControlLabel = Message::upcast(Stop);

    match start {
        ControlLabel::Start(_) => {}
        ControlLabel::Stop(_) => panic!("Expected Start"),
    }

    match stop {
        ControlLabel::Stop(_) => {}
        ControlLabel::Start(_) => panic!("Expected Stop"),
    }

    // Data labels work independently
    let ping: DataLabel = Message::upcast(Ping(100));
    let pong: DataLabel = Message::upcast(Pong(200));

    match ping {
        DataLabel::Ping(p) => assert_eq!(p.0, 100),
        DataLabel::Pong(_) => panic!("Expected Ping"),
    }

    match pong {
        DataLabel::Pong(p) => assert_eq!(p.0, 200),
        DataLabel::Ping(_) => panic!("Expected Pong"),
    }
}

#[test]
fn test_label_type_separation() {
    // Start can upcast to ControlLabel
    let _control: ControlLabel = Message::upcast(Start);

    // Ping can upcast to DataLabel
    let _data: DataLabel = Message::upcast(Ping(0));

    // These are completely separate type hierarchies
}

// ============================================================================
// Unit Struct Message Tests
// ============================================================================

#[derive(Debug, Message)]
enum SimpleLabel {
    Ack(Ack),
    Nack(Nack),
}

#[derive(Debug, PartialEq)]
struct Ack;

#[derive(Debug, PartialEq)]
struct Nack;

#[test]
fn test_unit_struct_messages() {
    let ack: SimpleLabel = Message::upcast(Ack);
    let nack: SimpleLabel = Message::upcast(Nack);

    // Downcast should work for unit structs
    let _: Ack = ack.downcast().unwrap();
    let _: Nack = nack.downcast().unwrap();
}

#[test]
fn test_unit_struct_wrong_downcast() {
    let ack: SimpleLabel = Message::upcast(Ack);

    // Wrong downcast returns error with original
    let result: Result<Nack, SimpleLabel> = ack.downcast();
    assert!(result.is_err());
}

// ============================================================================
// Tuple Struct Message Tests
// ============================================================================

#[derive(Debug, Message)]
enum TupleLabel {
    Pair(Pair),
    Triple(Triple),
}

#[derive(Debug, PartialEq)]
struct Pair(i32, i32);

#[derive(Debug, PartialEq)]
struct Triple(i32, i32, i32);

#[test]
fn test_tuple_struct_messages() {
    let pair = Pair(1, 2);
    let triple = Triple(3, 4, 5);

    let pair_label: TupleLabel = Message::upcast(pair);
    let triple_label: TupleLabel = Message::upcast(triple);

    let recovered_pair: Pair = pair_label.downcast().unwrap();
    let recovered_triple: Triple = triple_label.downcast().unwrap();

    assert_eq!(recovered_pair, Pair(1, 2));
    assert_eq!(recovered_triple, Triple(3, 4, 5));
}

// ============================================================================
// Large Variant Count Tests
// ============================================================================

#[derive(Debug, Message)]
enum ManyVariants {
    V1(V1),
    V2(V2),
    V3(V3),
    V4(V4),
    V5(V5),
}

#[derive(Debug)]
struct V1;
#[derive(Debug)]
struct V2;
#[derive(Debug)]
struct V3;
#[derive(Debug)]
struct V4;
#[derive(Debug)]
struct V5;

#[test]
fn test_many_variants_each_works() {
    // Each variant should upcast and downcast correctly
    let l1: ManyVariants = Message::upcast(V1);
    let l2: ManyVariants = Message::upcast(V2);
    let l3: ManyVariants = Message::upcast(V3);
    let l4: ManyVariants = Message::upcast(V4);
    let l5: ManyVariants = Message::upcast(V5);

    // All should downcast correctly
    let _: V1 = l1.downcast().unwrap();
    let _: V2 = l2.downcast().unwrap();
    let _: V3 = l3.downcast().unwrap();
    let _: V4 = l4.downcast().unwrap();
    let _: V5 = l5.downcast().unwrap();
}

#[test]
fn test_many_variants_wrong_downcast() {
    let l1: ManyVariants = Message::upcast(V1);

    // Wrong downcasts should fail
    let result: Result<V2, ManyVariants> = l1.downcast();
    assert!(result.is_err());
}
