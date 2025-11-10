// Test DOT file parsing and generation round-trip
//
// Verifies that:
// 1. DOT files can be parsed into FSMs
// 2. FSMs can be generated back to DOT format
// 3. The round-trip preserves the FSM structure

#[cfg(feature = "parsing")]
use rumpsteak_aura_fsm::dot::{parse, Dot};

#[cfg(feature = "parsing")]
#[test]
fn test_simple_adder_client_parse() {
    let dot_content = r#"digraph C {
  0;
  1;
  2;
  3;
  
  
  0 -> 1 [label="S!lhs(x: i32)", ];
  1 -> 2 [label="S!rhs(y: i32)", ];
  2 -> 3 [label="S?res(r: i32)", ];
  
  }"#;

    let mut fsms = parse(dot_content);
    let fsm = fsms.next().expect("should have one FSM");

    match fsm {
        Ok(fsm) => {
            // Verify basic properties
            assert_eq!(fsm.role(), "C");
            let (states, transitions) = fsm.size();
            assert_eq!(states, 4, "should have 4 states");
            assert_eq!(transitions, 3, "should have 3 transitions");
        }
        Err(e) => panic!("Failed to parse DOT file: {e}"),
    }

    // Verify there are no more FSMs
    assert!(fsms.next().is_none(), "should only have one FSM");
}

#[cfg(feature = "parsing")]
#[test]
fn test_simple_adder_server_parse() {
    let dot_content = r#"digraph S {
  0;
  1;
  2;
  3;
  
  
  0 -> 1 [label="C?lhs(x: i32)", ];
  1 -> 2 [label="C?rhs(y: i32)", ];
  2 -> 3 [label="C!res(r: i32)", ];
  
  }"#;

    let mut fsms = parse(dot_content);
    let fsm = fsms.next().expect("should have one FSM");

    match fsm {
        Ok(fsm) => {
            // Verify basic properties
            assert_eq!(fsm.role(), "S");
            let (states, transitions) = fsm.size();
            assert_eq!(states, 4, "should have 4 states");
            assert_eq!(transitions, 3, "should have 3 transitions");
        }
        Err(e) => panic!("Failed to parse DOT file: {e}"),
    }

    // Verify there are no more FSMs
    assert!(fsms.next().is_none(), "should only have one FSM");
}

#[cfg(feature = "parsing")]
#[test]
fn test_dot_generation() {
    let dot_content = r#"digraph TestRole {
  0;
  1;
  
  
  0 -> 1 [label="Other!msg()", ];
  
  }"#;

    let mut fsms = parse(dot_content);
    let fsm = fsms
        .next()
        .expect("should have one FSM")
        .expect("should parse successfully");

    // Generate DOT from the FSM
    let generated = format!("{}", Dot::new(&fsm));

    // Parse the generated DOT
    let mut fsms2 = parse(&generated);
    let fsm2 = fsms2
        .next()
        .expect("should have one FSM")
        .expect("should parse successfully");

    // Verify they have the same structure
    assert_eq!(fsm.role(), fsm2.role());
    assert_eq!(fsm.size(), fsm2.size());
}

#[cfg(feature = "parsing")]
#[test]
fn test_multiple_fsms_in_one_file() {
    let dot_content = r#"digraph A {
  0;
  1;
  
  0 -> 1 [label="B!msg()", ];
}

digraph B {
  0;
  1;
  
  0 -> 1 [label="A?msg()", ];
}"#;

    let fsms: Vec<_> = parse(dot_content).collect();

    assert_eq!(fsms.len(), 2, "should have two FSMs");

    // Check first FSM
    let fsm_a = fsms[0]
        .as_ref()
        .expect("first FSM should parse successfully");
    assert_eq!(fsm_a.role(), "A");

    // Check second FSM
    let fsm_b = fsms[1]
        .as_ref()
        .expect("second FSM should parse successfully");
    assert_eq!(fsm_b.role(), "B");
}

#[cfg(feature = "parsing")]
#[test]
fn test_empty_fsm() {
    let dot_content = r"digraph Empty {
  0;
}";

    let mut fsms = parse(dot_content);
    let fsm = fsms
        .next()
        .expect("should have one FSM")
        .expect("should parse successfully");

    assert_eq!(fsm.role(), "Empty");
    let (states, transitions) = fsm.size();
    assert_eq!(states, 1, "should have 1 state");
    assert_eq!(transitions, 0, "should have 0 transitions");
}

#[cfg(not(feature = "parsing"))]
#[test]
fn parsing_feature_disabled() {
    println!("DOT parsing tests require the 'parsing' feature to be enabled");
}
