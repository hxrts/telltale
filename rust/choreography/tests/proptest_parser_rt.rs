#![cfg(not(target_arch = "wasm32"))]
#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use proptest::prelude::*;
use telltale_choreography::compiler::parser::parse_choreography_str;
use telltale_choreography::compiler::projection::project;
use telltale_choreography::format_choreography_str;

fn linear_protocol_source(bits: &[bool]) -> String {
    let mut lines = vec![
        "protocol Roundtrip =".to_string(),
        "  roles Alice, Bob".to_string(),
    ];

    for (idx, send_from_alice) in bits.iter().enumerate() {
        let (from, to) = if *send_from_alice {
            ("Alice", "Bob")
        } else {
            ("Bob", "Alice")
        };
        lines.push(format!("  {from} -> {to} : M{idx}"));
    }

    lines.join("\n")
}

proptest! {
    #[test]
    fn parse_format_parse_preserves_projection_semantics(bits in prop::collection::vec(any::<bool>(), 1..8)) {
        let input = linear_protocol_source(&bits);
        let first = parse_choreography_str(&input).expect("parse input choreography");
        let formatted = format_choreography_str(&input).expect("format choreography");
        let second = parse_choreography_str(&formatted).expect("parse formatted choreography");

        for role in &first.roles {
            let left = project(&first, role).expect("project original");
            let right = project(&second, role).expect("project formatted");
            prop_assert_eq!(left, right);
        }
    }
}
