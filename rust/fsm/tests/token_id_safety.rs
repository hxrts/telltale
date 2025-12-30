//! Tests for Token -> TokenId unsafe transmute safety
//!
//! The parser uses unsafe code to convert Token enums to TokenId enums
//! by reading only the discriminant. These tests verify that:
//!
//! 1. Every Token variant maps to the correct TokenId variant
//! 2. The discriminant correspondence is maintained
//! 3. All variants are covered (exhaustive testing)
//!
//! These tests provide runtime verification of the safety invariants
//! documented in rust/fsm/src/dot/parse/mod.rs.

#![cfg(feature = "parsing")]

/// Test that FSM Token discriminants match TokenId
mod fsm_token_tests {
    use logos::Logos;
    use rumpsteak_aura_fsm::dot::parse::fsm::{Token, TokenId};

    /// Helper to get token ID via the unsafe transmute path
    fn token_id(token: &Token<'_>) -> TokenId {
        // This replicates the unsafe id() method for testing
        unsafe { *std::ptr::from_ref(token).cast() }
    }

    #[test]
    fn test_identifier_token_id() {
        // Create an Identifier token by lexing
        let mut lexer = Token::lexer("hello");
        let token = lexer.next().unwrap();
        assert!(
            matches!(token, Token::Identifier(_)),
            "expected Identifier, got {:?}",
            token
        );
        assert_eq!(
            token_id(&token),
            TokenId::Identifier,
            "Identifier discriminant mismatch"
        );
    }

    #[test]
    fn test_digraph_token_id() {
        let mut lexer = Token::lexer("digraph");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::Digraph));
        assert_eq!(token_id(&token), TokenId::Digraph);
    }

    #[test]
    fn test_label_token_id() {
        let mut lexer = Token::lexer("label");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::Label));
        assert_eq!(token_id(&token), TokenId::Label);
    }

    #[test]
    fn test_left_brace_token_id() {
        let mut lexer = Token::lexer("{");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::LeftBrace));
        assert_eq!(token_id(&token), TokenId::LeftBrace);
    }

    #[test]
    fn test_right_brace_token_id() {
        let mut lexer = Token::lexer("}");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::RightBrace));
        assert_eq!(token_id(&token), TokenId::RightBrace);
    }

    #[test]
    fn test_left_square_token_id() {
        let mut lexer = Token::lexer("[");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::LeftSquare));
        assert_eq!(token_id(&token), TokenId::LeftSquare);
    }

    #[test]
    fn test_right_square_token_id() {
        let mut lexer = Token::lexer("]");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::RightSquare));
        assert_eq!(token_id(&token), TokenId::RightSquare);
    }

    #[test]
    fn test_arrow_token_id() {
        let mut lexer = Token::lexer("->");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::Arrow));
        assert_eq!(token_id(&token), TokenId::Arrow);
    }

    #[test]
    fn test_equal_token_id() {
        let mut lexer = Token::lexer("=");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::Equal));
        assert_eq!(token_id(&token), TokenId::Equal);
    }

    #[test]
    fn test_comma_token_id() {
        let mut lexer = Token::lexer(",");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::Comma));
        assert_eq!(token_id(&token), TokenId::Comma);
    }

    #[test]
    fn test_semicolon_token_id() {
        let mut lexer = Token::lexer(";");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::Semicolon));
        assert_eq!(token_id(&token), TokenId::Semicolon);
    }

    #[test]
    fn test_eoi_token_id() {
        let token = Token::Eoi;
        assert_eq!(token_id(&token), TokenId::Eoi);
    }

    #[test]
    fn test_error_token_id() {
        let token = Token::Error;
        assert_eq!(token_id(&token), TokenId::Error);
    }

    /// Comprehensive test: parse a full DOT file and verify all token IDs
    #[test]
    fn test_all_tokens_in_context() {
        let source = r#"digraph Test { 0 -> 1 [label="msg"]; }"#;
        let mut lexer = Token::lexer(source);

        // Collect all tokens and verify each one
        let mut token_count = 0;
        while let Some(token) = lexer.next() {
            let id = token_id(&token);
            // Verify the ID matches what we expect from the token variant
            match &token {
                Token::Identifier(_) => assert_eq!(id, TokenId::Identifier),
                Token::Digraph => assert_eq!(id, TokenId::Digraph),
                Token::Label => assert_eq!(id, TokenId::Label),
                Token::LeftBrace => assert_eq!(id, TokenId::LeftBrace),
                Token::RightBrace => assert_eq!(id, TokenId::RightBrace),
                Token::LeftSquare => assert_eq!(id, TokenId::LeftSquare),
                Token::RightSquare => assert_eq!(id, TokenId::RightSquare),
                Token::Arrow => assert_eq!(id, TokenId::Arrow),
                Token::Equal => assert_eq!(id, TokenId::Equal),
                Token::Comma => assert_eq!(id, TokenId::Comma),
                Token::Semicolon => assert_eq!(id, TokenId::Semicolon),
                Token::Eoi => assert_eq!(id, TokenId::Eoi),
                Token::Error => assert_eq!(id, TokenId::Error),
            }
            token_count += 1;
        }
        assert!(token_count > 0, "should have parsed some tokens");
    }

    /// Verify the memory layout assumption: TokenId size equals discriminant size
    #[test]
    fn test_token_id_size_is_u8() {
        assert_eq!(
            std::mem::size_of::<TokenId>(),
            1,
            "TokenId should be exactly 1 byte (u8 discriminant)"
        );
    }

    /// Verify repr(u8) is applied correctly
    #[test]
    fn test_discriminant_is_u8() {
        // TokenId should be repr(u8), meaning each variant has a u8 discriminant
        let variants = [
            TokenId::Identifier,
            TokenId::Digraph,
            TokenId::Label,
            TokenId::LeftBrace,
            TokenId::RightBrace,
            TokenId::LeftSquare,
            TokenId::RightSquare,
            TokenId::Arrow,
            TokenId::Equal,
            TokenId::Comma,
            TokenId::Semicolon,
            TokenId::Eoi,
            TokenId::Error,
        ];

        // All discriminants should fit in u8 and be unique
        let mut seen = std::collections::HashSet::new();
        for variant in variants {
            let disc: u8 = unsafe { std::mem::transmute(variant) };
            assert!(
                seen.insert(disc),
                "duplicate discriminant {} for {:?}",
                disc,
                variant
            );
        }
    }
}

/// Test that Transition Token discriminants match TokenId
mod transition_token_tests {
    use logos::Logos;
    use rumpsteak_aura_fsm::dot::parse::transition::{Token, TokenId};

    /// Helper to get token ID via the unsafe transmute path
    fn token_id(token: &Token<'_>) -> TokenId {
        unsafe { *std::ptr::from_ref(token).cast() }
    }

    #[test]
    fn test_identifier_token_id() {
        let mut lexer = Token::lexer("hello");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::Identifier(_)));
        assert_eq!(token_id(&token), TokenId::Identifier);
    }

    #[test]
    fn test_boolean_true_token_id() {
        let mut lexer = Token::lexer("true");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::Boolean(true)));
        assert_eq!(token_id(&token), TokenId::Boolean);
    }

    #[test]
    fn test_boolean_false_token_id() {
        let mut lexer = Token::lexer("false");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::Boolean(false)));
        assert_eq!(token_id(&token), TokenId::Boolean);
    }

    #[test]
    fn test_number_token_id() {
        let mut lexer = Token::lexer("42");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::Number(42)));
        assert_eq!(token_id(&token), TokenId::Number);
    }

    #[test]
    fn test_left_round_token_id() {
        let mut lexer = Token::lexer("(");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::LeftRound));
        assert_eq!(token_id(&token), TokenId::LeftRound);
    }

    #[test]
    fn test_right_round_token_id() {
        let mut lexer = Token::lexer(")");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::RightRound));
        assert_eq!(token_id(&token), TokenId::RightRound);
    }

    #[test]
    fn test_left_brace_token_id() {
        let mut lexer = Token::lexer("{");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::LeftBrace));
        assert_eq!(token_id(&token), TokenId::LeftBrace);
    }

    #[test]
    fn test_right_brace_token_id() {
        let mut lexer = Token::lexer("}");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::RightBrace));
        assert_eq!(token_id(&token), TokenId::RightBrace);
    }

    #[test]
    fn test_left_square_token_id() {
        let mut lexer = Token::lexer("[");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::LeftSquare));
        assert_eq!(token_id(&token), TokenId::LeftSquare);
    }

    #[test]
    fn test_right_square_token_id() {
        let mut lexer = Token::lexer("]");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::RightSquare));
        assert_eq!(token_id(&token), TokenId::RightSquare);
    }

    #[test]
    fn test_question_token_id() {
        let mut lexer = Token::lexer("?");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::Question));
        assert_eq!(token_id(&token), TokenId::Question);
    }

    #[test]
    fn test_bang_token_id() {
        let mut lexer = Token::lexer("!");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::Bang));
        assert_eq!(token_id(&token), TokenId::Bang);
    }

    #[test]
    fn test_colon_token_id() {
        let mut lexer = Token::lexer(":");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::Colon));
        assert_eq!(token_id(&token), TokenId::Colon);
    }

    #[test]
    fn test_comma_token_id() {
        let mut lexer = Token::lexer(",");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::Comma));
        assert_eq!(token_id(&token), TokenId::Comma);
    }

    #[test]
    fn test_equal_token_id() {
        let mut lexer = Token::lexer("=");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::Equal));
        assert_eq!(token_id(&token), TokenId::Equal);
    }

    #[test]
    fn test_not_equal_token_id() {
        let mut lexer = Token::lexer("<>");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::NotEqual));
        assert_eq!(token_id(&token), TokenId::NotEqual);
    }

    #[test]
    fn test_less_equal_token_id() {
        let mut lexer = Token::lexer("<=");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::LessEqual));
        assert_eq!(token_id(&token), TokenId::LessEqual);
    }

    #[test]
    fn test_greater_equal_token_id() {
        let mut lexer = Token::lexer(">=");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::GreaterEqual));
        assert_eq!(token_id(&token), TokenId::GreaterEqual);
    }

    #[test]
    fn test_left_angle_token_id() {
        // Use context to ensure we get LeftAngle, not part of another token
        let mut lexer = Token::lexer("x < y");
        let _ = lexer.next(); // x
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::LeftAngle));
        assert_eq!(token_id(&token), TokenId::LeftAngle);
    }

    #[test]
    fn test_right_angle_token_id() {
        // Use context to ensure we get RightAngle, not part of another token
        let mut lexer = Token::lexer("x > y");
        let _ = lexer.next(); // x
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::RightAngle));
        assert_eq!(token_id(&token), TokenId::RightAngle);
    }

    #[test]
    fn test_plus_token_id() {
        let mut lexer = Token::lexer("+");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::Plus));
        assert_eq!(token_id(&token), TokenId::Plus);
    }

    #[test]
    fn test_minus_token_id() {
        let mut lexer = Token::lexer("-");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::Minus));
        assert_eq!(token_id(&token), TokenId::Minus);
    }

    #[test]
    fn test_star_token_id() {
        let mut lexer = Token::lexer("*");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::Star));
        assert_eq!(token_id(&token), TokenId::Star);
    }

    #[test]
    fn test_slash_token_id() {
        let mut lexer = Token::lexer("/");
        let token = lexer.next().unwrap();
        assert!(matches!(token, Token::Slash));
        assert_eq!(token_id(&token), TokenId::Slash);
    }

    #[test]
    fn test_eoi_token_id() {
        let token = Token::Eoi;
        assert_eq!(token_id(&token), TokenId::Eoi);
    }

    #[test]
    fn test_error_token_id() {
        let token = Token::Error;
        assert_eq!(token_id(&token), TokenId::Error);
    }

    /// Comprehensive test: parse a transition label and verify all token IDs
    #[test]
    fn test_all_tokens_in_context() {
        let source = r#"Server?request(x: i32, flag: bool)"#;
        let mut lexer = Token::lexer(source);

        let mut token_count = 0;
        while let Some(token) = lexer.next() {
            let id = token_id(&token);
            match &token {
                Token::Identifier(_) => assert_eq!(id, TokenId::Identifier),
                Token::Boolean(_) => assert_eq!(id, TokenId::Boolean),
                Token::Number(_) => assert_eq!(id, TokenId::Number),
                Token::LeftRound => assert_eq!(id, TokenId::LeftRound),
                Token::RightRound => assert_eq!(id, TokenId::RightRound),
                Token::LeftBrace => assert_eq!(id, TokenId::LeftBrace),
                Token::RightBrace => assert_eq!(id, TokenId::RightBrace),
                Token::LeftSquare => assert_eq!(id, TokenId::LeftSquare),
                Token::RightSquare => assert_eq!(id, TokenId::RightSquare),
                Token::LeftAngle => assert_eq!(id, TokenId::LeftAngle),
                Token::RightAngle => assert_eq!(id, TokenId::RightAngle),
                Token::Question => assert_eq!(id, TokenId::Question),
                Token::Bang => assert_eq!(id, TokenId::Bang),
                Token::Colon => assert_eq!(id, TokenId::Colon),
                Token::Comma => assert_eq!(id, TokenId::Comma),
                Token::Equal => assert_eq!(id, TokenId::Equal),
                Token::NotEqual => assert_eq!(id, TokenId::NotEqual),
                Token::LessEqual => assert_eq!(id, TokenId::LessEqual),
                Token::GreaterEqual => assert_eq!(id, TokenId::GreaterEqual),
                Token::Plus => assert_eq!(id, TokenId::Plus),
                Token::Minus => assert_eq!(id, TokenId::Minus),
                Token::Star => assert_eq!(id, TokenId::Star),
                Token::Slash => assert_eq!(id, TokenId::Slash),
                Token::Eoi => assert_eq!(id, TokenId::Eoi),
                Token::Error => assert_eq!(id, TokenId::Error),
            }
            token_count += 1;
        }
        assert!(token_count > 0, "should have parsed some tokens");
    }

    /// Verify the memory layout assumption: TokenId size equals discriminant size
    #[test]
    fn test_token_id_size_is_u8() {
        assert_eq!(
            std::mem::size_of::<TokenId>(),
            1,
            "TokenId should be exactly 1 byte (u8 discriminant)"
        );
    }

    /// Verify repr(u8) is applied correctly - all discriminants unique
    #[test]
    fn test_discriminant_is_u8() {
        let variants = [
            TokenId::Identifier,
            TokenId::Boolean,
            TokenId::Number,
            TokenId::LeftRound,
            TokenId::RightRound,
            TokenId::LeftBrace,
            TokenId::RightBrace,
            TokenId::LeftSquare,
            TokenId::RightSquare,
            TokenId::LeftAngle,
            TokenId::RightAngle,
            TokenId::Question,
            TokenId::Bang,
            TokenId::Colon,
            TokenId::Comma,
            TokenId::Equal,
            TokenId::NotEqual,
            TokenId::LessEqual,
            TokenId::GreaterEqual,
            TokenId::Plus,
            TokenId::Minus,
            TokenId::Star,
            TokenId::Slash,
            TokenId::Eoi,
            TokenId::Error,
        ];

        let mut seen = std::collections::HashSet::new();
        for variant in variants {
            let disc: u8 = unsafe { std::mem::transmute(variant) };
            assert!(
                seen.insert(disc),
                "duplicate discriminant {} for {:?}",
                disc,
                variant
            );
        }
    }
}

/// Tests for stress scenarios and edge cases
mod stress_tests {
    use rumpsteak_aura_fsm::dot::parse;

    /// Stress test: parse many DOT files to exercise the token ID path repeatedly
    #[test]
    fn test_many_parses_no_panic() {
        for i in 0..100 {
            let dot = format!(
                r#"digraph Test{i} {{
                    0;
                    1;
                    2;
                    0 -> 1 [label="Role{i}!msg{i}(x: i32)"];
                    1 -> 2 [label="Role{i}?response(y: bool)"];
                }}"#
            );

            let result = parse(&dot).next();
            assert!(
                result.is_some(),
                "iteration {} should produce a result",
                i
            );
            assert!(
                result.unwrap().is_ok(),
                "iteration {} should parse successfully",
                i
            );
        }
    }

    /// Test with unusual but valid identifiers
    #[test]
    fn test_unusual_identifiers() {
        let identifiers = [
            "_underscore",
            "CamelCase",
            "snake_case",
            "ALLCAPS",
            "mixedCase123",
            "a",               // single char
            "a1b2c3",          // alphanumeric
            "___",             // all underscores
            "role_with_many_underscores_in_name",
        ];

        for id in identifiers {
            // Use OtherRole to avoid self-communication error
            let dot = format!(
                r#"digraph {id} {{
                    0;
                    1;
                    0 -> 1 [label="OtherRole!msg()"];
                }}"#
            );

            let result = parse(&dot).next();
            assert!(
                result.is_some(),
                "identifier '{}' should produce a result",
                id
            );
            match result.unwrap() {
                Ok(fsm) => assert_eq!(fsm.role(), id),
                Err(e) => panic!("identifier '{}' failed to parse: {}", id, e),
            }
        }
    }
}
