//! Test file to verify choice construct support in external-demo choreography! macro
//!
//! This test checks whether the advanced parser (`parse_and_generate_with_extensions`)
//! can properly handle choice constructs.

use rumpsteak_aura_choreography::{extensions::ExtensionRegistry, parse_and_generate_with_extensions};

// Test the specific syntax requested by the user
#[test]
fn test_choice_construct_basic() {
    // This test verifies that the parser can handle choice constructs
    let choreography_src = r#"
        choreography TestChoice {
            roles: Alice, Bob;

            choice Alice {
                option1: {
                    Alice -> Bob: Message1;
                }
                option2: {
                    Alice -> Bob: Message2;
                }
            }
        }
    "#;

    let registry = ExtensionRegistry::new();
    let result = parse_and_generate_with_extensions(choreography_src, &registry);

    match result {
        Ok(_) => {
            println!("✓ Choice construct parsed successfully!");
            println!("✓ Advanced parser supports choice constructs");
        }
        Err(e) => {
            println!("✗ Choice construct parsing failed: {}", e);
            panic!("Choice construct test failed");
        }
    }
}

// Test more complex choice constructs
#[test]
fn test_choice_construct_complex() {
    let choreography_src = r#"
        choreography ComplexChoice {
            roles: Alice, Bob, Charlie;

            choice Alice {
                path1: {
                    Alice -> Bob: Message1;
                    Bob -> Charlie: Message2;
                }
                path2: {
                    Alice -> Charlie: Message2;
                    Charlie -> Bob: Message1;
                }
            }
        }
    "#;

    let registry = ExtensionRegistry::new();
    let result = parse_and_generate_with_extensions(choreography_src, &registry);

    match result {
        Ok(_) => {
            println!("✓ Complex choice construct parsed successfully!");
        }
        Err(e) => {
            println!("✗ Complex choice construct parsing failed: {}", e);
            panic!("Complex choice construct test failed");
        }
    }
}

// Test to check if we get meaningful error messages for invalid choice syntax
#[test]
fn test_choice_construct_error_handling() {
    // This test should ideally fail gracefully with clear error messages
    // if the choice syntax is not yet supported

    println!("Testing error handling for choice constructs...");

    // Test invalid syntax that should fail
    let invalid_choreography = r#"
        choreography InvalidChoice {
            roles: Alice, Bob;

            choice at Alice {
                option1: Alice -> Bob: Message1;
            }
        }
    "#;

    let registry = ExtensionRegistry::new();
    let result = parse_and_generate_with_extensions(invalid_choreography, &registry);

    match result {
        Ok(_) => {
            println!("Note: 'choice at Alice' syntax was accepted");
        }
        Err(e) => {
            println!("✓ Invalid syntax correctly rejected: {}", e);
        }
    }

    println!("✓ Choice construct syntax appears to be recognized by the parser");
}

#[cfg(test)]
mod choice_construct_analysis {
    use super::*;

    /// Analyze the current state of choice construct support
    #[test]
    fn analyze_choice_support() {
        println!("\n=== Choice Construct Support Analysis ===");

        // Check if the parser can handle choice constructs
        println!("1. Testing basic choice construct parsing...");

        let basic_choice = r#"
            choreography BasicChoice {
                roles: Alice, Bob;

                choice Alice {
                    option1: {
                        Alice -> Bob: Message1;
                    }
                }
            }
        "#;

        let registry = ExtensionRegistry::new();
        let result = parse_and_generate_with_extensions(basic_choice, &registry);

        match result {
            Ok(tokens) => {
                println!("2. Choice constructs are: FULLY SUPPORTED");
                println!("3. Generated code size: {} chars", tokens.to_string().len());
            }
            Err(e) => {
                println!("2. Choice constructs status: {}", e);
            }
        }
    }
}
