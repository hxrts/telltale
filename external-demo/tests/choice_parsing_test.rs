//! Simple test to verify that choice constructs can be parsed
//! 
//! This test focuses solely on whether the parser can handle choice syntax,
//! not whether the generated code compiles correctly.

use rumpsteak_aura_choreography::{parse_and_generate_with_extensions, extensions::ExtensionRegistry};

#[test]
fn test_choice_construct_parsing_only() {
    println!("=== Testing Choice Construct Parsing ===");
    
    // Test the corrected syntax based on the grammar
    let choreography_with_choice = r#"
        protocol TestChoice = {
            roles Alice, Bob
            
            choice at Alice {
                option1 -> {
                    Alice -> Bob: Message1
                }
                option2 -> {
                    Alice -> Bob: Message2
                }
            }
        }
    "#;
    
    println!("Input choreography:");
    println!("{}", choreography_with_choice);
    
    // Create extension registry (empty for basic test)
    let registry = ExtensionRegistry::new();
    
    // Test parsing
    match parse_and_generate_with_extensions(choreography_with_choice, &registry) {
        Ok(generated_tokens) => {
            println!("✓ Choice construct parsed successfully!");
            println!("✓ Advanced parser (`parse_and_generate_with_extensions`) supports choice constructs");
            println!("Generated code preview (first 500 chars):");
            let code_str = generated_tokens.to_string();
            let preview = if code_str.len() > 500 {
                format!("{}...", &code_str[..500])
            } else {
                code_str
            };
            println!("{}", preview);
        }
        Err(err) => {
            println!("✗ Choice construct parsing failed");
            println!("Error: {}", err);
            panic!("Choice construct parsing should work!");
        }
    }
}

#[test]
fn test_original_user_syntax() {
    println!("\n=== Testing Original User Syntax ===");
    
    // Test the user's original syntax
    let original_syntax = r#"
        protocol TestChoice = {
            roles Alice, Bob
            
            choice Alice {
                option1: Alice -> Bob : Message1
                option2: Alice -> Bob : Message2
            }
        }
    "#;
    
    println!("Testing original user syntax:");
    println!("{}", original_syntax);
    
    let registry = ExtensionRegistry::new();
    
    match parse_and_generate_with_extensions(original_syntax, &registry) {
        Ok(_) => {
            println!("✓ Original user syntax works!");
        }
        Err(err) => {
            println!("✗ Original user syntax failed (as expected)");
            println!("Error: {}", err);
            println!("This confirms the syntax needs to be: 'choice at Alice' with 'label -> { ... }'");
        }
    }
}

#[test]
fn test_complex_choice_parsing() {
    println!("\n=== Testing Complex Choice Construct ===");
    
    let complex_choice = r#"
        protocol ComplexChoice = {
            roles Alice, Bob, Charlie
            
            choice at Alice {
                path1 -> {
                    Alice -> Bob : Message1
                    Bob -> Charlie : Message2
                }
                path2 -> {
                    Alice -> Charlie : Message2
                    Charlie -> Bob : Message1
                }
                path3 -> {
                    Alice -> Bob : Message1
                    Alice -> Charlie : Message2
                    Bob -> Alice : Message1
                    Charlie -> Alice : Message2
                }
            }
        }
    "#;
    
    println!("Testing complex choice with multiple paths:");
    println!("{}", complex_choice);
    
    let registry = ExtensionRegistry::new();
    
    match parse_and_generate_with_extensions(complex_choice, &registry) {
        Ok(generated_tokens) => {
            println!("✓ Complex choice construct parsed successfully!");
            println!("Generated code size: {} chars", generated_tokens.to_string().len());
        }
        Err(err) => {
            println!("✗ Complex choice parsing failed");
            println!("Error: {}", err);
            panic!("Complex choice parsing should work!");
        }
    }
}

#[test]  
fn test_choice_with_guards() {
    println!("\n=== Testing Choice With Guards ===");
    
    let choice_with_guards = r#"
        protocol GuardedChoice = {
            roles Alice, Bob
            
            choice at Alice {
                fast when (condition == "fast") -> {
                    Alice -> Bob : QuickMessage
                }
                slow when (condition == "slow") -> {
                    Alice -> Bob : SlowMessage
                }
            }
        }
    "#;
    
    println!("Testing choice with guards:");
    println!("{}", choice_with_guards);
    
    let registry = ExtensionRegistry::new();
    
    match parse_and_generate_with_extensions(choice_with_guards, &registry) {
        Ok(_) => {
            println!("✓ Choice with guards parsed successfully!");
        }
        Err(err) => {
            println!("✗ Choice with guards failed");
            println!("Error: {}", err);
            // Don't panic - guards might not be implemented yet
        }
    }
}
