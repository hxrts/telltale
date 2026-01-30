//! Demonstration of correct choice construct syntax for external-demo
//!
//! This test shows the working syntax for choice constructs and provides
//! a corrected version of the user's original request.

use telltale_choreography::{extensions::ExtensionRegistry, parse_and_generate_with_extensions};

#[test]
fn demo_correct_choice_syntax() {
    println!("=== Choice Constructs ARE Supported! ===\n");

    // The user's original request (DOESN'T WORK):
    let original_request = r#"
protocol TestChoice = {
    roles Alice, Bob

    choice Alice {
        option1: Alice -> Bob : Message1
        option2: Alice -> Bob : Message2
    }
}
"#;

    // The CORRECTED syntax that WORKS:
    let corrected_syntax = r#"
protocol TestChoice = {
    roles Alice, Bob

    choice at Alice {
        option1 -> {
            Alice -> Bob : Message1
        }
        option2 -> {
            Alice -> Bob : Message2
        }
    }
}
"#;

    println!("❌ ORIGINAL SYNTAX (doesn't work):");
    println!("{}", original_request);

    println!("✅ CORRECTED SYNTAX (works!):");
    println!("{}", corrected_syntax);

    let registry = ExtensionRegistry::new();

    // Test original (should fail)
    match parse_and_generate_with_extensions(original_request, &registry) {
        Ok(_) => println!("Unexpected: Original syntax worked"),
        Err(_) => println!("✓ Confirmed: Original syntax fails as expected"),
    }

    // Test corrected (should work)
    match parse_and_generate_with_extensions(corrected_syntax, &registry) {
        Ok(_) => println!("✅ SUCCESS: Corrected syntax works perfectly!"),
        Err(e) => {
            println!("❌ ERROR: Corrected syntax failed: {}", e);
            panic!("This should work!");
        }
    }

    println!("\n=== Key Differences ===");
    println!("1. Use 'choice at Role' (or 'case choose Role of')");
    println!("2. Each branch uses 'label ->' with a block");
    println!("3. The parser generates session types automatically");
    println!("\n=== Result ===");
    println!("Choice constructs ARE supported by parse_and_generate_with_extensions!");
    println!("The advanced parser can handle choice constructs correctly.");
}
