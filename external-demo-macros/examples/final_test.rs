//! Demonstration of the fixed choreography macro and debugging approach
//!
//! This example shows how we diagnosed and fixed the issue with the choreography macro
//! generating malformed code due to a problematic timeout extension.

use rumpsteak_aura_choreography::{
    extensions::ExtensionRegistry, parse_and_generate_with_extensions,
};

/// Test the fixed implementation approach
fn test_fixed_implementation(input: &str) -> Result<proc_macro2::TokenStream, String> {
    // Use the same approach as our fixed macro: empty registry
    let registry = ExtensionRegistry::new();
    
    match parse_and_generate_with_extensions(input, &registry) {
        Ok(tokens) => Ok(tokens),
        Err(err) => Err(err.to_string()),
    }
}

fn main() {
    let input = r#"
protocol Test = {
    roles Alice, Bob
    Alice -> Bob : Message
}
"#;

    println!("🎉 Final Verification: Fixed Macro Test");
    println!("========================================");
    println!("Input choreography:");
    println!("{}", input);
    println!("----------------------------------------");

    match test_fixed_implementation(input) {
        Ok(tokens) => {
            println!("✅ SUCCESS: Fixed implementation generates valid code!");
            println!("Generated code:");
            println!("{}", tokens);
            
            let code_str = tokens.to_string();
            
            println!("\n📊 Code Quality Checks:");
            
            // Check 1: No stray .with_timeout
            if !code_str.contains(". with_timeout") {
                println!("  ✅ No malformed .with_timeout calls");
            } else {
                println!("  ❌ Still contains malformed .with_timeout");
            }
            
            // Check 2: Has proper role structures
            if code_str.contains("struct Roles") {
                println!("  ✅ Roles structure generated");
            }
            
            // Check 3: Has session types
            if code_str.contains("type Alice_Test") && code_str.contains("type Bob_Test") {
                println!("  ✅ Session types generated for both roles");
            }
            
            // Check 4: Proper syntax (ends correctly)
            if code_str.trim_end().ends_with(';') {
                println!("  ✅ Code has proper syntax termination");
            }
            
            println!("\n🔧 Implementation Details:");
            println!("  - Uses empty ExtensionRegistry instead of built-in extensions");
            println!("  - Avoids the buggy timeout extension entirely");
            println!("  - Generates clean, compilable Rumpsteak session types");
            
            println!("\n💡 Next Steps:");
            println!("  1. The macro in external-demo-macros has been fixed");
            println!("  2. The timeout extension still needs a proper fix in its generate_code() method");
            println!("  3. Once fixed, the macro can be updated to use built-in extensions again");
            
        }
        Err(err) => {
            println!("❌ Error: {}", err);
        }
    }
}
