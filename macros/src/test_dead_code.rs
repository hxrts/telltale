#[cfg(test)]
mod test_dead_code_fix {
    use quote::quote;

    // This test ensures that the generated code doesn't trigger dead_code warnings
    #[test]
    fn test_no_dead_code_warnings() {
        let input = quote! {
            protocol TestProtocol {
                roles: Alice, Bob;
                Alice -> Bob: Hello;
                Bob -> Alice: World;
            }
        };

        // This should compile without warnings
        let result = crate::choreography::choreography(input);
        assert!(result.is_ok());
        
        // Verify the generated code includes #[allow(dead_code)]
        let generated = result.unwrap().to_string();
        
        // Check for the attribute with various formatting possibilities
        let has_allow_dead_code = generated.contains("# [allow (dead_code)]") || 
                                  generated.contains("#[allow(dead_code)]") ||
                                  generated.contains("#[allow ( dead_code )]");
        
        assert!(has_allow_dead_code, "Generated code should contain #[allow(dead_code)] attribute");
    }
}