//! Debug parameterized roles parsing

use rumpsteak_choreography::compiler::parse_dsl;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let dsl = r#"
    choreography TestParamRoles {
        roles: Coordinator, Worker[3]
        
        Coordinator -> Worker[0]: Task
        Worker[0] -> Coordinator: Result
    }
    "#;

    println!("Parsing choreography...\n");
    let choreography = parse_dsl(dsl)?;

    println!("Declared roles:");
    for role in &choreography.roles {
        println!(
            "  - Name: {}, Index: {:?}, Array_size: {:?}, Is_array: {}",
            role.name,
            role.index,
            role.array_size.as_ref().map(|t| t.to_string()),
            role.is_array()
        );
    }

    println!("\nProtocol: {:?}", choreography.protocol);

    // Check mentions_role for each declared role
    println!("\nChecking mentions_role:");
    for role in &choreography.roles {
        let mentioned = choreography.protocol.mentions_role(role);
        println!("  - {}: {}", role.name, mentioned);
    }

    Ok(())
}
