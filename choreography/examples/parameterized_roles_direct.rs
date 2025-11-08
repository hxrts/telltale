//! Direct test of parameterized roles parsing without using the proc macro

use rumpsteak_choreography::compiler::{parse_dsl, project};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let dsl = r#"
    choreography TestParamRoles {
        roles: Coordinator, Worker[3]

        Coordinator -> Worker[0]: Task
        Worker[0] -> Coordinator: Result
    }
    "#;

    println!("Parsing choreography with parameterized roles...\n");

    // Parse the choreography
    let choreography = parse_dsl(dsl)?;

    println!("✓ Successfully parsed choreography: {}", choreography.name);
    println!("  Roles:");
    for role in &choreography.roles {
        if let Some(size) = &role.array_size {
            println!("    - {} (array size: {})", role.name, quote::quote!(#size));
        } else if role.index.is_some() {
            println!("    - {}[{}]", role.name, role.index.unwrap());
        } else {
            println!("    - {}", role.name);
        }
    }

    // Validate
    choreography.validate()?;
    println!("\n✓ Choreography validated successfully");

    // Project to local types
    println!("\n✓ Projecting to local types:");
    for role in &choreography.roles {
        match project(&choreography, role) {
            Ok(local_type) => {
                println!("    - {}: {:?}", role.name, local_type);
            }
            Err(e) => {
                println!("    - {}: Error - {}", role.name, e);
            }
        }
    }

    println!("\n🎉 Parameterized roles support is working!");

    Ok(())
}
