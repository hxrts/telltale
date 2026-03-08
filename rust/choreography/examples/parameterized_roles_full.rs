#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

//! Complete test demonstrating parameterized roles functionality

use telltale_choreography::compiler::{parse_dsl, project};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Parameterized Roles Test Suite ===\n");

    // Test 1: Concrete array size with indexed access
    test_concrete_array()?;

    // Test 2: Multiple indexed workers
    test_multiple_workers()?;

    // Test 3: Symbolic parameters
    test_symbolic_params()?;

    println!("\nAll parameterized roles tests passed!");

    Ok(())
}

fn test_concrete_array() -> Result<(), Box<dyn std::error::Error>> {
    println!("Test 1: Concrete array size Worker[3]");

    let dsl = r"
    protocol ConcreteArray =
      roles Master, Worker[3]

      Master { shard = 0 }
        -> Worker[0] : Task of jobs.Task
      Worker[0]
        -> Master : Result of jobs.Result
    ";

    let choreography = parse_dsl(dsl)?;
    choreography.validate()?;

    for role in &choreography.roles {
        project(&choreography, role)?;
    }

    println!("  Parsed, validated, and projected successfully\n");
    Ok(())
}

fn test_multiple_workers() -> Result<(), Box<dyn std::error::Error>> {
    println!("Test 2: Multiple indexed workers");

    let dsl = r"
    protocol MultipleWorkers =
      roles Coordinator, Worker[5]

      par
        | Coordinator { shard = 0 }
            -> Worker[0] : Init of jobs.Init
        | Coordinator { shard = 1 }
            -> Worker[1] : Init of jobs.Init
        | Coordinator { shard = 2 }
            -> Worker[2] : Init of jobs.Init
    ";

    let choreography = parse_dsl(dsl)?;
    choreography.validate()?;

    for role in &choreography.roles {
        let local = project(&choreography, role)?;
        println!("  - {}: {:?}", role.name(), local);
    }

    println!("  Multiple worker indices working\n");
    Ok(())
}

fn test_symbolic_params() -> Result<(), Box<dyn std::error::Error>> {
    println!("Test 3: Symbolic parameters Worker[N]");

    let dsl = r"
    protocol SymbolicParam =
      roles Leader, Follower[N]

      Leader
        -> Follower[i] : Command of control.Command
      Follower[i]
        -> Leader : Ack
    ";

    let choreography = parse_dsl(dsl)?;
    choreography.validate()?;

    println!("  Symbolic parameters (N, i) parsed and validated\n");
    Ok(())
}
