#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

//! Example: Capability validation extension for choreographies
//!
//! This example demonstrates a role-specific extension that validates
//! capabilities before allowing operations.

use std::any::{Any, TypeId};
use telltale_choreography::effects::{ExtensionEffect, LabelId, Program, RoleId};
use telltale_choreography::RoleName;

// Define roles
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Role {
    Alice,
    Bob,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum CapabilityLabel {
    Default,
}

impl LabelId for CapabilityLabel {
    fn as_str(&self) -> &'static str {
        match self {
            CapabilityLabel::Default => "default",
        }
    }

    fn from_str(label: &str) -> Option<Self> {
        match label {
            "default" => Some(CapabilityLabel::Default),
            _ => None,
        }
    }
}

impl RoleId for Role {
    type Label = CapabilityLabel;

    fn role_name(&self) -> RoleName {
        match self {
            Role::Alice => RoleName::from_static("Alice"),
            Role::Bob => RoleName::from_static("Bob"),
        }
    }
}

// Define a capability validation extension
#[derive(Clone, Debug)]
pub struct ValidateCapability {
    pub capability: String,
    pub role: Role,
}

impl ExtensionEffect<Role> for ValidateCapability {
    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }

    fn type_name(&self) -> &'static str {
        "ValidateCapability"
    }

    fn participating_roles(&self) -> Vec<Role> {
        vec![self.role]
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }

    fn clone_box(&self) -> Box<dyn ExtensionEffect<Role>> {
        Box::new(self.clone())
    }
}

// Define a flow cost extension
#[derive(Clone, Debug)]
pub struct ChargeFlowCost {
    pub cost: u32,
    pub role: Role,
}

impl ExtensionEffect<Role> for ChargeFlowCost {
    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }

    fn type_name(&self) -> &'static str {
        "ChargeFlowCost"
    }

    fn participating_roles(&self) -> Vec<Role> {
        vec![self.role]
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }

    fn clone_box(&self) -> Box<dyn ExtensionEffect<Role>> {
        Box::new(self.clone())
    }
}

fn main() {
    println!("Capability & Flow Cost Extension Example");
    println!("=========================================\n");

    // Create a program with capability checks and flow costs
    let program: Program<Role, String> = Program::new()
        .ext(ValidateCapability {
            capability: "send_message".to_string(),
            role: Role::Alice,
        })
        .ext(ChargeFlowCost {
            cost: 100,
            role: Role::Alice,
        })
        .send(Role::Bob, "Hello from Alice".to_string())
        .ext(ValidateCapability {
            capability: "receive_message".to_string(),
            role: Role::Bob,
        })
        .recv::<String>(Role::Alice)
        .ext(ChargeFlowCost {
            cost: 50,
            role: Role::Bob,
        })
        .end();

    println!("Created program with {} effects", program.len());
    println!("\nProgram structure:");
    for (i, effect) in program.effects().iter().enumerate() {
        if let Some(validate) = effect.as_extension::<ValidateCapability>() {
            println!(
                "  [{}] ValidateCapability: {:?} needs '{}'",
                i, validate.role, validate.capability
            );
        } else if let Some(cost) = effect.as_extension::<ChargeFlowCost>() {
            println!(
                "  [{}] ChargeFlowCost: {:?} pays {} units",
                i, cost.role, cost.cost
            );
        } else {
            println!("  [{}] {:?}", i, effect);
        }
    }

    println!("\nExtension benefits:");
    println!("  - ValidateCapability: Ensures roles have permissions before operations");
    println!("  - ChargeFlowCost: Tracks resource usage for billing/budgeting");
    println!("\nThese extensions fail fast if handlers aren't registered (type-safe).");
}
