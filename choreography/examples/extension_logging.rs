//! Example: Simple logging extension for choreographies
//!
//! This example demonstrates how to create and use a basic extension
//! that logs events during choreography execution.

use rumpsteak_aura_choreography::effects::{ExtensionEffect, Program};
use std::any::{Any, TypeId};

// Define a simple logging extension
#[derive(Clone, Debug)]
pub struct LogEvent {
    pub message: String,
    pub level: LogLevel,
}

#[derive(Clone, Debug)]
pub enum LogLevel {
    Info,
    Warn,
    Error,
}

impl ExtensionEffect for LogEvent {
    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }

    fn type_name(&self) -> &'static str {
        "LogEvent"
    }

    fn participating_role_ids(&self) -> Vec<Box<dyn Any>> {
        // Global extension - all roles should log
        vec![]
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }

    fn clone_box(&self) -> Box<dyn ExtensionEffect> {
        Box::new(self.clone())
    }
}

fn main() {
    println!("Logging Extension Example");
    println!("========================\n");

    // Create a program with logging extensions
    let program: Program<(), ()> = Program::new()
        .ext(LogEvent {
            message: "Starting choreography".to_string(),
            level: LogLevel::Info,
        })
        .ext(LogEvent {
            message: "Processing data".to_string(),
            level: LogLevel::Info,
        })
        .ext(LogEvent {
            message: "Choreography completed".to_string(),
            level: LogLevel::Info,
        })
        .end();

    println!("Created program with {} effects", program.len());
    println!("\nProgram structure:");
    for (i, effect) in program.effects.iter().enumerate() {
        if let Some(log_event) = effect.as_extension::<LogEvent>() {
            println!(
                "  [{}] LogEvent({:?}): {}",
                i, log_event.level, log_event.message
            );
        }
    }

    println!("\nTo execute this program, create a handler that implements ExtensibleHandler");
    println!("and registers a handler for LogEvent.");
}
